use hir::{AsAssocItem, HasSource, HirDisplay, Semantics};
use ide_db::{
    EditionedFileId, FileRange, FxHashSet, RootDatabase,
};
use syntax::{
    AstNode, SyntaxNode,
    ast::{self, HasArgList, HasGenericParams, HasTypeBounds},
};

use crate::{Diagnostic, DiagnosticCode, DiagnosticsContext, Severity};

pub(crate) fn pin_unpina(
    ctx: &DiagnosticsContext<'_>,
    file_id: EditionedFileId,
) -> Vec<Diagnostic> {
    let sema = &ctx.sema;
    let parse = sema.parse(file_id);
    let root = parse.syntax();

    let mut diagnostics = Vec::new();

    check_unsound_unpin_impls(ctx, sema, file_id, root, &mut diagnostics);
    check_pin_new_unchecked_calls(ctx, sema, file_id, root, &mut diagnostics);

    diagnostics
}

// ---------------------------------------------------------------------------
// Check 1: cross-file Unpin soundness
// ---------------------------------------------------------------------------

fn check_unsound_unpin_impls(
    ctx: &DiagnosticsContext<'_>,
    sema: &Semantics<'_, RootDatabase>,
    file_id: EditionedFileId,
    root: &SyntaxNode,
    out: &mut Vec<Diagnostic>,
) {
    for impl_ast in root.descendants().filter_map(ast::Impl::cast) {
        let Some(trait_path) = impl_ast.trait_() else { continue };
        if !is_unpin_trait_path(sema, &trait_path) {
            continue;
        }

        let Some(self_ty_ast) = impl_ast.self_ty() else { continue };
        let Some(adt) = resolve_self_ty_to_adt(sema, &self_ty_ast) else { continue };

        let structural_fields = collect_structural_fields_cross_file(sema, adt);
        if structural_fields.is_empty() {
            continue;
        }

        let bounded_unpin_types = collect_unpin_bounds(sema, &impl_ast);

        let mut offenders: Vec<String> = Vec::new();
        let hir::Adt::Struct(s) = adt else {
            continue;
        };
        let Some(unpin_trait) = find_marker_trait(sema, "Unpin") else { continue };

        let fields = s.fields(sema.db);
        for field in fields {
            let field_name = field.name(sema.db).as_str().to_owned();
            if !structural_fields.contains(&field_name) {
                continue;
            }
            let field_ty = field.ty(sema.db);
            let field_type = field_ty.to_type(sema.db);

            if field_ty_is_bounded_unpin(sema, &field_type, &bounded_unpin_types, ctx.display_target) {
                continue;
            }

            if field_type.impls_trait(sema.db, unpin_trait, &[]) {
                continue;
            }

            let mention = if field_ty_mentions_phantom_pinned(sema, &field_type, ctx.display_target) {
                format!("`{field_name}` (contains `PhantomPinned`)")
            } else {
                format!("`{field_name}`")
            };
            offenders.push(mention);
        }

        if offenders.is_empty() {
            continue;
        }

        let header_range = impl_ast
            .impl_token()
            .map(|t| t.text_range())
            .unwrap_or_else(|| impl_ast.syntax().text_range());

        let fields_list = offenders.join(", ");
        let message = format!(
            "`impl Unpin` is unsound: structurally pinned field(s) {fields_list} \
             have type(s) that are not `Unpin`. Either remove this manual \
             `Unpin` impl (the auto-trait would correctly leave the type \
             `!Unpin`), or add `Unpin` bounds covering each pinned field's type."
        );

        out.push(Diagnostic::new(
            DiagnosticCode::Ra("pin-unsound-unpin-impl", Severity::Warning),
            message,
            FileRange { file_id: file_id.file_id(sema.db), range: header_range },
        ));
    }
}

fn collect_structural_fields_cross_file(
    sema: &Semantics<'_, RootDatabase>,
    adt: hir::Adt,
) -> FxHashSet<String> {
    let mut structural: FxHashSet<String> = FxHashSet::default();

    let ty = adt.ty(sema.db);
    let impls = hir::Impl::all_for_type(sema.db, ty);

    for imp in impls {
        if imp.trait_(sema.db).is_some() {
            continue;
        }
        for func in imp.items(sema.db).into_iter().filter_map(|i| match i {
            hir::AssocItem::Function(f) => Some(f),
            _ => None,
        }) {
            let Some(source) = func.source(sema.db) else { continue };
            let func_ast = source.value;
            if !receiver_is_pin_mut_self(sema, &func_ast) {
                continue;
            }
            let Some(body) = func_ast.body() else { continue };
            classify_into(sema, &body, &mut structural);
        }
    }

    structural
}

fn classify_into(
    sema: &Semantics<'_, RootDatabase>,
    body: &ast::BlockExpr,
    out: &mut FxHashSet<String>,
) {
    for node in body.syntax().descendants() {
        let Some(call) = ast::MethodCallExpr::cast(node) else { continue };
        let Some(name_ref) = call.name_ref() else { continue };
        if name_ref.text() != "map_unchecked_mut" {
            continue;
        }

        let Some(func) = sema.resolve_method_call(&call) else { continue };
        let Some(assoc) = func.as_assoc_item(sema.db) else { continue };
        let hir::AssocItemContainer::Impl(imp) = assoc.container(sema.db) else { continue };
        let Some(adt) = imp.self_ty(sema.db).as_adt() else { continue };
        if !is_pin_struct(sema, adt) {
            continue;
        }

        let Some(receiver) = call.receiver() else { continue };
        if !is_self_expr(&receiver) {
            continue;
        }

        let Some(closure_arg) = call.arg_list().and_then(|a| a.args().next()) else {
            continue;
        };
        let ast::Expr::ClosureExpr(closure) = closure_arg else { continue };
        let Some(body_expr) = closure.body() else { continue };
        if let Some(field) = field_name_from_ref_field_chain(&body_expr) {
            out.insert(field);
        }
    }
}

fn is_pin_struct(sema: &Semantics<'_, RootDatabase>, adt: hir::Adt) -> bool {
    let hir::Adt::Struct(s) = adt else { return false };
    if s.name(sema.db).as_str() != "Pin" {
        return false;
    }
    let module = s.module(sema.db);
    if module.name(sema.db).map(|n| n.as_str() == "pin").unwrap_or(false) {
        let krate_name = module
            .krate(sema.db)
            .display_name(sema.db)
            .map(|d| d.canonical_name().to_owned());
        return matches!(krate_name.as_ref().map(|s| s.as_str()), Some("core") | Some("std"));
    }
    false
}

fn is_unpin_trait_path(sema: &Semantics<'_, RootDatabase>, ty: &ast::Type) -> bool {
    let ast::Type::PathType(pt) = ty else { return false };
    let Some(path) = pt.path() else { return false };
    matches!(
        sema.resolve_path(&path),
        Some(hir::PathResolution::Def(hir::ModuleDef::Trait(t)))
            if t.name(sema.db).as_str() == "Unpin"
    )
}

fn resolve_self_ty_to_adt(
    sema: &Semantics<'_, RootDatabase>,
    ty: &ast::Type,
) -> Option<hir::Adt> {
    let ast::Type::PathType(pt) = ty else { return None };
    let path = pt.path()?;
    match sema.resolve_path(&path)? {
        hir::PathResolution::Def(hir::ModuleDef::Adt(adt)) => Some(adt),
        _ => None,
    }
}

fn receiver_is_pin_mut_self(sema: &Semantics<'_, RootDatabase>, func: &ast::Fn) -> bool {
    let Some(param_list) = func.param_list() else { return false };
    let Some(self_param) = param_list.self_param() else { return false };
    let Some(ty) = self_param.ty() else { return false };
    let ast::Type::PathType(path_ty) = ty else { return false };
    let Some(path) = path_ty.path() else { return false };
    match sema.resolve_path(&path) {
        Some(hir::PathResolution::Def(hir::ModuleDef::Adt(adt))) => is_pin_struct(sema, adt),
        _ => false,
    }
}

fn is_self_expr(expr: &ast::Expr) -> bool {
    let ast::Expr::PathExpr(p) = expr else { return false };
    p.path()
        .and_then(|p| p.segment())
        .and_then(|s| s.name_ref())
        .map(|n| n.text() == "self")
        .unwrap_or(false)
}

fn field_name_from_ref_field_chain(expr: &ast::Expr) -> Option<String> {
    let ast::Expr::RefExpr(re) = expr else { return None };
    if re.mut_token().is_none() {
        return None;
    }
    let inner = re.expr()?;
    let ast::Expr::FieldExpr(fe) = inner else { return None };
    fe.name_ref().map(|n| n.text().to_string())
}

fn find_marker_trait(sema: &Semantics<'_, RootDatabase>, name: &str) -> Option<hir::Trait> {
    for krate in hir::Crate::all(sema.db) {
        let krate_name = krate
            .display_name(sema.db)
            .map(|d| d.canonical_name().to_owned());
        if !matches!(krate_name.as_ref().map(|s| s.as_str()), Some("core") | Some("std")) {
            continue;
        }
        let root = krate.root_module(sema.db);
        let Some(marker) = root.children(sema.db).find(|m| {
            m.name(sema.db).map(|n| n.as_str() == "marker").unwrap_or(false)
        }) else {
            continue;
        };
        for def in marker.declarations(sema.db) {
            if let hir::ModuleDef::Trait(t) = def {
                if t.name(sema.db).as_str() == name {
                    return Some(t);
                }
            }
        }
    }
    None
}

fn collect_unpin_bounds(
    sema: &Semantics<'_, RootDatabase>,
    impl_ast: &ast::Impl,
) -> FxHashSet<String> {
    let mut bounded: FxHashSet<String> = FxHashSet::default();
    let Some(where_clause) = impl_ast.where_clause() else { return bounded };
    for pred in where_clause.predicates() {
        let Some(ty) = pred.ty() else { continue };
        let Some(bounds) = pred.type_bound_list() else { continue };
        let mentions_unpin = bounds.bounds().any(|b| {
            b.ty()
                .and_then(|t| match t {
                    ast::Type::PathType(p) => p.path(),
                    _ => None,
                })
                .and_then(|p| sema.resolve_path(&p))
                .map(|res| {
                    matches!(
                        res,
                        hir::PathResolution::Def(hir::ModuleDef::Trait(t))
                            if t.name(sema.db).as_str() == "Unpin"
                    )
                })
                .unwrap_or(false)
        });
        if mentions_unpin {
            bounded.insert(ty.syntax().text().to_string());
        }
    }
    bounded
}

fn field_ty_is_bounded_unpin(
    sema: &Semantics<'_, RootDatabase>,
    field_ty: &hir::Type<'_>,
    bounded: &FxHashSet<String>,
    display_target: hir::DisplayTarget,
) -> bool {
    if bounded.is_empty() {
        return false;
    }
    let rendered = field_ty.display(sema.db, display_target).to_string();
    bounded.contains(&rendered)
}

fn field_ty_mentions_phantom_pinned(
    sema: &Semantics<'_, RootDatabase>,
    field_ty: &hir::Type<'_>,
    display_target: hir::DisplayTarget,
) -> bool {
    let rendered = field_ty.display(sema.db, display_target).to_string();
    rendered.contains("PhantomPinned")
}

// ---------------------------------------------------------------------------
// Check 2: Pin::new_unchecked hint
// ---------------------------------------------------------------------------

fn check_pin_new_unchecked_calls(
    _ctx: &DiagnosticsContext<'_>,
    sema: &Semantics<'_, RootDatabase>,
    file_id: EditionedFileId,
    root: &SyntaxNode,
    out: &mut Vec<Diagnostic>,
) {
    for node in root.descendants() {
        let Some(call) = ast::CallExpr::cast(node) else { continue };
        let Some(path) = (match call.expr() {
            Some(ast::Expr::PathExpr(p)) => p.path(),
            _ => None,
        }) else {
            continue;
        };

        let Some(hir::PathResolution::Def(hir::ModuleDef::Function(func))) =
            sema.resolve_path(&path)
        else {
            continue;
        };
        if func.name(sema.db).as_str() != "new_unchecked" {
            continue;
        }
        let Some(assoc) = func.as_assoc_item(sema.db) else { continue };
        let hir::AssocItemContainer::Impl(imp) = assoc.container(sema.db) else { continue };
        let Some(adt) = imp.self_ty(sema.db).as_adt() else { continue };
        if !is_pin_struct(sema, adt) {
            continue;
        }

        if is_inside_unsafe_fn(call.syntax()) {
            continue;
        }
        if originates_from_known_pin_macro(sema, call.syntax()) {
            continue;
        }

        let range = call.syntax().text_range();
        let message =
            "`Pin::new_unchecked` is `unsafe`; the caller must guarantee that \
             the pointee will not be moved before its drop. If pinning a heap \
             value, prefer `Box::pin`. If pinning a stack value, prefer the \
             `pin!` macro from `core::pin` (Rust 1.68+) or the `pin-utils` \
             crate. Suppress this hint with `#[allow(...)]` if the safety \
             reasoning is documented at the call site.".to_owned();

        out.push(Diagnostic::new(
            DiagnosticCode::Ra("pin-new-unchecked-unjustified", Severity::WeakWarning),
            message,
            FileRange { file_id: file_id.file_id(sema.db), range },
        ));
    }
}

fn is_inside_unsafe_fn(node: &SyntaxNode) -> bool {
    let mut cur = node.parent();
    while let Some(parent) = cur {
        if let Some(func) = ast::Fn::cast(parent.clone()) {
            return func.unsafe_token().is_some();
        }
        cur = parent.parent();
    }
    false
}

fn originates_from_known_pin_macro(
    sema: &Semantics<'_, RootDatabase>,
    node: &SyntaxNode,
) -> bool {
    let Some(file_id) = sema.hir_file_for(node).macro_file() else {
        return false;
    };
    let mut current = Some(file_id);
    while let Some(mf) = current {
        let call = mf.call_node(sema.db);
        let krate_name = (|| {
            let module = sema.scope(&call.value)?.module();
            module
                .krate(sema.db)
                .display_name(sema.db)
                .map(|d| d.canonical_name().to_owned())
        })();
        if matches!(
            krate_name.as_ref().map(|s| s.as_str()),
            Some("pin_project")
                | Some("pin_project_lite")
                | Some("pin_utils")
                | Some("futures_util")
        ) {
            return true;
        }
        current = mf.parent(sema.db).macro_file();
    }
    false
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use crate::tests::check_diagnostics;

    /// A type with `PhantomPinned` and a manual `Unpin` impl — the most
    /// common manifestation of the bug.
    #[test]
    #[ignore = "requires minicore: map_unchecked_mut, unpin, PhantomPinned"]
    fn warns_on_unpin_impl_with_phantom_pinned() {
        check_diagnostics(
            r#"
//- minicore: pin, unpin
use core::pin::Pin;
use core::marker::{PhantomPinned, Unpin};

struct Foo {
    inner: i32,
    _p: PhantomPinned,
}

impl Foo {
    fn p(self: Pin<&mut Self>) -> Pin<&mut PhantomPinned> {
        unsafe { self.map_unchecked_mut(|s| &mut s._p) }
    }
}

impl Unpin for Foo {}
//^^^^ warning: `impl Unpin` is unsound: structurally pinned field(s) `_p` (contains `PhantomPinned`) have type(s) that are not `Unpin`. Either remove this manual `Unpin` impl (the auto-trait would correctly leave the type `!Unpin`), or add `Unpin` bounds covering each pinned field's type.
"#,
        );
    }

    /// `Pin::new_unchecked` on the stack — produces a hint.
    #[test]
    #[ignore = "requires minicore: new_unchecked"]
    fn hints_on_pin_new_unchecked() {
        check_diagnostics(
            r#"
//- minicore: pin
use core::pin::Pin;

fn make() {
    let mut x = 5_i32;
    let _p = unsafe { Pin::new_unchecked(&mut x) };
                     //^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ weak: `Pin::new_unchecked` is `unsafe`; the caller must guarantee that the pointee will not be moved before its drop. If pinning a heap value, prefer `Box::pin`. If pinning a stack value, prefer the `pin!` macro from `core::pin` (Rust 1.68+) or the `pin-utils` crate. Suppress this hint with `#[allow(...)]` if the safety reasoning is documented at the call site.
}
"#,
        );
    }

    /// Inside an `unsafe fn` — no hint, the function signature has already
    /// declared the unsafe contract.
    #[test]
    #[ignore = "requires minicore: new_unchecked"]
    fn no_hint_inside_unsafe_fn() {
        check_diagnostics(
            r#"
//- minicore: pin
use core::pin::Pin;

unsafe fn make() {
    let mut x = 5_i32;
    let _p = Pin::new_unchecked(&mut x);
}
"#,
        );
    }

    /// Cross-file `impl Unpin`: the type and its inherent impl live in
    /// `lib.rs`, the bad `Unpin` impl lives in another module. Diagnostic
    /// should fire on the `impl Unpin` site.
    #[test]
    #[ignore = "needs multi-module fixture; sketch in README"]
    fn warns_cross_file_unpin_impl() {}
}
