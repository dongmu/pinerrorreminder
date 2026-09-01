use hir::{AsAssocItem, HasSource, InFile, Semantics};
use ide_db::{
    EditionedFileId, FxHashMap, FxHashSet, RootDatabase,
};
use syntax::{
    AstNode, SyntaxNode, TextRange,
    ast::{self, HasArgList, HasGenericArgs, HasGenericParams, HasName, HasTypeBounds},
};

use crate::{Diagnostic, DiagnosticCode, DiagnosticsContext, Severity};

pub(crate) fn pin_consistency(
    ctx: &DiagnosticsContext<'_>,
    file_id: EditionedFileId,
) -> Vec<Diagnostic> {
    let sema = &ctx.sema;
    let parse = sema.parse(file_id);
    let root = parse.syntax();

    let mut diagnostics = Vec::new();

    for impl_ast in root.descendants().filter_map(ast::Impl::cast) {
        if impl_ast.trait_().is_none() {
            analyze_inherent_impl(ctx, sema, file_id, &impl_ast, &mut diagnostics);
        }
    }

    analyze_drop_and_unpin(ctx, sema, file_id, root, &mut diagnostics);

    diagnostics
}

// ---------------------------------------------------------------------------
// Per-field classification
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct ProjectionSite {
    #[allow(dead_code)]
    field_name: String,
    method_name: String,
    range: TextRange,
}

#[derive(Default)]
struct FieldClassification {
    structural_sites: Vec<ProjectionSite>,
    non_structural_sites: Vec<ProjectionSite>,
}

fn analyze_inherent_impl(
    _ctx: &DiagnosticsContext<'_>,
    sema: &Semantics<'_, RootDatabase>,
    file_id: EditionedFileId,
    impl_ast: &ast::Impl,
    out: &mut Vec<Diagnostic>,
) {
    let Some(assoc_list) = impl_ast.assoc_item_list() else { return };

    let mut by_field: FxHashMap<String, FieldClassification> = FxHashMap::default();

    for item in assoc_list.assoc_items() {
        let ast::AssocItem::Fn(func) = item else { continue };
        if !receiver_is_pin_mut_self(sema, &func) {
            continue;
        }
        let method_name = func
            .name()
            .map(|n| n.text().to_string())
            .unwrap_or_else(|| "<unnamed>".to_owned());

        if let Some(body) = func.body() {
            classify_projections_in_body(
                sema,
                &body,
                &method_name,
                &mut by_field,
            );
        }
    }

    if by_field.is_empty() {
        return;
    }

    for (field_name, classification) in &by_field {
        if classification.structural_sites.is_empty()
            || classification.non_structural_sites.is_empty()
        {
            continue;
        }

        let example_structural = &classification.structural_sites[0];

        for ns in &classification.non_structural_sites {
            let message = format!(
                "field `{field_name}` is treated as non-structurally pinned here \
                 (in `{}`), but as structurally pinned elsewhere \
                 (e.g. in `{}`). This inconsistency is unsound: one site relies on \
                 the pin guarantee while the other has broken it.",
                ns.method_name, example_structural.method_name
            );

            let vfs_file_id = file_id.file_id(sema.db);
            out.push(Diagnostic::new(
                DiagnosticCode::Ra("pin-inconsistent-projection", Severity::Warning),
                message,
                ide_db::FileRange { file_id: vfs_file_id, range: ns.range },
            ));
        }
    }

}

fn receiver_is_pin_mut_self(sema: &Semantics<'_, RootDatabase>, func: &ast::Fn) -> bool {
    let Some(param_list) = func.param_list() else { return false };
    let Some(self_param) = param_list.self_param() else { return false };

    let Some(ty) = self_param.ty() else {
        return false;
    };

    let ast::Type::PathType(path_ty) = ty else { return false };
    let Some(path) = path_ty.path() else { return false };

    match sema.resolve_path(&path) {
        Some(hir::PathResolution::Def(hir::ModuleDef::Adt(hir::Adt::Struct(s)))) => {
            if !is_pin_struct(sema, hir::Adt::Struct(s)) {
                return false;
            }
        }
        _ => return false,
    }

    let Some(seg) = path.segment() else { return false };
    let Some(args) = seg.generic_arg_list() else { return false };
    args.generic_args().any(|g| {
        let ast::GenericArg::TypeArg(ta) = g else { return false };
        let Some(t) = ta.ty() else { return false };
        let ast::Type::RefType(rt) = t else { return false };
        rt.mut_token().is_some()
            && matches!(
                rt.ty(),
                Some(ast::Type::PathType(p))
                    if p.path()
                        .and_then(|p| p.segment())
                        .and_then(|s| s.name_ref())
                        .map(|n| n.text() == "Self")
                        .unwrap_or(false)
            )
    })
}

fn classify_projections_in_body(
    sema: &Semantics<'_, RootDatabase>,
    body: &ast::BlockExpr,
    method_name: &str,
    by_field: &mut FxHashMap<String, FieldClassification>,
) {
    for node in body.syntax().descendants() {
        let Some(call) = ast::MethodCallExpr::cast(node.clone()) else { continue };
        let Some(name_ref) = call.name_ref() else { continue };
        let method = name_ref.text();
        let is_map = method == "map_unchecked_mut";
        let is_get = method == "get_unchecked_mut";
        if !is_map && !is_get {
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

        if is_map {
            let Some(closure_arg) = call.arg_list().and_then(|a| a.args().next()) else {
                continue;
            };
            let ast::Expr::ClosureExpr(closure) = closure_arg else { continue };
            let Some(body_expr) = closure.body() else { continue };
            let Some(field) = field_name_from_ref_field_chain(&body_expr) else {
                continue;
            };
            record(by_field, field, method_name, call.syntax(), Bucket::Structural);
        } else {
            let Some(field_expr) =
                call.syntax().parent().and_then(ast::FieldExpr::cast)
            else {
                continue;
            };
            let Some(name_ref) = field_expr.name_ref() else { continue };
            let field = name_ref.text().to_string();
            record(by_field, field, method_name, field_expr.syntax(), Bucket::NonStructural);
        }
    }
}

#[derive(Clone, Copy)]
enum Bucket {
    Structural,
    NonStructural,
}

fn record(
    by_field: &mut FxHashMap<String, FieldClassification>,
    field_name: String,
    method_name: &str,
    node: &SyntaxNode,
    bucket: Bucket,
) {
    let site = ProjectionSite {
        field_name: field_name.clone(),
        method_name: method_name.to_owned(),
        range: node.text_range(),
    };
    let entry = by_field.entry(field_name).or_default();
    match bucket {
        Bucket::Structural => entry.structural_sites.push(site),
        Bucket::NonStructural => entry.non_structural_sites.push(site),
    }
}

fn is_self_expr(expr: &ast::Expr) -> bool {
    if let ast::Expr::PathExpr(p) = expr {
        if let Some(path) = p.path() {
            if let Some(seg) = path.segment() {
                if let Some(name_ref) = seg.name_ref() {
                    return name_ref.text() == "self";
                }
            }
        }
    }
    false
}

fn field_name_from_ref_field_chain(expr: &ast::Expr) -> Option<String> {
    let ast::Expr::RefExpr(re) = expr else { return None };
    if re.mut_token().is_none() {
        return None;
    }
    let mut inner = re.expr()?;
    loop {
        let ast::Expr::FieldExpr(fe) = inner else { return None };
        let parent_expr = fe.expr()?;
        match &parent_expr {
            ast::Expr::FieldExpr(_) => {
                inner = parent_expr;
            }
            ast::Expr::PathExpr(_) => {
                return fe.name_ref().map(|n| n.text().to_string());
            }
            _ => return fe.name_ref().map(|n| n.text().to_string()),
        }
    }
}

// ---------------------------------------------------------------------------
// Drop / Unpin secondary checks
// ---------------------------------------------------------------------------

fn analyze_drop_and_unpin(
    _ctx: &DiagnosticsContext<'_>,
    sema: &Semantics<'_, RootDatabase>,
    file_id: EditionedFileId,
    root: &SyntaxNode,
    out: &mut Vec<Diagnostic>,
) {
    let mut structural_fields_by_adt: FxHashMap<hir::Adt, FxHashSet<String>> =
        FxHashMap::default();

    for impl_ast in root.descendants().filter_map(ast::Impl::cast) {
        if impl_ast.trait_().is_some() {
            continue;
        }
        let Some(self_ty) = impl_ast.self_ty() else { continue };
        let Some(adt) = resolve_self_ty_to_adt(sema, &self_ty) else { continue };

        let Some(assoc_list) = impl_ast.assoc_item_list() else { continue };
        let mut by_field: FxHashMap<String, FieldClassification> = FxHashMap::default();
        for item in assoc_list.assoc_items() {
            let ast::AssocItem::Fn(func) = item else { continue };
            if !receiver_is_pin_mut_self(sema, &func) {
                continue;
            }
            let method_name = func
                .name()
                .map(|n| n.text().to_string())
                .unwrap_or_default();
            if let Some(body) = func.body() {
                classify_projections_in_body(sema, &body, &method_name, &mut by_field);
            }
        }
        for (field, classification) in by_field {
            if !classification.structural_sites.is_empty() {
                structural_fields_by_adt
                    .entry(adt)
                    .or_default()
                    .insert(field);
            }
        }
    }

    if structural_fields_by_adt.is_empty() {
        return;
    }

    for impl_ast in root.descendants().filter_map(ast::Impl::cast) {
        let Some(trait_path) = impl_ast.trait_() else { continue };
        let Some(self_ty) = impl_ast.self_ty() else { continue };
        let Some(adt) = resolve_self_ty_to_adt(sema, &self_ty) else { continue };
        let Some(structural_fields) = structural_fields_by_adt.get(&adt) else { continue };

        let trait_kind = match resolve_trait_path(sema, &trait_path) {
            Some(TraitKind::Drop) => TraitKind::Drop,
            Some(TraitKind::Unpin) => TraitKind::Unpin,
            _ => continue,
        };

        match trait_kind {
            TraitKind::Drop => {
                use crate::handlers::pin_drop_analysis::{
                    analyze_drop_body, build_move_diagnostic, DropVerdict,
                };

                let verdicts = analyze_drop_body(sema, &impl_ast, structural_fields);

                let mut emitted_strong = false;
                for (field, verdict) in &verdicts {
                    match verdict {
                        DropVerdict::DefinitelyMoves { site, kind } => {
                            out.push(build_move_diagnostic(
                                file_id, field, *site, kind, sema.db,
                            ));
                            emitted_strong = true;
                        }
                        DropVerdict::PossiblyMoves => {}
                        DropVerdict::NoMove => {}
                    }
                }

                let any_possibly = verdicts
                    .iter()
                    .any(|(_, v)| matches!(v, DropVerdict::PossiblyMoves));
                if any_possibly && !emitted_strong {
                    let header_range = impl_ast
                        .impl_token()
                        .map(|t| t.text_range())
                        .unwrap_or_else(|| impl_ast.syntax().text_range());
                    let fields_list = structural_fields
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>()
                        .join(", ");
                    let message = format!(
                        "manual `Drop` impl on a type with structurally pinned field(s): \
                         `{fields_list}`. The body of `drop` receives `&mut self` and \
                         must not move out of these fields, or the pin guarantee is \
                         broken. Verify, or migrate to `pin-project` which generates \
                         a sound `Drop` for you."
                    );
                    let vfs_file_id = file_id.file_id(sema.db);
                    out.push(Diagnostic::new(
                        DiagnosticCode::Ra("pin-drop-on-structural", Severity::WeakWarning),
                        message,
                        ide_db::FileRange { file_id: vfs_file_id, range: header_range },
                    ));
                }
            }
            TraitKind::Unpin => {
                let missing_bounds = unpin_impl_missing_bounds(
                    sema,
                    &impl_ast,
                    adt,
                    structural_fields,
                );
                if missing_bounds.is_empty() {
                    continue;
                }
                let fields_list = missing_bounds.join(", ");
                let header_range = impl_ast
                    .impl_token()
                    .map(|t| t.text_range())
                    .unwrap_or_else(|| impl_ast.syntax().text_range());
                let message = format!(
                    "`impl Unpin` on a type with structurally pinned field(s) \
                     missing the corresponding `Unpin` bound(s): `{fields_list}`. \
                     This is unsound: callers may move the outer type even though \
                     the projection assumes its pinned field stays pinned."
                );
                let vfs_file_id = file_id.file_id(sema.db);
                out.push(Diagnostic::new(
                    DiagnosticCode::Ra("pin-unpin-without-bounds", Severity::Warning),
                    message,
                    ide_db::FileRange { file_id: vfs_file_id, range: header_range },
                ));
            }
        }
    }
}

#[derive(Copy, Clone)]
enum TraitKind {
    Drop,
    Unpin,
}

fn resolve_trait_path(
    sema: &Semantics<'_, RootDatabase>,
    path: &ast::Type,
) -> Option<TraitKind> {
    let ast::Type::PathType(pt) = path else { return None };
    let path = pt.path()?;
    match sema.resolve_path(&path)? {
        hir::PathResolution::Def(hir::ModuleDef::Trait(t)) => {
            let name = t.name(sema.db);
            let krate = t.module(sema.db).krate(sema.db);
            let krate_name = krate
                .display_name(sema.db)
                .map(|d| d.canonical_name().to_owned());
            let is_corelike =
                matches!(krate_name.as_ref().map(|s| s.as_str()), Some("core") | Some("std") | Some("alloc"));
            if !is_corelike {
                return None;
            }
            match name.as_str() {
                "Drop" => Some(TraitKind::Drop),
                "Unpin" => Some(TraitKind::Unpin),
                _ => None,
            }
        }
        _ => None,
    }
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

fn unpin_impl_missing_bounds(
    sema: &Semantics<'_, RootDatabase>,
    impl_ast: &ast::Impl,
    adt: hir::Adt,
    structural_fields: &FxHashSet<String>,
) -> Vec<String> {
    let mut bounded_types: FxHashSet<String> = FxHashSet::default();

    if let Some(where_clause) = impl_ast.where_clause() {
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
                bounded_types.insert(ty.syntax().text().to_string());
            }
        }
    }

    let mut missing = Vec::new();
    let hir::Adt::Struct(s) = adt else { return missing };
    let source = match s.source(sema.db) {
        Some(src) => src,
        None => return missing,
    };
    let InFile { value: struct_def, .. } = source;

    let Some(field_list) = struct_def.field_list() else { return missing };
    let ast::FieldList::RecordFieldList(fields) = field_list else {
        return missing;
    };

    for field in fields.fields() {
        let Some(name) = field.name() else { continue };
        if !structural_fields.contains(name.text().as_ref()) {
            continue;
        }
        let Some(ty) = field.ty() else { continue };
        let ty_text = ty.syntax().text().to_string();
        if !is_simple_generic_param(sema, &ty) {
            continue;
        }
        if !bounded_types.contains(&ty_text) {
            missing.push(format!("{}: {}", name.text(), ty_text));
        }
    }
    missing
}

fn is_simple_generic_param(sema: &Semantics<'_, RootDatabase>, ty: &ast::Type) -> bool {
    let ast::Type::PathType(pt) = ty else { return false };
    let Some(path) = pt.path() else { return false };
    if path.qualifier().is_some() {
        return false;
    }
    let Some(seg) = path.segment() else { return false };
    if seg.generic_arg_list().is_some() {
        return false;
    }
    matches!(
        sema.resolve_path(&path),
        Some(hir::PathResolution::TypeParam(_))
    )
}


fn is_pin_struct(sema: &Semantics<'_, RootDatabase>, adt: hir::Adt) -> bool {
    let hir::Adt::Struct(s) = adt else { return false };
    if s.name(sema.db).as_str() != "Pin" {
        return false;
    }
    let module = s.module(sema.db);
    let parent_name = module.name(sema.db);
    if parent_name.as_ref().map(|n| n.as_str()) != Some("pin") {
        return false;
    }
    let krate = module.krate(sema.db);
    let krate_name = krate
        .display_name(sema.db)
        .map(|d| d.canonical_name().to_owned());
    matches!(krate_name.as_ref().map(|s| s.as_str()), Some("core") | Some("std"))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use crate::tests::check_diagnostics;

    /// Two methods, same field, opposite treatment — the smoking gun.
    #[test]
    #[ignore = "requires minicore: map_unchecked_mut, get_unchecked_mut"]
    fn detects_inconsistent_field_projection() {
        check_diagnostics(
            r#"
//- minicore: pin
use core::pin::Pin;

struct Foo { inner: i32 }

impl Foo {
    fn pinned(self: Pin<&mut Self>) -> Pin<&mut i32> {
        unsafe { self.map_unchecked_mut(|s| &mut s.inner) }
    }
    fn unpinned(self: Pin<&mut Self>) -> &mut i32 {
        unsafe { &mut self.get_unchecked_mut().inner }
                      //^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ warning: field `inner` is treated as non-structurally pinned here (in `unpinned`), but as structurally pinned elsewhere (e.g. in `pinned`). This inconsistency is unsound: one site relies on the pin guarantee while the other has broken it.
    }
}
"#,
        );
    }

    /// Same field, both methods structural — no diagnostic.
    #[test]
    #[ignore = "requires minicore: map_unchecked_mut"]
    fn no_warn_when_consistently_structural() {
        check_diagnostics(
            r#"
//- minicore: pin
use core::pin::Pin;

struct Foo { inner: i32, other: i32 }

impl Foo {
    fn p1(self: Pin<&mut Self>) -> Pin<&mut i32> {
        unsafe { self.map_unchecked_mut(|s| &mut s.inner) }
    }
    fn p2(self: Pin<&mut Self>) -> Pin<&mut i32> {
        unsafe { self.map_unchecked_mut(|s| &mut s.inner) }
    }
}
"#,
        );
    }

    /// Two different fields, one each of structural and non-structural —
    /// this is FINE because they're different fields.
    #[test]
    #[ignore = "requires minicore: map_unchecked_mut, get_unchecked_mut"]
    fn no_warn_when_different_fields() {
        check_diagnostics(
            r#"
//- minicore: pin
use core::pin::Pin;

struct Foo { pinned_field: i32, unpinned_field: i32 }

impl Foo {
    fn p(self: Pin<&mut Self>) -> Pin<&mut i32> {
        unsafe { self.map_unchecked_mut(|s| &mut s.pinned_field) }
    }
    fn u(self: Pin<&mut Self>) -> &mut i32 {
        unsafe { &mut self.get_unchecked_mut().unpinned_field }
    }
}
"#,
        );
    }

    /// Manual `Drop` impl alongside structural projection → weak warning.
    #[test]
    #[ignore = "requires minicore: map_unchecked_mut, Drop"]
    fn warns_on_manual_drop_with_structural_field() {
        check_diagnostics(
            r#"
//- minicore: pin, drop
use core::pin::Pin;

struct Foo { inner: i32 }

impl Foo {
    fn p(self: Pin<&mut Self>) -> Pin<&mut i32> {
        unsafe { self.map_unchecked_mut(|s| &mut s.inner) }
    }
}

impl Drop for Foo {
//^^^^ weak: manual `Drop` impl on a type with structurally pinned field(s): `inner`. The body of `drop` receives `&mut self` and must not move out of these fields, or the pin guarantee is broken. Verify, or migrate to `pin-project` which generates a sound `Drop` for you.
    fn drop(&mut self) {}
}
"#,
        );
    }

    /// `impl Unpin` on a generic type with a structurally pinned generic
    /// field, but no `T: Unpin` bound → warn.
    #[test]
    #[ignore = "requires minicore: map_unchecked_mut, Unpin"]
    fn warns_on_unpin_impl_missing_bound() {
        check_diagnostics(
            r#"
//- minicore: pin, unpin
use core::pin::Pin;
use core::marker::Unpin;

struct Foo<T> { inner: T }

impl<T> Foo<T> {
    fn p(self: Pin<&mut Self>) -> Pin<&mut T> {
        unsafe { self.map_unchecked_mut(|s| &mut s.inner) }
    }
}

impl<T> Unpin for Foo<T> {}
//^^^^ warning: `impl Unpin` on a type with structurally pinned field(s) missing the corresponding `Unpin` bound(s): `inner: T`. This is unsound: callers may move the outer type even though the projection assumes its pinned field stays pinned.
"#,
        );
    }

    /// `impl Unpin` *with* the bound — no warning.
    #[test]
    #[ignore = "requires minicore: map_unchecked_mut, Unpin"]
    fn no_warn_unpin_impl_with_bound() {
        check_diagnostics(
            r#"
//- minicore: pin, unpin
use core::pin::Pin;
use core::marker::Unpin;

struct Foo<T> { inner: T }

impl<T> Foo<T> {
    fn p(self: Pin<&mut Self>) -> Pin<&mut T> {
        unsafe { self.map_unchecked_mut(|s| &mut s.inner) }
    }
}

impl<T> Unpin for Foo<T> where T: Unpin {}
"#,
        );
    }

    /// Sanity: a method with `&mut self` (not Pin) shouldn't trip the analysis.
    #[test]
    #[ignore = "requires minicore: map_unchecked_mut"]
    fn ignores_non_pin_methods() {
        check_diagnostics(
            r#"
//- minicore: pin
use core::pin::Pin;

struct Foo { inner: i32 }

impl Foo {
    fn p(self: Pin<&mut Self>) -> Pin<&mut i32> {
        unsafe { self.map_unchecked_mut(|s| &mut s.inner) }
    }
    fn ordinary(&mut self) -> &mut i32 {
        &mut self.inner
    }
}
"#,
        );
    }
}
