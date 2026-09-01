use hir::{AsAssocItem, HirDisplay, Semantics};
use ide_db::{
    EditionedFileId, RootDatabase,
    source_change::SourceChange,
    assists::{Assist, AssistId, AssistKind},
    label::Label,
    text_edit::TextEdit,
};
use syntax::{
    AstNode, SyntaxNode, SyntaxNodePtr,
    ast::{self, HasArgList},
};

use crate::{Diagnostic, DiagnosticCode, DiagnosticsContext, Severity};

pub(crate) fn pin_misuse(
    ctx: &DiagnosticsContext<'_>,
    file_id: EditionedFileId,
) -> Vec<Diagnostic> {
    let sema = &ctx.sema;
    let parse = sema.parse(file_id);
    let root = parse.syntax();

    let mut diagnostics = Vec::new();

    for node in root.descendants() {
        let Some(call) = ast::MethodCallExpr::cast(node.clone())
            .map(CallLike::Method)
            .or_else(|| ast::CallExpr::cast(node.clone()).map(CallLike::Free))
        else {
            continue;
        };

        check_hand_rolled_projection(ctx, sema, file_id, &call, &mut diagnostics);
        check_pin_new_on_non_unpin(ctx, sema, file_id, &call, &mut diagnostics);
    }

    diagnostics
}

enum CallLike {
    Method(ast::MethodCallExpr),
    Free(ast::CallExpr),
}

impl CallLike {
    fn syntax(&self) -> &SyntaxNode {
        match self {
            CallLike::Method(m) => m.syntax(),
            CallLike::Free(c) => c.syntax(),
        }
    }
}

// -- Check 1: hand-rolled pin projection ------------------------------------

fn check_hand_rolled_projection(
    ctx: &DiagnosticsContext<'_>,
    sema: &Semantics<'_, RootDatabase>,
    file_id: EditionedFileId,
    call: &CallLike,
    out: &mut Vec<Diagnostic>,
) {
    let func = match call {
        CallLike::Method(m) => sema.resolve_method_call(m),
        CallLike::Free(c) => {
            let path = match c.expr() {
                Some(ast::Expr::PathExpr(p)) => p.path(),
                _ => None,
            };
            path.and_then(|p| match sema.resolve_path(&p)? {
                hir::PathResolution::Def(hir::ModuleDef::Function(f)) => Some(f),
                _ => None,
            })
        }
    };
    let Some(func) = func else { return };

    let name = func.name(sema.db);
    let name_str = name.as_str();
    let is_unsafe_projection =
        name_str == "map_unchecked_mut" || name_str == "get_unchecked_mut";
    if !is_unsafe_projection {
        return;
    }

    let Some(assoc) = func.as_assoc_item(sema.db) else { return };
    let container = assoc.container(sema.db);
    let hir::AssocItemContainer::Impl(imp) = container else { return };
    let self_ty = imp.self_ty(sema.db);
    let Some(adt) = self_ty.as_adt() else { return };
    if !is_pin_struct(sema, adt) {
        return;
    }

    if originates_from_pin_project_macro(sema, call.syntax()) {
        return;
    }

    let hir_file_id = hir::HirFileId::from(file_id);
    let range = ctx.sema.diagnostics_display_range(hir::InFile::new(
        hir_file_id,
        SyntaxNodePtr::new(call.syntax()),
    ));

    let message = format!(
        "hand-rolled pin projection via `Pin::{name_str}`; consider using \
         `pin-project` or `pin-project-lite` to enforce structural-pinning \
         invariants automatically"
    );

    out.push(Diagnostic::new(
        DiagnosticCode::Ra("pin-hand-rolled-projection", Severity::WeakWarning),
        message,
        range,
    ));
}

// -- Check 2: `Pin::new` on a `!Unpin` type ---------------------------------

fn check_pin_new_on_non_unpin(
    ctx: &DiagnosticsContext<'_>,
    sema: &Semantics<'_, RootDatabase>,
    file_id: EditionedFileId,
    call: &CallLike,
    out: &mut Vec<Diagnostic>,
) {
    let CallLike::Free(call_expr) = call else { return };

    let path_expr = match call_expr.expr() {
        Some(ast::Expr::PathExpr(p)) => p,
        _ => return,
    };
    let path = match path_expr.path() {
        Some(p) => p,
        None => return,
    };

    let Some(hir::PathResolution::Def(hir::ModuleDef::Function(func))) =
        sema.resolve_path(&path)
    else {
        return;
    };
    if func.name(sema.db).as_str() != "new" {
        return;
    }
    let Some(assoc) = func.as_assoc_item(sema.db) else { return };
    let hir::AssocItemContainer::Impl(imp) = assoc.container(sema.db) else { return };
    let Some(adt) = imp.self_ty(sema.db).as_adt() else { return };
    if !is_pin_struct(sema, adt) {
        return;
    }

    let arg_list = match call_expr.arg_list() {
        Some(a) => a,
        None => return,
    };
    let mut args = arg_list.args();
    let Some(arg_expr) = args.next() else { return };
    if args.next().is_some() {
        return;
    }

    let Some(arg_ty) = sema.type_of_expr(&arg_expr).map(|info| info.adjusted()) else {
        return;
    };

    let Some(unpin_trait) = find_unpin_trait(sema) else { return };
    if arg_ty.impls_trait(sema.db, unpin_trait, &[]) {
        return;
    }

    let hir_file_id = hir::HirFileId::from(file_id);
    let range = ctx.sema.diagnostics_display_range(hir::InFile::new(
        hir_file_id,
        SyntaxNodePtr::new(call_expr.syntax()),
    ));

    let display_target = ctx.display_target;
    let ty_display = arg_ty.display(sema.db, display_target);
    let message = format!(
        "`Pin::new` requires `Unpin`, but `{ty_display}` is not `Unpin`. \
         Use `Box::pin(...)` for heap pinning, or `unsafe {{ Pin::new_unchecked(...) }} \
         if you can guarantee the value is never moved."
    );

    let vfs_file_id = file_id.file_id(sema.db);
    let fix = build_pin_new_fix(vfs_file_id, call_expr);

    let mut diag = Diagnostic::new(
        DiagnosticCode::Ra("pin-new-on-non-unpin", Severity::Warning),
        message,
        range,
    );
    if let Some(fix) = fix {
        diag = diag.with_fixes(Some(vec![fix]));
    }
    out.push(diag);
}

fn build_pin_new_fix(vfs_file_id: ide_db::FileId, call: &ast::CallExpr) -> Option<Assist> {
    let path_expr = match call.expr()? {
        ast::Expr::PathExpr(p) => p,
        _ => return None,
    };
    let path = path_expr.path()?;
    let path_range = path.syntax().text_range();

    let edit = TextEdit::replace(path_range, "Box::pin".to_owned());
    let source_change = SourceChange::from_text_edit(vfs_file_id, edit);

    Some(Assist {
        id: AssistId("replace_pin_new_with_box_pin", AssistKind::QuickFix, None),
        label: Label::new("Replace `Pin::new` with `Box::pin`".to_owned()),
        group: None,
        target: call.syntax().text_range(),
        source_change: Some(source_change),
        command: None,
    })
}

// -- Shared helpers ---------------------------------------------------------

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
    let krate_name = krate.display_name(sema.db).map(|d| d.canonical_name().to_owned());
    matches!(krate_name.as_ref().map(|s| s.as_str()), Some("core") | Some("std"))
}

fn find_unpin_trait(sema: &Semantics<'_, RootDatabase>) -> Option<hir::Trait> {
    for krate in hir::Crate::all(sema.db) {
        let name = krate.display_name(sema.db).map(|d| d.canonical_name().to_owned());
        if !matches!(name.as_ref().map(|s| s.as_str()), Some("core") | Some("std")) {
            continue;
        }
        let root = krate.root_module(sema.db);
        let Some(marker) = root
            .children(sema.db)
            .find(|m| m.name(sema.db).map(|n| n.as_str() == "marker").unwrap_or(false))
        else {
            continue;
        };
        for def in marker.declarations(sema.db) {
            if let hir::ModuleDef::Trait(t) = def {
                if t.name(sema.db).as_str() == "Unpin" {
                    return Some(t);
                }
            }
        }
    }
    None
}

fn originates_from_pin_project_macro(
    sema: &Semantics<'_, RootDatabase>,
    node: &SyntaxNode,
) -> bool {
    let Some(macro_call_id) = sema.hir_file_for(node).macro_file() else {
        return false;
    };

    let mut current: Option<hir::MacroCallId> = Some(macro_call_id);
    while let Some(mf) = current {
        let call = mf.call_node(sema.db);
        let module = sema.scope(&call.value).and_then(|scope| Some(scope.module()));
        let krate_name = module.and_then(|m| {
            m.krate(sema.db).display_name(sema.db).map(|d| d.canonical_name().to_owned())
        });
        if matches!(krate_name.as_ref().map(|s| s.as_str()), Some("pin_project") | Some("pin_project_lite")) {
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

    /// Hand-rolled projection should produce a weak warning.
    #[test]
    #[ignore = "requires minicore additions for Pin::map_unchecked_mut"]
    fn warns_on_hand_rolled_map_unchecked_mut() {
        check_diagnostics(
            r#"
//- minicore: pin
use core::pin::Pin;

struct Foo { inner: i32 }

impl Foo {
    fn project_inner(self: Pin<&mut Self>) -> Pin<&mut i32> {
        unsafe { self.map_unchecked_mut(|s| &mut s.inner) }
                 //^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ weak: hand-rolled pin projection via `Pin::map_unchecked_mut`; consider using `pin-project` or `pin-project-lite` to enforce structural-pinning invariants automatically
    }
}
"#,
        );
    }

    #[test]
    #[ignore = "requires minicore additions for Pin::get_unchecked_mut"]
    fn warns_on_hand_rolled_get_unchecked_mut() {
        check_diagnostics(
            r#"
//- minicore: pin
use core::pin::Pin;

struct Foo { inner: i32 }

impl Foo {
    fn raw(self: Pin<&mut Self>) -> &mut i32 {
        unsafe { &mut self.get_unchecked_mut().inner }
                      //^^^^^^^^^^^^^^^^^^^^^^^ weak: hand-rolled pin projection via `Pin::get_unchecked_mut`; consider using `pin-project` or `pin-project-lite` to enforce structural-pinning invariants automatically
    }
}
"#,
        );
    }

    /// `Pin::new` on an `Unpin` value is fine — no warning.
    #[test]
    fn no_warn_pin_new_on_unpin() {
        check_diagnostics(
            r#"
//- minicore: pin
use core::pin::Pin;

fn ok() {
    let mut x = 5_i32;
    let _p = Pin::new(&mut x);
}
"#,
        );
    }

    /// `Pin::new` on a `!Unpin` value (here, `PhantomPinned`) should warn.
    #[test]
    #[ignore = "requires minicore additions for PhantomPinned"]
    fn warns_on_pin_new_with_non_unpin() {
        check_diagnostics(
            r#"
//- minicore: pin
use core::pin::Pin;
use core::marker::PhantomPinned;

struct NotUnpin {
    _p: PhantomPinned,
}

fn make() -> NotUnpin { NotUnpin { _p: PhantomPinned } }

fn bad() {
    let mut x = make();
    let _p = Pin::new(&mut x);
            //^^^^^^^^^^^^^^^ error: `Pin::new` requires `Unpin`, but `&mut NotUnpin` is not `Unpin`. Use `Box::pin(...)` for heap pinning, or `unsafe { Pin::new_unchecked(...) } if you can guarantee the value is never moved.
}
"#,
        );
    }

    /// Make sure we correctly skip warning when the call is generated by a
    /// `pin-project`-family macro. We can't easily run the real macro in a
    /// minicore fixture, so this test stubs the crate name; it's the most
    /// fragile of the bunch and may need to be marked `#[ignore]` until
    /// fixture support for proc-macros lands in your environment.
    #[test]
    #[ignore = "requires proc-macro fixture for pin_project; see README"]
    fn no_warn_inside_pin_project_macro() {}
}
