use hir::Semantics;
use ide_db::{
    EditionedFileId, FileRange, FxHashSet, RootDatabase,
};
use syntax::{
    AstNode, TextRange,
    ast::{self, HasArgList, HasName},
};

use crate::{Diagnostic, DiagnosticCode, Severity};


/// Result for a single (drop_impl, structural_field) pair.
#[derive(Clone, Debug)]
pub(crate) enum DropVerdict {
    DefinitelyMoves { site: TextRange, kind: MovePatternKind },
    PossiblyMoves,
    NoMove,
}

#[derive(Clone, Debug)]
pub(crate) enum MovePatternKind {
    DirectMove,
    MemReplace,
    MemSwap,
    MemTake,
    PtrRead,
    Assignment,
}

impl MovePatternKind {
    pub(crate) fn describe(&self) -> &'static str {
        match self {
            MovePatternKind::DirectMove => "moved by value",
            MovePatternKind::MemReplace => "replaced via `mem::replace`",
            MovePatternKind::MemSwap => "swapped via `mem::swap`",
            MovePatternKind::MemTake => "taken via `mem::take`",
            MovePatternKind::PtrRead => "read out via `ptr::read`",
            MovePatternKind::Assignment => "reassigned (overwriting the pinned value in-place)",
        }
    }
}

pub(crate) fn analyze_drop_body(
    sema: &Semantics<'_, RootDatabase>,
    drop_impl: &ast::Impl,
    structural_fields: &FxHashSet<String>,
) -> Vec<(String, DropVerdict)> {
    let Some(assoc_list) = drop_impl.assoc_item_list() else {
        return structural_fields
            .iter()
            .cloned()
            .map(|f| (f, DropVerdict::NoMove))
            .collect();
    };
    let Some(drop_fn) = assoc_list.assoc_items().find_map(|item| {
        let ast::AssocItem::Fn(f) = item else { return None };
        if f.name().map(|n| n.text().to_string()).as_deref() == Some("drop") {
            Some(f)
        } else {
            None
        }
    }) else {
        return structural_fields
            .iter()
            .cloned()
            .map(|f| (f, DropVerdict::NoMove))
            .collect();
    };

    let Some(body) = drop_fn.body() else {
        return structural_fields
            .iter()
            .cloned()
            .map(|f| (f, DropVerdict::NoMove))
            .collect();
    };

    structural_fields
        .iter()
        .map(|field_name| {
            let verdict = classify_drop_body_for_field(sema, &body, field_name);
            (field_name.clone(), verdict)
        })
        .collect()
}

fn classify_drop_body_for_field(
    sema: &Semantics<'_, RootDatabase>,
    body: &ast::BlockExpr,
    field_name: &str,
) -> DropVerdict {
    let mut any_reference = false;
    let mut possibly = false;

    for node in body.syntax().descendants() {
        if let Some(field_expr) = ast::FieldExpr::cast(node.clone()) {
            if !is_self_field_with_name(&field_expr, field_name) {
                continue;
            }
            any_reference = true;
            match classify_field_use_context(&field_expr) {
                FieldUseContext::Borrow => {
                }
                FieldUseContext::Assignment => {
                    return DropVerdict::DefinitelyMoves {
                        site: field_expr.syntax().text_range(),
                        kind: MovePatternKind::Assignment,
                    };
                }
                FieldUseContext::DirectMove => {
                    if !field_is_copy(sema, &field_expr) {
                        return DropVerdict::DefinitelyMoves {
                            site: field_expr.syntax().text_range(),
                            kind: MovePatternKind::DirectMove,
                        };
                    }
                }
                FieldUseContext::PassedAsArgument => {
                    if !field_is_copy(sema, &field_expr) {
                        return DropVerdict::DefinitelyMoves {
                            site: field_expr.syntax().text_range(),
                            kind: MovePatternKind::DirectMove,
                        };
                    }
                }
                FieldUseContext::MethodReceiver => {
                    possibly = true;
                }
                FieldUseContext::Other => {
                    possibly = true;
                }
            }
            continue;
        }

        if let Some(call) = ast::CallExpr::cast(node.clone()) {
            if let Some(kind) = is_known_move_call(sema, &call) {
                if call_targets_self_field(&call, field_name) {
                    return DropVerdict::DefinitelyMoves {
                        site: call.syntax().text_range(),
                        kind,
                    };
                }
            }
        }
    }

    if !any_reference {
        DropVerdict::NoMove
    } else if possibly {
        DropVerdict::PossiblyMoves
    } else {
        DropVerdict::NoMove
    }
}

// ---------------------------------------------------------------------------
// Field-expression context classification
// ---------------------------------------------------------------------------

enum FieldUseContext {
    /// Wrapped in `&` or `&mut` — a borrow.
    Borrow,
    /// LHS of an assignment.
    Assignment,
    /// Used by-value in an expression (e.g., `let x = self.field;`,
    /// `return self.field;`, `Some(self.field)`).
    DirectMove,
    /// Passed as a function-call argument by value.
    PassedAsArgument,
    /// Receiver of a method call (`self.field.foo()`).
    MethodReceiver,
    /// Anything else — match arms, pattern positions, etc.
    Other,
}

fn classify_field_use_context(field_expr: &ast::FieldExpr) -> FieldUseContext {
    let parent = match field_expr.syntax().parent() {
        Some(p) => p,
        None => return FieldUseContext::Other,
    };

    let parent = if ast::ParenExpr::can_cast(parent.kind()) {
        parent.parent().unwrap_or(parent)
    } else {
        parent
    };

    if let Some(ref_expr) = ast::RefExpr::cast(parent.clone()) {
        if ref_expr.expr().map(|e| e.syntax() == field_expr.syntax()).unwrap_or(false) {
            return FieldUseContext::Borrow;
        }
    }

    if let Some(bin) = ast::BinExpr::cast(parent.clone()) {
        if let Some(op) = bin.op_kind() {
            use ast::BinaryOp;
            if matches!(op, BinaryOp::Assignment { .. }) {
                if bin.lhs().map(|e| e.syntax() == field_expr.syntax()).unwrap_or(false) {
                    return FieldUseContext::Assignment;
                }
            }
        }
    }

    if let Some(method_call) = ast::MethodCallExpr::cast(parent.clone()) {
        if method_call
            .receiver()
            .map(|e| e.syntax() == field_expr.syntax())
            .unwrap_or(false)
        {
            return FieldUseContext::MethodReceiver;
        }
    }

    if ast::ArgList::can_cast(parent.kind()) {
        return FieldUseContext::PassedAsArgument;
    }

    if ast::LetStmt::can_cast(parent.kind())
        || ast::ReturnExpr::can_cast(parent.kind())
        || ast::TupleExpr::can_cast(parent.kind())
        || ast::RecordExprField::can_cast(parent.kind())
    {
        return FieldUseContext::DirectMove;
    }

    FieldUseContext::Other
}

fn is_self_field_with_name(field_expr: &ast::FieldExpr, field_name: &str) -> bool {
    let Some(name_ref) = field_expr.name_ref() else { return false };
    if name_ref.text() != field_name {
        return false;
    }
    let Some(receiver) = field_expr.expr() else { return false };
    let ast::Expr::PathExpr(p) = receiver else { return false };
    let Some(path) = p.path() else { return false };
    path.segment()
        .and_then(|s| s.name_ref())
        .map(|n| n.text() == "self")
        .unwrap_or(false)
}

fn field_is_copy(sema: &Semantics<'_, RootDatabase>, field_expr: &ast::FieldExpr) -> bool {
    let Some(ty) = sema.type_of_expr(&ast::Expr::FieldExpr(field_expr.clone())) else {
        return false;
    };
    let Some(copy) = find_marker_trait(sema, "Copy") else { return false };
    ty.adjusted().impls_trait(sema.db, copy, &[])
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

// ---------------------------------------------------------------------------
// Known move-through-&mut function calls
// ---------------------------------------------------------------------------

fn is_known_move_call(
    sema: &Semantics<'_, RootDatabase>,
    call: &ast::CallExpr,
) -> Option<MovePatternKind> {
    let path = match call.expr()? {
        ast::Expr::PathExpr(p) => p.path()?,
        _ => return None,
    };
    let resolution = sema.resolve_path(&path)?;
    let hir::PathResolution::Def(hir::ModuleDef::Function(func)) = resolution else {
        return None;
    };
    let name = func.name(sema.db);
    let module = func.module(sema.db);
    let module_name = module.name(sema.db).map(|n| n.as_str().to_owned());
    let krate_name = module
        .krate(sema.db)
        .display_name(sema.db)
        .map(|d| d.canonical_name().to_owned());
    if !matches!(krate_name.as_ref().map(|s| s.as_str()), Some("core") | Some("std")) {
        return None;
    }
    match (module_name.as_deref(), name.as_str()) {
        (Some("mem"), "replace") => Some(MovePatternKind::MemReplace),
        (Some("mem"), "swap") => Some(MovePatternKind::MemSwap),
        (Some("mem"), "take") => Some(MovePatternKind::MemTake),
        (Some("ptr"), "read") => Some(MovePatternKind::PtrRead),
        _ => None,
    }
}

fn call_targets_self_field(call: &ast::CallExpr, field_name: &str) -> bool {
    let Some(args) = call.arg_list() else { return false };
    args.args().any(|arg| arg_targets_self_field(&arg, field_name))
}

fn arg_targets_self_field(arg: &ast::Expr, field_name: &str) -> bool {
    let inner = match arg {
        ast::Expr::RefExpr(re) => match re.expr() {
            Some(e) => e,
            None => return false,
        },
        other => other.clone(),
    };
    let ast::Expr::FieldExpr(fe) = inner else { return false };
    is_self_field_with_name(&fe, field_name)
}

// ---------------------------------------------------------------------------
// Diagnostic emission helpers (called from pin_consistency.rs)
// ---------------------------------------------------------------------------

pub(crate) fn build_move_diagnostic(
    file_id: EditionedFileId,
    field_name: &str,
    site: TextRange,
    kind: &MovePatternKind,
    db: &RootDatabase,
) -> Diagnostic {
    let vfs_file_id = file_id.file_id(db);
    let message = format!(
        "structurally pinned field `{field_name}` is {} in `Drop::drop`. This \
         breaks the pin guarantee: pinned values must remain at the same \
         memory location until their destructor runs to completion. Either \
         leave this field untouched in `drop`, or migrate the type to \
         `pin-project` (which generates a sound `Drop`).",
        kind.describe()
    );
    Diagnostic::new(
        DiagnosticCode::Ra("pin-drop-moves-pinned-field", Severity::Warning),
        message,
        FileRange { file_id: vfs_file_id, range: site },
    )
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use crate::tests::check_diagnostics;

    /// `mem::replace` on a structurally pinned field — definitely a move.
    #[test]
    #[ignore = "requires minicore: map_unchecked_mut, mem, drop"]
    fn warns_on_mem_replace_in_drop() {
        check_diagnostics(
            r#"
//- minicore: pin, drop, mem
use core::pin::Pin;
use core::mem;

struct Foo { inner: String }

impl Foo {
    fn p(self: Pin<&mut Self>) -> Pin<&mut String> {
        unsafe { self.map_unchecked_mut(|s| &mut s.inner) }
    }
}

impl Drop for Foo {
    fn drop(&mut self) {
        let _ = mem::replace(&mut self.inner, String::new());
                //^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ warning: structurally pinned field `inner` is replaced via `mem::replace` in `Drop::drop`. This breaks the pin guarantee: pinned values must remain at the same memory location until their destructor runs to completion. Either leave this field untouched in `drop`, or migrate the type to `pin-project` (which generates a sound `Drop`).
    }
}
"#,
        );
    }

    /// Direct field assignment — also a move for pin purposes.
    #[test]
    #[ignore = "requires minicore: map_unchecked_mut, drop"]
    fn warns_on_assignment_in_drop() {
        check_diagnostics(
            r#"
//- minicore: pin, drop
use core::pin::Pin;

struct Foo { inner: String }

impl Foo {
    fn p(self: Pin<&mut Self>) -> Pin<&mut String> {
        unsafe { self.map_unchecked_mut(|s| &mut s.inner) }
    }
}

impl Drop for Foo {
    fn drop(&mut self) {
        self.inner = String::new();
        //^^^^^^^^ warning: structurally pinned field `inner` is reassigned (overwriting the pinned value in-place) in `Drop::drop`. This breaks the pin guarantee: pinned values must remain at the same memory location until their destructor runs to completion. Either leave this field untouched in `drop`, or migrate the type to `pin-project` (which generates a sound `Drop`).
    }
}
"#,
        );
    }

    /// Empty `drop` — no warning at all (Stage 2's hint should also be
    /// suppressed by the `NoMove` verdict).
    #[test]
    #[ignore = "requires minicore: map_unchecked_mut, drop"]
    fn no_warn_on_empty_drop() {
        check_diagnostics(
            r#"
//- minicore: pin, drop
use core::pin::Pin;

struct Foo { inner: String }

impl Foo {
    fn p(self: Pin<&mut Self>) -> Pin<&mut String> {
        unsafe { self.map_unchecked_mut(|s| &mut s.inner) }
    }
}

impl Drop for Foo {
    fn drop(&mut self) {}
}
"#,
        );
    }

    /// `drop` only borrows the field — no warning.
    #[test]
    #[ignore = "requires minicore: map_unchecked_mut, drop"]
    fn no_warn_on_borrow_only_drop() {
        check_diagnostics(
            r#"
//- minicore: pin, drop
use core::pin::Pin;

fn observe(_s: &str) {}

struct Foo { inner: String }

impl Foo {
    fn p(self: Pin<&mut Self>) -> Pin<&mut String> {
        unsafe { self.map_unchecked_mut(|s| &mut s.inner) }
    }
}

impl Drop for Foo {
    fn drop(&mut self) {
        observe(&self.inner);
    }
}
"#,
        );
    }

    /// Method call on the field — keeps it as a hint, not an escalated
    /// warning. (We can't tell if `clear` consumes the receiver without
    /// looking up its signature; conservative choice is "possibly moves".)
    #[test]
    #[ignore = "requires minicore: map_unchecked_mut, drop"]
    fn keeps_hint_for_unclassified_method_call() {
        check_diagnostics(
            r#"
//- minicore: pin, drop
use core::pin::Pin;

struct Foo { inner: String }

impl Foo {
    fn p(self: Pin<&mut Self>) -> Pin<&mut String> {
        unsafe { self.map_unchecked_mut(|s| &mut s.inner) }
    }
}

impl Drop for Foo {
//^^^^ weak: manual `Drop` impl on a type with structurally pinned field(s): `inner`. The body of `drop` receives `&mut self` and must not move out of these fields, or the pin guarantee is broken. Verify, or migrate to `pin-project` which generates a sound `Drop` for you.
    fn drop(&mut self) {
        self.inner.clear();
    }
}
"#,
        );
    }

    /// Different field is moved — no warning, because the *other* field is
    /// the structural one. (Tests that we correctly scope per-field.)
    #[test]
    #[ignore = "requires minicore: map_unchecked_mut, drop, mem"]
    fn no_warn_when_moved_field_is_not_structural() {
        check_diagnostics(
            r#"
//- minicore: pin, drop, mem
use core::pin::Pin;
use core::mem;

struct Foo { pinned_field: String, free_field: String }

impl Foo {
    fn p(self: Pin<&mut Self>) -> Pin<&mut String> {
        unsafe { self.map_unchecked_mut(|s| &mut s.pinned_field) }
    }
}

impl Drop for Foo {
    fn drop(&mut self) {
        // Moving the non-structural field is fine.
        let _ = mem::replace(&mut self.free_field, String::new());
    }
}
"#,
        );
    }
}
