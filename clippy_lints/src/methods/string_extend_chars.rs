use clippy_utils::diagnostics::span_lint_and_sugg;
use clippy_utils::source::snippet_with_applicability;
use clippy_utils::ty::is_type_diagnostic_item;
use if_chain::if_chain;
use rustc_errors::Applicability;
use rustc_hir as hir;
use rustc_lint::LateContext;
use rustc_middle::ty;
use rustc_span::symbol::sym;

use super::STRING_EXTEND_CHARS;

pub(super) fn check(cx: &LateContext<'_>, expr: &hir::Expr<'_>, recv: &hir::Expr<'_>, arg: &hir::Expr<'_>) {
    let obj_ty = cx.typeck_results().expr_ty(recv).peel_refs();
    if_chain! {
        if is_type_diagnostic_item(cx, obj_ty, sym::string_type);
        if let hir::ExprKind::MethodCall(name, _, [target], _) = arg.kind;
        if name.ident.as_str() == "chars";
        then {
            let self_ty = cx.typeck_results().expr_ty(target).peel_refs();
            let ref_str = if *self_ty.kind() == ty::Str {
                ""
            } else if is_type_diagnostic_item(cx, self_ty, sym::string_type) {
                "&"
            } else {
                return;
            };
            let mut applicability = Applicability::MachineApplicable;
            span_lint_and_sugg(
                cx,
                STRING_EXTEND_CHARS,
                expr.span,
                "calling `.extend(_.chars())`",
                "try this",
                format!(
                    "{}.push_str({}{})",
                    snippet_with_applicability(cx, recv.span, "..", &mut applicability),
                    ref_str,
                    snippet_with_applicability(cx, target.span, "..", &mut applicability)
                ),
                applicability,
            );
        }
    }
}
