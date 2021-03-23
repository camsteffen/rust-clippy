use clippy_utils::diagnostics::span_lint_and_sugg;
use clippy_utils::single_segment_path;
use clippy_utils::source::snippet_with_applicability;
use if_chain::if_chain;
use rustc_errors::Applicability;
use rustc_hir as hir;
use rustc_lint::LateContext;
use rustc_lint::Lint;
use rustc_middle::ty;
use rustc_span::sym;

/// Wrapper fn for `CHARS_NEXT_CMP` and `CHARS_LAST_CMP` lints.
pub(super) fn check(
    cx: &LateContext<'_>,
    info: &crate::methods::BinaryExprInfo<'_>,
    chars_method: &str,
    lint: &'static Lint,
    suggest: &str,
) -> bool {
    if_chain! {
        if let hir::ExprKind::MethodCall(name, _, [recv], _) = info.chain.kind;
        if name.ident.as_str() == chars_method;
        if let hir::ExprKind::MethodCall(name, _, [recv], _) = recv.kind;
        if name.ident.as_str() == "chars";
        if let hir::ExprKind::Call(ref fun, [arg_char]) = info.other.kind;
        if let hir::ExprKind::Path(ref qpath) = fun.kind;
        if let Some(segment) = single_segment_path(qpath);
        if segment.ident.name == sym::Some;
        if *cx.typeck_results().expr_ty_adjusted(recv).peel_refs().kind() == ty::Str;
        then {
            let mut applicability = Applicability::MachineApplicable;
            span_lint_and_sugg(
                cx,
                lint,
                info.expr.span,
                &format!("you should use the `{}` method", suggest),
                "like this",
                format!("{}{}.{}({})",
                        if info.eq { "" } else { "!" },
                        snippet_with_applicability(cx, recv.span, "..", &mut applicability),
                        suggest,
                        snippet_with_applicability(cx, arg_char.span, "..", &mut applicability)),
                applicability,
            );

            return true;
        }
    }

    false
}
