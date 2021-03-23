use clippy_utils::diagnostics::span_lint_and_sugg;
use clippy_utils::source::snippet_with_applicability;
use if_chain::if_chain;
use rustc_ast::ast;
use rustc_errors::Applicability;
use rustc_hir as hir;
use rustc_lint::LateContext;
use rustc_lint::Lint;
use rustc_span::sym;

/// Wrapper fn for `CHARS_NEXT_CMP` and `CHARS_LAST_CMP` lints with `unwrap()`.
pub(super) fn check<'tcx>(
    cx: &LateContext<'tcx>,
    info: &crate::methods::BinaryExprInfo<'_>,
    chars_method: &str,
    lint: &'static Lint,
    suggest: &str,
) -> bool {
    if_chain! {
        if let hir::ExprKind::MethodCall(name, _, [recv], _) = info.chain.kind;
        if name.ident.name == sym::unwrap;
        if let hir::ExprKind::MethodCall(name, _, [recv], _) = recv.kind;
        if name.ident.name.as_str() == chars_method;
        if let hir::ExprKind::MethodCall(name, _, [recv], _) = recv.kind;
        if name.ident.name.as_str() == "chars";
        if let hir::ExprKind::Lit(ref lit) = info.other.kind;
        if let ast::LitKind::Char(c) = lit.node;
        then {
            let mut applicability = Applicability::MachineApplicable;
            span_lint_and_sugg(
                cx,
                lint,
                info.expr.span,
                &format!("you should use the `{}` method", suggest),
                "like this",
                format!("{}{}.{}('{}')",
                        if info.eq { "" } else { "!" },
                        snippet_with_applicability(cx, recv.span, "..", &mut applicability),
                        suggest,
                        c),
                applicability,
            );

            true
        } else {
            false
        }
    }
}
