use crate::methods::chars_cmp_with_unwrap;
use rustc_lint::LateContext;

use super::CHARS_LAST_CMP;

/// Checks for the `CHARS_LAST_CMP` lint with `unwrap()`.
pub(super) fn check<'tcx>(cx: &LateContext<'tcx>, info: &crate::methods::BinaryExprInfo<'_>) -> bool {
    if chars_cmp_with_unwrap::check(cx, info, "last", CHARS_LAST_CMP, "ends_with") {
        true
    } else {
        chars_cmp_with_unwrap::check(cx, info, "next_back", CHARS_LAST_CMP, "ends_with")
    }
}
