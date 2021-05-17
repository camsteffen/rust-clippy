use crate::consts::{constant_context, constant_simple};
use crate::differing_macro_contexts;
use crate::source::snippet_opt;
use rustc_ast::ast::InlineAsmTemplatePiece;
use rustc_ast::Label;
use rustc_data_structures::fx::FxHasher;
use rustc_hir::def::Res;
use rustc_hir::HirIdMap;
use rustc_hir::{
    Arm, BareFnTy, BinOpKind, Block, BodyId, Destination, Expr, ExprField, ExprKind, FnRetTy, GenericArg, GenericArgs,
    Guard, HirId, InlineAsm, InlineAsmOperand, Lifetime, LifetimeName, MutTy, ParamName, Pat, PatField, PatKind, Path,
    PathSegment, QPath, Stmt, StmtKind, Ty, TyKind, TypeBinding,
};
use rustc_lexer::{tokenize, TokenKind};
use rustc_lint::LateContext;
use rustc_middle::ty::TypeckResults;
use rustc_span::symbol::Ident;
use std::hash::{Hash, Hasher};

/// Type used to check whether two ast are the same. This is different from the
/// operator
/// `==` on ast types as this operator would compare true equality with ID and
/// span.
///
/// Note that some expressions kinds are not considered but could be added.
pub struct SpanlessEq<'a, 'tcx> {
    /// Context used to evaluate constant expressions.
    cx: &'a LateContext<'tcx>,
    maybe_typeck_results: Option<&'tcx TypeckResults<'tcx>>,
    allow_side_effects: bool,
    expr_fallback: Option<Box<dyn FnMut(&Expr<'_>, &Expr<'_>) -> bool + 'a>>,
}

impl<'a, 'tcx> SpanlessEq<'a, 'tcx> {
    pub fn new(cx: &'a LateContext<'tcx>) -> Self {
        Self {
            cx,
            maybe_typeck_results: cx.maybe_typeck_results(),
            allow_side_effects: true,
            expr_fallback: None,
        }
    }

    /// Consider expressions containing potential side effects as not equal.
    pub fn deny_side_effects(self) -> Self {
        Self {
            allow_side_effects: false,
            ..self
        }
    }

    pub fn expr_fallback(self, expr_fallback: impl FnMut(&Expr<'_>, &Expr<'_>) -> bool + 'a) -> Self {
        Self {
            expr_fallback: Some(Box::new(expr_fallback)),
            ..self
        }
    }

    /// Use this method to wrap comparisons that may involve inter-expression context.
    /// See `self.locals`.
    pub fn inter_expr(&mut self) -> HirEqInterExpr<'_, 'a, 'tcx> {
        HirEqInterExpr {
            inner: self,
            locals: HirIdMap::default(),
        }
    }

    #[allow(dead_code)]
    pub fn eq_block(&mut self, left: &Block<'_>, right: &Block<'_>) -> bool {
        self.inter_expr().eq_block(left, right)
    }

    pub fn eq_expr(&mut self, left: &Expr<'_>, right: &Expr<'_>) -> bool {
        self.inter_expr().eq_expr(left, right)
    }

    pub fn eq_path_segment(&mut self, left: &PathSegment<'_>, right: &PathSegment<'_>) -> bool {
        self.inter_expr().eq_path_segment(left, right)
    }

    pub fn eq_path_segments(&mut self, left: &[PathSegment<'_>], right: &[PathSegment<'_>]) -> bool {
        self.inter_expr().eq_path_segments(left, right)
    }
}

pub struct HirEqInterExpr<'a, 'b, 'tcx> {
    inner: &'a mut SpanlessEq<'b, 'tcx>,

    // When binding are declared, the binding ID in the left expression is mapped to the one on the
    // right. For example, when comparing `{ let x = 1; x + 2 }` and `{ let y = 1; y + 2 }`,
    // these blocks are considered equal since `x` is mapped to `y`.
    locals: HirIdMap<HirId>,
}

impl HirEqInterExpr<'_, '_, '_> {
    pub fn eq_stmt(&mut self, left: &Stmt<'_>, right: &Stmt<'_>) -> bool {
        match (&left.kind, &right.kind) {
            (&StmtKind::Local(ref l), &StmtKind::Local(ref r)) => {
                // This additional check ensures that the type of the locals are equivalent even if the init
                // expression or type have some inferred parts.
                if let Some(typeck) = self.inner.maybe_typeck_results {
                    let l_ty = typeck.pat_ty(&l.pat);
                    let r_ty = typeck.pat_ty(&r.pat);
                    if !rustc_middle::ty::TyS::same_type(l_ty, r_ty) {
                        return false;
                    }
                }

                // eq_pat adds the HirIds to the locals map. We therefor call it last to make sure that
                // these only get added if the init and type is equal.
                both(&l.init, &r.init, |l, r| self.eq_expr(l, r))
                    && both(&l.ty, &r.ty, |l, r| self.eq_ty(l, r))
                    && self.eq_pat(&l.pat, &r.pat)
            },
            (&StmtKind::Expr(ref l), &StmtKind::Expr(ref r)) | (&StmtKind::Semi(ref l), &StmtKind::Semi(ref r)) => {
                self.eq_expr(l, r)
            },
            _ => false,
        }
    }

    /// Checks whether two blocks are the same.
    fn eq_block(&mut self, left: &Block<'_>, right: &Block<'_>) -> bool {
        match (left.stmts, left.expr, right.stmts, right.expr) {
            ([], None, [], None) => {
                // For empty blocks, check to see if the tokens are equal. This will catch the case where a macro
                // expanded to nothing, or the cfg attribute was used.
                let (left, right) = match (
                    snippet_opt(self.inner.cx, left.span),
                    snippet_opt(self.inner.cx, right.span),
                ) {
                    (Some(left), Some(right)) => (left, right),
                    _ => return true,
                };
                let mut left_pos = 0;
                let left = tokenize(&left)
                    .map(|t| {
                        let end = left_pos + t.len;
                        let s = &left[left_pos..end];
                        left_pos = end;
                        (t, s)
                    })
                    .filter(|(t, _)| {
                        !matches!(
                            t.kind,
                            TokenKind::LineComment { .. } | TokenKind::BlockComment { .. } | TokenKind::Whitespace
                        )
                    })
                    .map(|(_, s)| s);
                let mut right_pos = 0;
                let right = tokenize(&right)
                    .map(|t| {
                        let end = right_pos + t.len;
                        let s = &right[right_pos..end];
                        right_pos = end;
                        (t, s)
                    })
                    .filter(|(t, _)| {
                        !matches!(
                            t.kind,
                            TokenKind::LineComment { .. } | TokenKind::BlockComment { .. } | TokenKind::Whitespace
                        )
                    })
                    .map(|(_, s)| s);
                left.eq(right)
            },
            _ => {
                over(&left.stmts, &right.stmts, |l, r| self.eq_stmt(l, r))
                    && both(&left.expr, &right.expr, |l, r| self.eq_expr(l, r))
            },
        }
    }

    #[allow(clippy::similar_names)]
    pub fn eq_expr(&mut self, left: &Expr<'_>, right: &Expr<'_>) -> bool {
        if !self.inner.allow_side_effects && differing_macro_contexts(left.span, right.span) {
            return false;
        }

        if let Some(typeck_results) = self.inner.maybe_typeck_results {
            if let (Some(l), Some(r)) = (
                constant_simple(self.inner.cx, typeck_results, left),
                constant_simple(self.inner.cx, typeck_results, right),
            ) {
                if l == r {
                    return true;
                }
            }
        }

        let is_eq = match (
            &reduce_exprkind(self.inner.cx, &left.kind),
            &reduce_exprkind(self.inner.cx, &right.kind),
        ) {
            (&ExprKind::AddrOf(lb, l_mut, ref le), &ExprKind::AddrOf(rb, r_mut, ref re)) => {
                lb == rb && l_mut == r_mut && self.eq_expr(le, re)
            },
            (&ExprKind::Continue(li), &ExprKind::Continue(ri)) => {
                both(&li.label, &ri.label, |l, r| l.ident.name == r.ident.name)
            },
            (&ExprKind::Assign(ref ll, ref lr, _), &ExprKind::Assign(ref rl, ref rr, _)) => {
                self.inner.allow_side_effects && self.eq_expr(ll, rl) && self.eq_expr(lr, rr)
            },
            (&ExprKind::AssignOp(ref lo, ref ll, ref lr), &ExprKind::AssignOp(ref ro, ref rl, ref rr)) => {
                self.inner.allow_side_effects && lo.node == ro.node && self.eq_expr(ll, rl) && self.eq_expr(lr, rr)
            },
            (&ExprKind::Block(ref l, _), &ExprKind::Block(ref r, _)) => self.eq_block(l, r),
            (&ExprKind::Binary(l_op, ref ll, ref lr), &ExprKind::Binary(r_op, ref rl, ref rr)) => {
                l_op.node == r_op.node && self.eq_expr(ll, rl) && self.eq_expr(lr, rr)
                    || swap_binop(l_op.node, ll, lr).map_or(false, |(l_op, ll, lr)| {
                        l_op == r_op.node && self.eq_expr(ll, rl) && self.eq_expr(lr, rr)
                    })
            },
            (&ExprKind::Break(li, ref le), &ExprKind::Break(ri, ref re)) => {
                both(&li.label, &ri.label, |l, r| l.ident.name == r.ident.name)
                    && both(le, re, |l, r| self.eq_expr(l, r))
            },
            (&ExprKind::Box(ref l), &ExprKind::Box(ref r)) => self.eq_expr(l, r),
            (&ExprKind::Call(l_fun, l_args), &ExprKind::Call(r_fun, r_args)) => {
                self.inner.allow_side_effects && self.eq_expr(l_fun, r_fun) && self.eq_exprs(l_args, r_args)
            },
            (&ExprKind::Cast(ref lx, ref lt), &ExprKind::Cast(ref rx, ref rt))
            | (&ExprKind::Type(ref lx, ref lt), &ExprKind::Type(ref rx, ref rt)) => {
                self.eq_expr(lx, rx) && self.eq_ty(lt, rt)
            },
            (&ExprKind::Field(ref l_f_exp, ref l_f_ident), &ExprKind::Field(ref r_f_exp, ref r_f_ident)) => {
                l_f_ident.name == r_f_ident.name && self.eq_expr(l_f_exp, r_f_exp)
            },
            (&ExprKind::Index(ref la, ref li), &ExprKind::Index(ref ra, ref ri)) => {
                self.eq_expr(la, ra) && self.eq_expr(li, ri)
            },
            (&ExprKind::If(ref lc, ref lt, ref le), &ExprKind::If(ref rc, ref rt, ref re)) => {
                self.eq_expr(lc, rc) && self.eq_expr(&**lt, &**rt) && both(le, re, |l, r| self.eq_expr(l, r))
            },
            (&ExprKind::Lit(ref l), &ExprKind::Lit(ref r)) => l.node == r.node,
            (&ExprKind::Loop(ref lb, ref ll, ref lls, _), &ExprKind::Loop(ref rb, ref rl, ref rls, _)) => {
                lls == rls && self.eq_block(lb, rb) && both(ll, rl, |l, r| l.ident.name == r.ident.name)
            },
            (&ExprKind::Match(ref le, ref la, ref ls), &ExprKind::Match(ref re, ref ra, ref rs)) => {
                ls == rs
                    && self.eq_expr(le, re)
                    && over(la, ra, |l, r| {
                        self.eq_pat(&l.pat, &r.pat)
                            && both(&l.guard, &r.guard, |l, r| self.eq_guard(l, r))
                            && self.eq_expr(&l.body, &r.body)
                    })
            },
            (&ExprKind::MethodCall(l_path, _, l_args, _), &ExprKind::MethodCall(r_path, _, r_args, _)) => {
                self.inner.allow_side_effects && self.eq_path_segment(l_path, r_path) && self.eq_exprs(l_args, r_args)
            },
            (&ExprKind::Repeat(ref le, ref ll_id), &ExprKind::Repeat(ref re, ref rl_id)) => {
                let mut celcx = constant_context(self.inner.cx, self.inner.cx.tcx.typeck_body(ll_id.body));
                let ll = celcx.expr(&self.inner.cx.tcx.hir().body(ll_id.body).value);
                let mut celcx = constant_context(self.inner.cx, self.inner.cx.tcx.typeck_body(rl_id.body));
                let rl = celcx.expr(&self.inner.cx.tcx.hir().body(rl_id.body).value);

                self.eq_expr(le, re) && ll == rl
            },
            (&ExprKind::Ret(ref l), &ExprKind::Ret(ref r)) => both(l, r, |l, r| self.eq_expr(l, r)),
            (&ExprKind::Path(ref l), &ExprKind::Path(ref r)) => self.eq_qpath(l, r),
            (&ExprKind::Struct(ref l_path, ref lf, ref lo), &ExprKind::Struct(ref r_path, ref rf, ref ro)) => {
                self.eq_qpath(l_path, r_path)
                    && both(lo, ro, |l, r| self.eq_expr(l, r))
                    && over(lf, rf, |l, r| self.eq_expr_field(l, r))
            },
            (&ExprKind::Tup(l_tup), &ExprKind::Tup(r_tup)) => self.eq_exprs(l_tup, r_tup),
            (&ExprKind::Unary(l_op, ref le), &ExprKind::Unary(r_op, ref re)) => l_op == r_op && self.eq_expr(le, re),
            (&ExprKind::Array(l), &ExprKind::Array(r)) => self.eq_exprs(l, r),
            (&ExprKind::DropTemps(ref le), &ExprKind::DropTemps(ref re)) => self.eq_expr(le, re),
            _ => false,
        };
        is_eq || self.inner.expr_fallback.as_mut().map_or(false, |f| f(left, right))
    }

    fn eq_exprs(&mut self, left: &[Expr<'_>], right: &[Expr<'_>]) -> bool {
        over(left, right, |l, r| self.eq_expr(l, r))
    }

    fn eq_expr_field(&mut self, left: &ExprField<'_>, right: &ExprField<'_>) -> bool {
        left.ident.name == right.ident.name && self.eq_expr(&left.expr, &right.expr)
    }

    fn eq_guard(&mut self, left: &Guard<'_>, right: &Guard<'_>) -> bool {
        match (left, right) {
            (Guard::If(l), Guard::If(r)) => self.eq_expr(l, r),
            (Guard::IfLet(lp, le), Guard::IfLet(rp, re)) => self.eq_pat(lp, rp) && self.eq_expr(le, re),
            _ => false,
        }
    }

    fn eq_generic_arg(&mut self, left: &GenericArg<'_>, right: &GenericArg<'_>) -> bool {
        match (left, right) {
            (GenericArg::Lifetime(l_lt), GenericArg::Lifetime(r_lt)) => Self::eq_lifetime(l_lt, r_lt),
            (GenericArg::Type(l_ty), GenericArg::Type(r_ty)) => self.eq_ty(l_ty, r_ty),
            _ => false,
        }
    }

    fn eq_lifetime(left: &Lifetime, right: &Lifetime) -> bool {
        left.name == right.name
    }

    fn eq_pat_field(&mut self, left: &PatField<'_>, right: &PatField<'_>) -> bool {
        let (PatField { ident: li, pat: lp, .. }, PatField { ident: ri, pat: rp, .. }) = (&left, &right);
        li.name == ri.name && self.eq_pat(lp, rp)
    }

    /// Checks whether two patterns are the same.
    fn eq_pat(&mut self, left: &Pat<'_>, right: &Pat<'_>) -> bool {
        match (&left.kind, &right.kind) {
            (&PatKind::Box(ref l), &PatKind::Box(ref r)) => self.eq_pat(l, r),
            (&PatKind::Struct(ref lp, ref la, ..), &PatKind::Struct(ref rp, ref ra, ..)) => {
                self.eq_qpath(lp, rp) && over(la, ra, |l, r| self.eq_pat_field(l, r))
            },
            (&PatKind::TupleStruct(ref lp, ref la, ls), &PatKind::TupleStruct(ref rp, ref ra, rs)) => {
                self.eq_qpath(lp, rp) && over(la, ra, |l, r| self.eq_pat(l, r)) && ls == rs
            },
            (&PatKind::Binding(lb, li, _, ref lp), &PatKind::Binding(rb, ri, _, ref rp)) => {
                let eq = lb == rb && both(lp, rp, |l, r| self.eq_pat(l, r));
                if eq {
                    self.locals.insert(li, ri);
                }
                eq
            },
            (&PatKind::Path(ref l), &PatKind::Path(ref r)) => self.eq_qpath(l, r),
            (&PatKind::Lit(ref l), &PatKind::Lit(ref r)) => self.eq_expr(l, r),
            (&PatKind::Tuple(ref l, ls), &PatKind::Tuple(ref r, rs)) => {
                ls == rs && over(l, r, |l, r| self.eq_pat(l, r))
            },
            (&PatKind::Range(ref ls, ref le, li), &PatKind::Range(ref rs, ref re, ri)) => {
                both(ls, rs, |a, b| self.eq_expr(a, b)) && both(le, re, |a, b| self.eq_expr(a, b)) && (li == ri)
            },
            (&PatKind::Ref(ref le, ref lm), &PatKind::Ref(ref re, ref rm)) => lm == rm && self.eq_pat(le, re),
            (&PatKind::Slice(ref ls, ref li, ref le), &PatKind::Slice(ref rs, ref ri, ref re)) => {
                over(ls, rs, |l, r| self.eq_pat(l, r))
                    && over(le, re, |l, r| self.eq_pat(l, r))
                    && both(li, ri, |l, r| self.eq_pat(l, r))
            },
            (&PatKind::Wild, &PatKind::Wild) => true,
            _ => false,
        }
    }

    #[allow(clippy::similar_names)]
    fn eq_qpath(&mut self, left: &QPath<'_>, right: &QPath<'_>) -> bool {
        match (left, right) {
            (&QPath::Resolved(ref lty, ref lpath), &QPath::Resolved(ref rty, ref rpath)) => {
                both(lty, rty, |l, r| self.eq_ty(l, r)) && self.eq_path(lpath, rpath)
            },
            (&QPath::TypeRelative(ref lty, ref lseg), &QPath::TypeRelative(ref rty, ref rseg)) => {
                self.eq_ty(lty, rty) && self.eq_path_segment(lseg, rseg)
            },
            (&QPath::LangItem(llang_item, _), &QPath::LangItem(rlang_item, _)) => llang_item == rlang_item,
            _ => false,
        }
    }

    fn eq_path(&mut self, left: &Path<'_>, right: &Path<'_>) -> bool {
        match (left.res, right.res) {
            (Res::Local(l), Res::Local(r)) => l == r || self.locals.get(&l) == Some(&r),
            (Res::Local(_), _) | (_, Res::Local(_)) => false,
            _ => over(&left.segments, &right.segments, |l, r| self.eq_path_segment(l, r)),
        }
    }

    fn eq_path_parameters(&mut self, left: &GenericArgs<'_>, right: &GenericArgs<'_>) -> bool {
        if !(left.parenthesized || right.parenthesized) {
            over(&left.args, &right.args, |l, r| self.eq_generic_arg(l, r)) // FIXME(flip1995): may not work
                && over(&left.bindings, &right.bindings, |l, r| self.eq_type_binding(l, r))
        } else if left.parenthesized && right.parenthesized {
            over(left.inputs(), right.inputs(), |l, r| self.eq_ty(l, r))
                && both(&Some(&left.bindings[0].ty()), &Some(&right.bindings[0].ty()), |l, r| {
                    self.eq_ty(l, r)
                })
        } else {
            false
        }
    }

    pub fn eq_path_segments(&mut self, left: &[PathSegment<'_>], right: &[PathSegment<'_>]) -> bool {
        left.len() == right.len() && left.iter().zip(right).all(|(l, r)| self.eq_path_segment(l, r))
    }

    pub fn eq_path_segment(&mut self, left: &PathSegment<'_>, right: &PathSegment<'_>) -> bool {
        // The == of idents doesn't work with different contexts,
        // we have to be explicit about hygiene
        left.ident.name == right.ident.name && both(&left.args, &right.args, |l, r| self.eq_path_parameters(l, r))
    }

    #[allow(clippy::similar_names)]
    fn eq_ty(&mut self, left: &Ty<'_>, right: &Ty<'_>) -> bool {
        match (&left.kind, &right.kind) {
            (&TyKind::Slice(ref l_vec), &TyKind::Slice(ref r_vec)) => self.eq_ty(l_vec, r_vec),
            (&TyKind::Array(ref lt, ref ll_id), &TyKind::Array(ref rt, ref rl_id)) => {
                let cx = self.inner.cx;
                let eval_const =
                    |body| constant_context(cx, cx.tcx.typeck_body(body)).expr(&cx.tcx.hir().body(body).value);
                self.eq_ty(lt, rt) && eval_const(ll_id.body) == eval_const(rl_id.body)
            },
            (&TyKind::Ptr(ref l_mut), &TyKind::Ptr(ref r_mut)) => {
                l_mut.mutbl == r_mut.mutbl && self.eq_ty(&*l_mut.ty, &*r_mut.ty)
            },
            (&TyKind::Rptr(_, ref l_rmut), &TyKind::Rptr(_, ref r_rmut)) => {
                l_rmut.mutbl == r_rmut.mutbl && self.eq_ty(&*l_rmut.ty, &*r_rmut.ty)
            },
            (&TyKind::Path(ref l), &TyKind::Path(ref r)) => self.eq_qpath(l, r),
            (&TyKind::Tup(ref l), &TyKind::Tup(ref r)) => over(l, r, |l, r| self.eq_ty(l, r)),
            (&TyKind::Infer, &TyKind::Infer) => true,
            _ => false,
        }
    }

    fn eq_type_binding(&mut self, left: &TypeBinding<'_>, right: &TypeBinding<'_>) -> bool {
        left.ident.name == right.ident.name && self.eq_ty(&left.ty(), &right.ty())
    }
}

/// Some simple reductions like `{ return }` => `return`
fn reduce_exprkind<'hir>(cx: &LateContext<'_>, kind: &'hir ExprKind<'hir>) -> &'hir ExprKind<'hir> {
    if let ExprKind::Block(block, _) = kind {
        match (block.stmts, block.expr) {
            // From an `if let` expression without an `else` block. The arm for the implicit wild pattern is an empty
            // block with an empty span.
            ([], None) if block.span.is_empty() => &ExprKind::Tup(&[]),
            // `{}` => `()`
            ([], None) => match snippet_opt(cx, block.span) {
                // Don't reduce if there are any tokens contained in the braces
                Some(snip)
                    if tokenize(&snip)
                        .map(|t| t.kind)
                        .filter(|t| {
                            !matches!(
                                t,
                                TokenKind::LineComment { .. } | TokenKind::BlockComment { .. } | TokenKind::Whitespace
                            )
                        })
                        .ne([TokenKind::OpenBrace, TokenKind::CloseBrace].iter().copied()) =>
                {
                    kind
                },
                _ => &ExprKind::Tup(&[]),
            },
            ([], Some(expr)) => match expr.kind {
                // `{ return .. }` => `return ..`
                ExprKind::Ret(..) => &expr.kind,
                _ => kind,
            },
            ([stmt], None) => match stmt.kind {
                StmtKind::Expr(expr) | StmtKind::Semi(expr) => match expr.kind {
                    // `{ return ..; }` => `return ..`
                    ExprKind::Ret(..) => &expr.kind,
                    _ => kind,
                },
                _ => kind,
            },
            _ => kind,
        }
    } else {
        kind
    }
}

fn swap_binop<'a>(
    binop: BinOpKind,
    lhs: &'a Expr<'a>,
    rhs: &'a Expr<'a>,
) -> Option<(BinOpKind, &'a Expr<'a>, &'a Expr<'a>)> {
    match binop {
        BinOpKind::Add | BinOpKind::Eq | BinOpKind::Ne | BinOpKind::BitAnd | BinOpKind::BitXor | BinOpKind::BitOr => {
            Some((binop, rhs, lhs))
        },
        BinOpKind::Lt => Some((BinOpKind::Gt, rhs, lhs)),
        BinOpKind::Le => Some((BinOpKind::Ge, rhs, lhs)),
        BinOpKind::Ge => Some((BinOpKind::Le, rhs, lhs)),
        BinOpKind::Gt => Some((BinOpKind::Lt, rhs, lhs)),
        BinOpKind::Mul // Not always commutative, e.g. with matrices. See issue #5698
        | BinOpKind::Shl
        | BinOpKind::Shr
        | BinOpKind::Rem
        | BinOpKind::Sub
        | BinOpKind::Div
        | BinOpKind::And
        | BinOpKind::Or => None,
    }
}

/// Checks if the two `Option`s are both `None` or some equal values as per
/// `eq_fn`.
pub fn both<X>(l: &Option<X>, r: &Option<X>, mut eq_fn: impl FnMut(&X, &X) -> bool) -> bool {
    l.as_ref()
        .map_or_else(|| r.is_none(), |x| r.as_ref().map_or(false, |y| eq_fn(x, y)))
}

/// Checks if two slices are equal as per `eq_fn`.
pub fn over<X>(left: &[X], right: &[X], mut eq_fn: impl FnMut(&X, &X) -> bool) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(x, y)| eq_fn(x, y))
}

/// Counts how many elements of the slices are equal as per `eq_fn`.
pub fn count_eq<X: Sized>(
    left: &mut dyn Iterator<Item = X>,
    right: &mut dyn Iterator<Item = X>,
    mut eq_fn: impl FnMut(&X, &X) -> bool,
) -> usize {
    left.zip(right).take_while(|(l, r)| eq_fn(l, r)).count()
}

/// Checks if two expressions evaluate to the same value, and don't contain any side effects.
pub fn eq_expr_value(cx: &LateContext<'_>, left: &Expr<'_>, right: &Expr<'_>) -> bool {
    SpanlessEq::new(cx).deny_side_effects().eq_expr(left, right)
}

pub fn hash_spanless_fx(cx: &LateContext<'_>, item: &impl SpanlessHash) -> u64 {
    let mut fx = FxHasher::default();
    item.hash_spanless(&mut SpanlessHasher::new(cx), &mut fx);
    fx.finish()
}

/// Type used to hash an ast element. This is different from the `Hash` trait
/// on ast types as this
/// trait would consider IDs and spans.
///
/// All expressions kind are hashed, but some might have a weaker hash.
pub struct SpanlessHasher<'a, 'tcx> {
    cx: &'a LateContext<'tcx>,
    maybe_typeck_results: Option<&'a TypeckResults<'tcx>>,
}

impl<'a, 'tcx> SpanlessHasher<'a, 'tcx> {
    pub fn new(cx: &'a LateContext<'tcx>) -> Self {
        Self {
            cx,
            maybe_typeck_results: cx.maybe_typeck_results(),
        }
    }
}

pub trait SpanlessHash {
    fn hash_spanless<H: Hasher>(&self, sh: &mut SpanlessHasher<'_, '_>, state: &mut H);
}

macro_rules! spanless_hash_impls {
    (
        fn hash_spanless(&$slf:ident, $spanless:ident, $state:ident);
        $($ty:ty => $body:expr $(,)?)*
    ) => {
        $(
        impl SpanlessHash for $ty {
            fn hash_spanless<H: Hasher>(
                &$slf,
                #[allow(unused_variables)] $spanless: &mut SpanlessHasher<'_, '_>,
                $state: &mut H
            ) {
                $body
            }
        }
        )*
    };
}

spanless_hash_impls! {
    fn hash_spanless(&self, sh, state);

    Arm<'_> => (self.pat, &self.guard, self.body).hash_spanless(sh, state),
    BareFnTy<'_> => {
        (self.unsafety, self.abi).hash(state);
        self.decl.inputs.hash_spanless(sh, state);
        std::mem::discriminant(&self.decl.output).hash(state);
        match self.decl.output {
            FnRetTy::DefaultReturn(_) => {},
            FnRetTy::Return(ref ty) => ty.hash_spanless(sh, state),
        }
        self.decl.c_variadic.hash(state);
    }
    Block<'_> => {
        (self.stmts, self.expr).hash_spanless(sh, state);
        std::mem::discriminant(&self.rules).hash(state);
    }
    BodyId => {
        // swap out TypeckResults when hashing a body
        let old_maybe_typeck_results = sh
            .maybe_typeck_results
            .replace(sh.cx.tcx.typeck_body(*self));
        sh.cx.tcx.hir().body(*self).value.hash_spanless(sh, state);
        sh.maybe_typeck_results = old_maybe_typeck_results;
    }
    Destination => self.label.hash_spanless(sh, state),
    Expr<'_> => {
        let simple_const = sh
            .maybe_typeck_results
            .and_then(|typeck_results| constant_simple(sh.cx, typeck_results, self));

        // const hashing may result in the same hash as some unrelated node, so add a sort of
        // discriminant depending on which path we're choosing next
        simple_const.hash(state);
        if simple_const.is_some() {
            return;
        }

        std::mem::discriminant(&self.kind).hash(state);

        match self.kind {
            ExprKind::AddrOf(kind, m, ref e) => {
                std::mem::discriminant(&kind).hash(state);
                m.hash(state);
                e.hash_spanless(sh, state);
            },
            ExprKind::Continue(d) => d.hash_spanless(sh, state),
            ExprKind::Assign(ref l, ref r, _) => (l, r).hash_spanless(sh, state),
            ExprKind::AssignOp(ref o, ref l, ref r) => {
                std::mem::discriminant(&o.node).hash(state);
                (l, r).hash_spanless(sh, state);
            },
            ExprKind::Block(ref b, _) => b.hash_spanless(sh, state),
            ExprKind::Binary(op, ref l, ref r) => {
                std::mem::discriminant(&op.node).hash(state);
                (l, r).hash_spanless(sh, state);
            },
            ExprKind::Break(d, j) => (d, j).hash_spanless(sh, state),
            ExprKind::Box(ref e)
            | ExprKind::DropTemps(ref e)
            | ExprKind::Yield(ref e, _) => e.hash_spanless(sh, state),
            ExprKind::Call(ref fun, args) => (fun, args).hash_spanless(sh, state),
            ExprKind::Cast(ref e, ty)
            | ExprKind::Type(ref e, ty) => (e, ty).hash_spanless(sh, state),
            ExprKind::Closure(cap, _, eid, _, _) => {
                std::mem::discriminant(&cap).hash(state);
                // closures inherit TypeckResults
                sh.cx.tcx.hir().body(eid).value.hash_spanless(sh, state);
            },
            ExprKind::Field(ref e, ref f) => (e, f).hash_spanless(sh, state),
            ExprKind::Index(ref a, ref i) => (a, i).hash_spanless(sh, state),
            ExprKind::InlineAsm(ref asm) => asm.hash_spanless(sh, state),
            ExprKind::LlvmInlineAsm(..) | ExprKind::Err => {},
            ExprKind::Lit(ref l) => l.node.hash(state),
            ExprKind::Loop(b, label, ..) => (b, label).hash_spanless(sh, state),
            ExprKind::If(cond, then, els) => (cond, then, els).hash_spanless(sh, state),
            ExprKind::Match(e, arms, ref s) => {
                (e, arms).hash_spanless(sh, state);
                s.hash(state);
            },
            ExprKind::MethodCall(ref path, _, args, _) => (path, args).hash_spanless(sh, state),
            ExprKind::ConstBlock(ref l_id) => l_id.body.hash_spanless(sh, state),
            ExprKind::Repeat(ref e, ref l_id) => (e, l_id.body).hash_spanless(sh, state),
            ExprKind::Ret(e) => e.hash_spanless(sh, state),
            ExprKind::Path(ref qpath) => qpath.hash_spanless(sh, state),
            ExprKind::Struct(p, f, e) => (p, f, e).hash_spanless(sh, state),
            ExprKind::Array(e) | ExprKind::Tup(e) => e.hash_spanless(sh, state),
            ExprKind::Unary(lop, ref le) => {
                std::mem::discriminant(&lop).hash(state);
                le.hash_spanless(sh, state);
            },
        }
    }
    ExprField<'_> => (self.ident, self.expr).hash_spanless(sh, state),
    GenericArg<'_> => match *self {
        GenericArg::Lifetime(l) => l.hash_spanless(sh, state),
        GenericArg::Type(ref ty) => ty.hash_spanless(sh, state),
        GenericArg::Const(ref ca) => ca.value.body.hash_spanless(sh, state),
    }
    Guard<'_> => match *self {
        Guard::If(e) | Guard::IfLet(_, e) => e.hash_spanless(sh, state),
    }
    InlineAsm<'_> => {
        self.template.hash_spanless(sh, state);
        self.options.hash(state);
        self.operands.len().hash(state);
        for (op, _) in self.operands {
            match op {
                InlineAsmOperand::In { reg, expr } => {
                    reg.hash(state);
                    expr.hash_spanless(sh, state);
                },
                InlineAsmOperand::Out { reg, late, expr } => {
                    (reg, late).hash(state);
                    expr.hash_spanless(sh, state)
                },
                InlineAsmOperand::InOut { reg, late, expr } => {
                    (reg, late).hash(state);
                    expr.hash_spanless(sh, state);
                },
                InlineAsmOperand::SplitInOut {
                    reg,
                    late,
                    in_expr,
                    out_expr,
                } => {
                    (reg, late).hash(state);
                    (in_expr, out_expr).hash_spanless(sh, state);
                },
                InlineAsmOperand::Const { anon_const } => anon_const.body.hash_spanless(sh, state),
                InlineAsmOperand::Sym { expr } => expr.hash_spanless(sh, state),
            }
        }
    }
    InlineAsmTemplatePiece => match self {
        InlineAsmTemplatePiece::String(s) => s.hash(state),
        InlineAsmTemplatePiece::Placeholder {
            operand_idx,
            modifier,
            span: _,
        } => (operand_idx, modifier).hash(state),
    }
    Ident => self.name.hash(state),
    Label => self.ident.hash_spanless(sh, state),
    Lifetime => {
        std::mem::discriminant(&self.name).hash(state);
        if let LifetimeName::Param(ref name) = self.name {
            std::mem::discriminant(name).hash(state);
            match name {
                ParamName::Plain(ref ident) => ident.hash_spanless(sh, state),
                ParamName::Fresh(ref size) => size.hash(state),
                ParamName::Error => {},
            }
        }
    }
    MutTy<'_> => {
        self.ty.hash_spanless(sh, state);
        self.mutbl.hash(state);
    }
    Pat<'_> => {
        std::mem::discriminant(&self.kind).hash(state);
        match self.kind {
            PatKind::Binding(ann, _, _, pat) => {
                std::mem::discriminant(&ann).hash(state);
                pat.hash_spanless(sh, state);
            },
            PatKind::Box(pat) => pat.hash_spanless(sh, state),
            PatKind::Lit(expr) => expr.hash_spanless(sh, state),
            PatKind::Or(pats) => pats.hash_spanless(sh, state),
            PatKind::Path(ref qpath) => qpath.hash_spanless(sh, state),
            PatKind::Range(s, e, i) => {
                (s, e).hash_spanless(sh, state);
                std::mem::discriminant(&i).hash(state);
            },
            PatKind::Ref(pat, mu) => {
                pat.hash_spanless(sh, state);
                std::mem::discriminant(&mu).hash(state);
            },
            PatKind::Slice(l, m, r) => (l, m, r).hash_spanless(sh, state),
            PatKind::Struct(ref qpath, fields, e) => {
                (qpath, fields).hash_spanless(sh, state);
                e.hash(state)
            },
            PatKind::Tuple(pats, e) => {
                pats.hash_spanless(sh, state);
                e.hash(state);
            },
            PatKind::TupleStruct(ref qpath, pats, e) => {
                (qpath, pats).hash_spanless(sh, state);
                e.hash(state);
            },
            PatKind::Wild => {},
        }
    }
    Path<'_> => match self.res {
        // constant hash since equality is dependant on inter-expression context
        Res::Local(_) => 1_u8.hash(state),
        _ => self.segments.hash_spanless(sh, state),
    }
    PatField<'_> => (self.ident, self.pat).hash_spanless(sh, state),
    PathSegment<'_> => (self.ident, self.args().args).hash_spanless(sh, state),
    Stmt<'_> => {
        std::mem::discriminant(&self.kind).hash(state);
        match self.kind {
            StmtKind::Local(local) => (local.pat, local.init).hash_spanless(sh, state),
            StmtKind::Item(..) => {},
            StmtKind::Expr(expr) | StmtKind::Semi(expr) => expr.hash_spanless(sh, state),
        }
    }
    Ty<'_> => {
        std::mem::discriminant(&self.kind).hash(state);
        match self.kind {
            TyKind::Slice(ty) => ty.hash_spanless(sh, state),
            TyKind::Array(ty, anon_const) => (ty, anon_const.body).hash_spanless(sh, state),
            TyKind::Ptr(ref mut_ty) => mut_ty.hash_spanless(sh, state),
            TyKind::Rptr(lifetime, ref mut_ty) => (lifetime, mut_ty).hash_spanless(sh, state),
            TyKind::BareFn(bfn) => bfn.hash_spanless(sh, state),
            TyKind::Tup(tys) => tys.hash_spanless(sh, state),
            TyKind::Path(ref qpath) => qpath.hash_spanless(sh, state),
            TyKind::OpaqueDef(_, arg_list) => arg_list.hash_spanless(sh, state),
            TyKind::TraitObject(_, lifetime, _) => lifetime.hash_spanless(sh, state),
            TyKind::Typeof(anon_const) => anon_const.body.hash_spanless(sh, state),
            TyKind::Err | TyKind::Infer | TyKind::Never => {},
        }
    }
    QPath<'_> => match *self {
        QPath::Resolved(_, ref path) => path.hash_spanless(sh, state),
        QPath::TypeRelative(_, ref path) => path.ident.hash_spanless(sh, state),
        QPath::LangItem(lang_item, ..) => lang_item.hash(state),
    }
}

impl<'a, T> SpanlessHash for &T
where
    T: ?Sized + SpanlessHash,
{
    fn hash_spanless<H: Hasher>(&self, sh: &mut SpanlessHasher<'_, '_>, state: &mut H) {
        (*self).hash_spanless(sh, state);
    }
}

impl<'a, T> SpanlessHash for [T]
where
    T: SpanlessHash,
{
    fn hash_spanless<H: Hasher>(&self, sh: &mut SpanlessHasher<'_, '_>, state: &mut H) {
        self.len().hash(state);
        for e in self {
            e.hash_spanless(sh, state);
        }
    }
}

impl<'a, T> SpanlessHash for Option<T>
where
    T: SpanlessHash,
{
    fn hash_spanless<H: Hasher>(&self, sh: &mut SpanlessHasher<'_, '_>, state: &mut H) {
        self.is_some().hash(state);
        if let Some(e) = self {
            e.hash_spanless(sh, state);
        }
    }
}

macro_rules! spanless_hash_tuple {
    ($($a:ident)*) => {
        impl<$($a: SpanlessHash),*> SpanlessHash for ($($a),*) {
            fn hash_spanless<H: Hasher>(&self, sh: &mut SpanlessHasher<'_, '_>, state: &mut H) {
                #[allow(non_snake_case)]
                let ($(ref $a),*) = *self;
                $($a.hash_spanless(sh, state);)*
            }
        }
    };
}

spanless_hash_tuple!(A B);
spanless_hash_tuple!(A B C);
