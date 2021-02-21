use crate::consts::{constant_context, constant_simple};
use crate::utils::differing_macro_contexts;
use rustc_ast::ast::InlineAsmTemplatePiece;
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::stable_hasher::{HashStable, StableHasher};
use rustc_hir::def::Res;
use rustc_hir::{
    BinOpKind, Block, BlockCheckMode, BodyId, BorrowKind, CaptureBy, Expr, ExprKind, Field, FieldPat, FnRetTy,
    GenericArg, GenericArgs, Guard, HirId, InlineAsmOperand, Lifetime, LifetimeName, ParamName, Pat, PatKind, Path,
    PathSegment, QPath, Stmt, StmtKind, Ty, TyKind, TypeBinding,
};
use rustc_lint::LateContext;
use rustc_middle::ich::StableHashingContextProvider;
use rustc_middle::ty::TypeckResults;
use rustc_span::Symbol;
use std::hash::Hash;
use std::iter::ExactSizeIterator;

macro_rules! all {
    ($a:expr, $b:expr, $s:ident.$eq_fn:ident) => {
        all_eq_with($a, $b, |a, b| $s.$eq_fn(a, b))
    };
}

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
    fn inter_expr(&mut self) -> HirEqInterExpr<'_, 'a, 'tcx> {
        HirEqInterExpr {
            inner: self,
            locals: FxHashMap::default(),
        }
    }

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
        let mut inter_expr = self.inter_expr();
        all!(left, right, inter_expr.eq_path_segment)
    }

    pub fn eq_ty_kind(&mut self, left: &TyKind<'_>, right: &TyKind<'_>) -> bool {
        self.inter_expr().eq_ty_kind(left, right)
    }
}

struct HirEqInterExpr<'a, 'b, 'tcx> {
    inner: &'a mut SpanlessEq<'b, 'tcx>,

    // When binding are declared, the binding ID in the left expression is mapped to the one on the
    // right. For example, when comparing `{ let x = 1; x + 2 }` and `{ let y = 1; y + 2 }`,
    // these blocks are considered equal since `x` is mapped to `y`.
    locals: FxHashMap<HirId, HirId>,
}

impl HirEqInterExpr<'_, '_, '_> {
    fn eq_stmt(&mut self, left: &Stmt<'_>, right: &Stmt<'_>) -> bool {
        match (&left.kind, &right.kind) {
            (&StmtKind::Local(l), &StmtKind::Local(r)) => {
                self.eq_pat(l.pat, r.pat) && all!(l.ty, r.ty, self.eq_ty) && all!(l.init, r.init, self.eq_expr)
            },
            (&StmtKind::Expr(l), &StmtKind::Expr(r)) | (&StmtKind::Semi(l), &StmtKind::Semi(r)) => self.eq_expr(l, r),
            _ => false,
        }
    }

    /// Checks whether two blocks are the same.
    fn eq_block(&mut self, left: &Block<'_>, right: &Block<'_>) -> bool {
        all!(left.stmts, right.stmts, self.eq_stmt) && all!(left.expr, right.expr, self.eq_expr)
    }

    #[allow(clippy::similar_names)]
    fn eq_expr(&mut self, left: &Expr<'_>, right: &Expr<'_>) -> bool {
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

        let is_eq = match (reduce_exprkind(&left.kind), reduce_exprkind(&right.kind)) {
            (&ExprKind::AddrOf(lb, l_mut, le), &ExprKind::AddrOf(rb, r_mut, re)) => {
                lb == rb && l_mut == r_mut && self.eq_expr(le, re)
            },
            (&ExprKind::Continue(li), &ExprKind::Continue(ri)) => all_eq_by(&li.label, &ri.label, |l| l.ident.name),
            (&ExprKind::Assign(ll, lr, _), &ExprKind::Assign(rl, rr, _)) => {
                self.inner.allow_side_effects && self.eq_expr(ll, rl) && self.eq_expr(lr, rr)
            },
            (&ExprKind::AssignOp(lo, ll, lr), &ExprKind::AssignOp(ro, rl, rr)) => {
                self.inner.allow_side_effects && lo.node == ro.node && self.eq_expr(ll, rl) && self.eq_expr(lr, rr)
            },
            (&ExprKind::Block(l, _), &ExprKind::Block(r, _)) => self.eq_block(l, r),
            (&ExprKind::Binary(l_op, ll, lr), &ExprKind::Binary(r_op, rl, rr)) => {
                l_op.node == r_op.node && self.eq_expr(ll, rl) && self.eq_expr(lr, rr)
                    || swap_binop(l_op.node, ll, lr).map_or(false, |(l_op, ll, lr)| {
                        l_op == r_op.node && self.eq_expr(ll, rl) && self.eq_expr(lr, rr)
                    })
            },
            (&ExprKind::Break(li, le), &ExprKind::Break(ri, re)) => {
                all_eq_by(li.label, ri.label, |l| l.ident.name) && all!(le, re, self.eq_expr)
            },
            (&ExprKind::Box(l), &ExprKind::Box(r)) => self.eq_expr(l, r),
            (&ExprKind::Call(l_fun, l_args), &ExprKind::Call(r_fun, r_args)) => {
                self.inner.allow_side_effects && self.eq_expr(l_fun, r_fun) && all!(l_args, r_args, self.eq_expr)
            },
            (&ExprKind::Cast(lx, lt), &ExprKind::Cast(rx, rt)) | (&ExprKind::Type(lx, lt), &ExprKind::Type(rx, rt)) => {
                self.eq_expr(lx, rx) && self.eq_ty(lt, rt)
            },
            (&ExprKind::Field(l_f_exp, l_f_ident), &ExprKind::Field(r_f_exp, r_f_ident)) => {
                l_f_ident.name == r_f_ident.name && self.eq_expr(l_f_exp, r_f_exp)
            },
            (&ExprKind::Index(la, li), &ExprKind::Index(ra, ri)) => self.eq_expr(la, ra) && self.eq_expr(li, ri),
            (&ExprKind::If(lc, lt, le), &ExprKind::If(rc, rt, re)) => {
                self.eq_expr(lc, rc) && self.eq_expr(lt, rt) && all!(le, re, self.eq_expr)
            },
            (ExprKind::Lit(l), ExprKind::Lit(r)) => l.node == r.node,
            (&ExprKind::Loop(lb, ll, lls, _), &ExprKind::Loop(rb, rl, rls, _)) => {
                lls == rls && self.eq_block(lb, rb) && all_eq_by(ll, rl, |l| l.ident.name)
            },
            (&ExprKind::Match(le, la, ls), &ExprKind::Match(re, ra, rs)) => {
                ls == rs
                    && self.eq_expr(le, re)
                    && over(la, ra, |l, r| {
                        self.eq_pat(l.pat, r.pat)
                            && all!(&l.guard, &r.guard, self.eq_guard)
                            && self.eq_expr(l.body, r.body)
                    })
            },
            (&ExprKind::MethodCall(l_path, _, l_args, _), &ExprKind::MethodCall(r_path, _, r_args, _)) => {
                self.inner.allow_side_effects
                    && self.eq_path_segment(l_path, r_path)
                    && all!(l_args, r_args, self.eq_expr)
            },
            (&ExprKind::Repeat(le, ll_id), &ExprKind::Repeat(re, rl_id)) => {
                let mut celcx = constant_context(self.inner.cx, self.inner.cx.tcx.typeck_body(ll_id.body));
                let ll = celcx.expr(&self.inner.cx.tcx.hir().body(ll_id.body).value);
                let mut celcx = constant_context(self.inner.cx, self.inner.cx.tcx.typeck_body(rl_id.body));
                let rl = celcx.expr(&self.inner.cx.tcx.hir().body(rl_id.body).value);

                self.eq_expr(le, re) && ll == rl
            },
            (&ExprKind::Ret(l), &ExprKind::Ret(r)) => all!(l, r, self.eq_expr),
            (ExprKind::Path(l), ExprKind::Path(r)) => self.eq_qpath(l, r),
            (&ExprKind::Struct(l_path, lf, lo), &ExprKind::Struct(r_path, rf, ro)) => {
                self.eq_qpath(l_path, r_path) && all!(lo, ro, self.eq_expr) && all!(lf, rf, self.eq_field)
            },
            (&ExprKind::Tup(l_tup), &ExprKind::Tup(r_tup)) => all!(l_tup, r_tup, self.eq_expr),
            (&ExprKind::Unary(l_op, le), &ExprKind::Unary(r_op, re)) => l_op == r_op && self.eq_expr(le, re),
            (&ExprKind::Array(l), &ExprKind::Array(r)) => all!(l, r, self.eq_expr),
            (&ExprKind::DropTemps(le), &ExprKind::DropTemps(re)) => self.eq_expr(le, re),
            _ => false,
        };
        is_eq || self.inner.expr_fallback.as_mut().map_or(false, |f| f(left, right))
    }

    fn eq_field(&mut self, left: &Field<'_>, right: &Field<'_>) -> bool {
        left.ident.name == right.ident.name && self.eq_expr(left.expr, right.expr)
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

    fn eq_fieldpat(&mut self, left: &FieldPat<'_>, right: &FieldPat<'_>) -> bool {
        let (FieldPat { ident: li, pat: lp, .. }, FieldPat { ident: ri, pat: rp, .. }) = (&left, &right);
        li.name == ri.name && self.eq_pat(lp, rp)
    }

    /// Checks whether two patterns are the same.
    fn eq_pat(&mut self, left: &Pat<'_>, right: &Pat<'_>) -> bool {
        match (&left.kind, &right.kind) {
            (&PatKind::Box(l), &PatKind::Box(r)) => self.eq_pat(l, r),
            (&PatKind::Struct(ref lp, la, ..), &PatKind::Struct(ref rp, ra, ..)) => {
                self.eq_qpath(lp, rp) && all!(la, ra, self.eq_fieldpat)
            },
            (&PatKind::TupleStruct(ref lp, la, ls), &PatKind::TupleStruct(ref rp, ra, rs)) => {
                self.eq_qpath(lp, rp) && all!(la, ra, self.eq_pat) && ls == rs
            },
            (&PatKind::Binding(lb, li, _, lp), &PatKind::Binding(rb, ri, _, rp)) => {
                let eq = lb == rb && all!(lp, rp, self.eq_pat);
                if eq {
                    self.locals.insert(li, ri);
                }
                eq
            },
            (PatKind::Path(l), PatKind::Path(r)) => self.eq_qpath(l, r),
            (&PatKind::Lit(l), &PatKind::Lit(r)) => self.eq_expr(l, r),
            (&PatKind::Tuple(l, ls), &PatKind::Tuple(r, rs)) => ls == rs && all!(l, r, self.eq_pat),
            (&PatKind::Range(ls, le, li), &PatKind::Range(rs, re, ri)) => {
                all!(ls, rs, self.eq_expr) && all!(le, re, self.eq_expr) && li == ri
            },
            (&PatKind::Ref(le, lm), &PatKind::Ref(re, rm)) => lm == rm && self.eq_pat(le, re),
            (&PatKind::Slice(ls, li, le), &PatKind::Slice(rs, ri, re)) => {
                all!(ls, rs, self.eq_pat) && all!(le, re, self.eq_pat) && all!(li, ri, self.eq_pat)
            },
            (&PatKind::Wild, &PatKind::Wild) => true,
            _ => false,
        }
    }

    #[allow(clippy::similar_names)]
    fn eq_qpath(&mut self, left: &QPath<'_>, right: &QPath<'_>) -> bool {
        match (left, right) {
            (&QPath::Resolved(lty, lpath), &QPath::Resolved(rty, rpath)) => {
                all!(lty, rty, self.eq_ty) && self.eq_path(lpath, rpath)
            },
            (&QPath::TypeRelative(lty, lseg), &QPath::TypeRelative(rty, rseg)) => {
                self.eq_ty(lty, rty) && self.eq_path_segment(lseg, rseg)
            },
            (&QPath::LangItem(llang_item, _), &QPath::LangItem(rlang_item, _)) => llang_item == rlang_item,
            _ => false,
        }
    }

    fn eq_path(&mut self, left: &Path<'_>, right: &Path<'_>) -> bool {
        match (left.res, right.res) {
            // the locals may either refer to the exact same binding or to corresponding bindings
            // which are declared within the expressions that are being compared
            (Res::Local(l), Res::Local(r)) => l == r || self.locals.get(&l) == Some(&r),
            (Res::Local(_), _) | (_, Res::Local(_)) => false,
            _ => all!(left.segments, right.segments, self.eq_path_segment),
        }
    }

    fn eq_path_parameters(&mut self, left: &GenericArgs<'_>, right: &GenericArgs<'_>) -> bool {
        if !(left.parenthesized || right.parenthesized) {
            all!(left.args, right.args, self.eq_generic_arg) // FIXME(flip1995): may not work
                && all!(left.bindings, right.bindings, self.eq_type_binding)
        } else if left.parenthesized && right.parenthesized {
            all!(left.inputs(), right.inputs(), self.eq_ty) && self.eq_ty(left.bindings[0].ty(), right.bindings[0].ty())
        } else {
            false
        }
    }

    pub fn eq_path_segment(&mut self, left: &PathSegment<'_>, right: &PathSegment<'_>) -> bool {
        // The == of idents doesn't work with different contexts,
        // we have to be explicit about hygiene
        left.ident.name == right.ident.name && all!(left.args, right.args, self.eq_path_parameters)
    }

    fn eq_ty(&mut self, left: &Ty<'_>, right: &Ty<'_>) -> bool {
        self.eq_ty_kind(&left.kind, &right.kind)
    }

    #[allow(clippy::similar_names)]
    fn eq_ty_kind(&mut self, left: &TyKind<'_>, right: &TyKind<'_>) -> bool {
        match (left, right) {
            (&TyKind::Slice(l_vec), &TyKind::Slice(r_vec)) => self.eq_ty(l_vec, r_vec),
            (&TyKind::Array(lt, ll_id), &TyKind::Array(rt, rl_id)) => {
                let cx = self.inner.cx;
                let eval_const =
                    |body| constant_context(cx, cx.tcx.typeck_body(body)).expr(&cx.tcx.hir().body(body).value);
                self.eq_ty(lt, rt) && eval_const(ll_id.body) == eval_const(rl_id.body)
            },
            (TyKind::Ptr(l_mut), TyKind::Ptr(r_mut)) => l_mut.mutbl == r_mut.mutbl && self.eq_ty(l_mut.ty, r_mut.ty),
            (TyKind::Rptr(_, l_rmut), TyKind::Rptr(_, r_rmut)) => {
                l_rmut.mutbl == r_rmut.mutbl && self.eq_ty(l_rmut.ty, r_rmut.ty)
            },
            (TyKind::Path(l), TyKind::Path(r)) => self.eq_qpath(l, r),
            (&TyKind::Tup(l), &TyKind::Tup(r)) => all!(l, r, self.eq_ty),
            (&TyKind::Infer, &TyKind::Infer) => true,
            _ => false,
        }
    }

    fn eq_type_binding(&mut self, left: &TypeBinding<'_>, right: &TypeBinding<'_>) -> bool {
        left.ident.name == right.ident.name && self.eq_ty(left.ty(), right.ty())
    }
}

/// Some simple reductions like `{ return }` => `return`
fn reduce_exprkind<'hir>(kind: &'hir ExprKind<'hir>) -> &ExprKind<'hir> {
    if let ExprKind::Block(block, _) = kind {
        match (block.stmts, block.expr) {
            // `{}` => `()`
            ([], None) => &ExprKind::Tup(&[]),
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

pub fn all_eq_with<I, T, F>(a: I, b: I, eq_fn: F) -> bool
where
    I: IntoIterator,
    I::IntoIter: ExactSizeIterator<Item = T>,
    F: FnMut(T, T) -> bool,
{
    fn inner<I, T, F>(mut a: I, mut b: I, mut eq_fn: F) -> bool
    where
        I: ExactSizeIterator<Item = T>,
        F: FnMut(T, T) -> bool,
    {
        if a.len() != b.len() {
            return false;
        }
        loop {
            match (a.next(), b.next()) {
                (Some(a), Some(b)) => {
                    if !eq_fn(a, b) {
                        break false;
                    }
                },
                (None, None) => break true,
                _ => break false,
            }
        }
    }
    inner(a.into_iter(), b.into_iter(), eq_fn)
}

pub fn all_eq_by<I, F, T, U>(a: I, b: I, mut key_fn: F) -> bool
where
    I: IntoIterator,
    I::IntoIter: ExactSizeIterator<Item = T>,
    F: FnMut(T) -> U,
    U: PartialEq,
{
    all_eq_with(a, b, |a, b| key_fn(a) == key_fn(b))
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

/// Checks if two expressions evaluate to the same value, and don't contain any side effects.
pub fn eq_expr_value(cx: &LateContext<'_>, left: &Expr<'_>, right: &Expr<'_>) -> bool {
    SpanlessEq::new(cx).deny_side_effects().eq_expr(left, right)
}

/// Type used to hash an ast element. This is different from the `Hash` trait
/// on ast types as this
/// trait would consider IDs and spans.
///
/// All expressions kind are hashed, but some might have a weaker hash.
pub struct SpanlessHash<'a, 'tcx> {
    /// Context used to evaluate constant expressions.
    cx: &'a LateContext<'tcx>,
    maybe_typeck_results: Option<&'tcx TypeckResults<'tcx>>,
    s: StableHasher,
}

impl<'a, 'tcx> SpanlessHash<'a, 'tcx> {
    pub fn new(cx: &'a LateContext<'tcx>) -> Self {
        Self {
            cx,
            maybe_typeck_results: cx.maybe_typeck_results(),
            s: StableHasher::new(),
        }
    }

    pub fn finish(self) -> u64 {
        self.s.finish()
    }

    pub fn hash_block(&mut self, b: &Block<'_>) {
        for s in b.stmts {
            self.hash_stmt(s);
        }

        if let Some(ref e) = b.expr {
            self.hash_expr(e);
        }

        match b.rules {
            BlockCheckMode::DefaultBlock => 0,
            BlockCheckMode::UnsafeBlock(_) => 1,
            BlockCheckMode::PushUnsafeBlock(_) => 2,
            BlockCheckMode::PopUnsafeBlock(_) => 3,
        }
        .hash(&mut self.s);
    }

    #[allow(clippy::many_single_char_names, clippy::too_many_lines)]
    pub fn hash_expr(&mut self, e: &Expr<'_>) {
        let simple_const = self
            .maybe_typeck_results
            .and_then(|typeck_results| constant_simple(self.cx, typeck_results, e));

        // const hashing may result in the same hash as some unrelated node, so add a sort of
        // discriminant depending on which path we're choosing next
        simple_const.is_some().hash(&mut self.s);

        if let Some(e) = simple_const {
            return e.hash(&mut self.s);
        }

        std::mem::discriminant(&e.kind).hash(&mut self.s);

        match e.kind {
            ExprKind::AddrOf(kind, m, ref e) => {
                match kind {
                    BorrowKind::Ref => 0,
                    BorrowKind::Raw => 1,
                }
                .hash(&mut self.s);
                m.hash(&mut self.s);
                self.hash_expr(e);
            },
            ExprKind::Continue(i) => {
                if let Some(i) = i.label {
                    self.hash_name(i.ident.name);
                }
            },
            ExprKind::Assign(ref l, ref r, _) => {
                self.hash_expr(l);
                self.hash_expr(r);
            },
            ExprKind::AssignOp(ref o, ref l, ref r) => {
                o.node
                    .hash_stable(&mut self.cx.tcx.get_stable_hashing_context(), &mut self.s);
                self.hash_expr(l);
                self.hash_expr(r);
            },
            ExprKind::Block(ref b, _) => {
                self.hash_block(b);
            },
            ExprKind::Binary(op, ref l, ref r) => {
                op.node
                    .hash_stable(&mut self.cx.tcx.get_stable_hashing_context(), &mut self.s);
                self.hash_expr(l);
                self.hash_expr(r);
            },
            ExprKind::Break(i, ref j) => {
                if let Some(i) = i.label {
                    self.hash_name(i.ident.name);
                }
                if let Some(ref j) = *j {
                    self.hash_expr(&*j);
                }
            },
            ExprKind::Box(ref e) | ExprKind::DropTemps(ref e) | ExprKind::Yield(ref e, _) => {
                self.hash_expr(e);
            },
            ExprKind::Call(ref fun, args) => {
                self.hash_expr(fun);
                self.hash_exprs(args);
            },
            ExprKind::Cast(ref e, ref ty) | ExprKind::Type(ref e, ref ty) => {
                self.hash_expr(e);
                self.hash_ty(ty);
            },
            ExprKind::Closure(cap, _, eid, _, _) => {
                match cap {
                    CaptureBy::Value => 0,
                    CaptureBy::Ref => 1,
                }
                .hash(&mut self.s);
                // closures inherit TypeckResults
                self.hash_expr(&self.cx.tcx.hir().body(eid).value);
            },
            ExprKind::Field(ref e, ref f) => {
                self.hash_expr(e);
                self.hash_name(f.name);
            },
            ExprKind::Index(ref a, ref i) => {
                self.hash_expr(a);
                self.hash_expr(i);
            },
            ExprKind::InlineAsm(ref asm) => {
                for piece in asm.template {
                    match piece {
                        InlineAsmTemplatePiece::String(s) => s.hash(&mut self.s),
                        InlineAsmTemplatePiece::Placeholder {
                            operand_idx,
                            modifier,
                            span: _,
                        } => {
                            operand_idx.hash(&mut self.s);
                            modifier.hash(&mut self.s);
                        },
                    }
                }
                asm.options.hash(&mut self.s);
                for (op, _op_sp) in asm.operands {
                    match op {
                        InlineAsmOperand::In { reg, expr } => {
                            reg.hash(&mut self.s);
                            self.hash_expr(expr);
                        },
                        InlineAsmOperand::Out { reg, late, expr } => {
                            reg.hash(&mut self.s);
                            late.hash(&mut self.s);
                            if let Some(expr) = expr {
                                self.hash_expr(expr);
                            }
                        },
                        InlineAsmOperand::InOut { reg, late, expr } => {
                            reg.hash(&mut self.s);
                            late.hash(&mut self.s);
                            self.hash_expr(expr);
                        },
                        InlineAsmOperand::SplitInOut {
                            reg,
                            late,
                            in_expr,
                            out_expr,
                        } => {
                            reg.hash(&mut self.s);
                            late.hash(&mut self.s);
                            self.hash_expr(in_expr);
                            if let Some(out_expr) = out_expr {
                                self.hash_expr(out_expr);
                            }
                        },
                        InlineAsmOperand::Const { expr } | InlineAsmOperand::Sym { expr } => self.hash_expr(expr),
                    }
                }
            },
            ExprKind::LlvmInlineAsm(..) | ExprKind::Err => {},
            ExprKind::Lit(ref l) => {
                l.node.hash(&mut self.s);
            },
            ExprKind::Loop(ref b, ref i, ..) => {
                self.hash_block(b);
                if let Some(i) = *i {
                    self.hash_name(i.ident.name);
                }
            },
            ExprKind::If(ref cond, ref then, ref else_opt) => {
                let c: fn(_, _, _) -> _ = ExprKind::If;
                c.hash(&mut self.s);
                self.hash_expr(cond);
                self.hash_expr(&**then);
                if let Some(ref e) = *else_opt {
                    self.hash_expr(e);
                }
            },
            ExprKind::Match(ref e, arms, ref s) => {
                self.hash_expr(e);

                for arm in arms {
                    // TODO: arm.pat?
                    if let Some(ref e) = arm.guard {
                        self.hash_guard(e);
                    }
                    self.hash_expr(&arm.body);
                }

                s.hash(&mut self.s);
            },
            ExprKind::MethodCall(ref path, ref _tys, args, ref _fn_span) => {
                self.hash_name(path.ident.name);
                self.hash_exprs(args);
            },
            ExprKind::ConstBlock(ref l_id) => {
                self.hash_body(l_id.body);
            },
            ExprKind::Repeat(ref e, ref l_id) => {
                self.hash_expr(e);
                self.hash_body(l_id.body);
            },
            ExprKind::Ret(ref e) => {
                if let Some(ref e) = *e {
                    self.hash_expr(e);
                }
            },
            ExprKind::Path(ref qpath) => {
                self.hash_qpath(qpath);
            },
            ExprKind::Struct(ref path, fields, ref expr) => {
                self.hash_qpath(path);

                for f in fields {
                    self.hash_name(f.ident.name);
                    self.hash_expr(&f.expr);
                }

                if let Some(ref e) = *expr {
                    self.hash_expr(e);
                }
            },
            ExprKind::Tup(tup) => {
                self.hash_exprs(tup);
            },
            ExprKind::Array(v) => {
                self.hash_exprs(v);
            },
            ExprKind::Unary(lop, ref le) => {
                lop.hash_stable(&mut self.cx.tcx.get_stable_hashing_context(), &mut self.s);
                self.hash_expr(le);
            },
        }
    }

    pub fn hash_exprs(&mut self, e: &[Expr<'_>]) {
        for e in e {
            self.hash_expr(e);
        }
    }

    pub fn hash_name(&mut self, n: Symbol) {
        n.as_str().hash(&mut self.s);
    }

    pub fn hash_qpath(&mut self, p: &QPath<'_>) {
        match *p {
            QPath::Resolved(_, ref path) => {
                self.hash_path(path);
            },
            QPath::TypeRelative(_, ref path) => {
                self.hash_name(path.ident.name);
            },
            QPath::LangItem(lang_item, ..) => {
                lang_item.hash_stable(&mut self.cx.tcx.get_stable_hashing_context(), &mut self.s);
            },
        }
        // self.maybe_typeck_results.unwrap().qpath_res(p, id).hash(&mut self.s);
    }

    pub fn hash_path(&mut self, path: &Path<'_>) {
        match path.res {
            // constant hash since equality is dependant on inter-expression context
            Res::Local(_) => 1_usize.hash(&mut self.s),
            _ => {
                for seg in path.segments {
                    self.hash_name(seg.ident.name);
                }
            },
        }
    }

    pub fn hash_stmt(&mut self, b: &Stmt<'_>) {
        std::mem::discriminant(&b.kind).hash(&mut self.s);

        match &b.kind {
            StmtKind::Local(local) => {
                if let Some(ref init) = local.init {
                    self.hash_expr(init);
                }
            },
            StmtKind::Item(..) => {},
            StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
                self.hash_expr(expr);
            },
        }
    }

    pub fn hash_guard(&mut self, g: &Guard<'_>) {
        match g {
            Guard::If(ref expr) | Guard::IfLet(_, ref expr) => {
                self.hash_expr(expr);
            },
        }
    }

    pub fn hash_lifetime(&mut self, lifetime: &Lifetime) {
        std::mem::discriminant(&lifetime.name).hash(&mut self.s);
        if let LifetimeName::Param(ref name) = lifetime.name {
            std::mem::discriminant(name).hash(&mut self.s);
            match name {
                ParamName::Plain(ref ident) => {
                    ident.name.hash(&mut self.s);
                },
                ParamName::Fresh(ref size) => {
                    size.hash(&mut self.s);
                },
                ParamName::Error => {},
            }
        }
    }

    pub fn hash_ty(&mut self, ty: &Ty<'_>) {
        self.hash_tykind(&ty.kind);
    }

    pub fn hash_tykind(&mut self, ty: &TyKind<'_>) {
        std::mem::discriminant(ty).hash(&mut self.s);
        match ty {
            TyKind::Slice(ty) => {
                self.hash_ty(ty);
            },
            TyKind::Array(ty, anon_const) => {
                self.hash_ty(ty);
                self.hash_body(anon_const.body);
            },
            TyKind::Ptr(mut_ty) => {
                self.hash_ty(&mut_ty.ty);
                mut_ty.mutbl.hash(&mut self.s);
            },
            TyKind::Rptr(lifetime, mut_ty) => {
                self.hash_lifetime(lifetime);
                self.hash_ty(&mut_ty.ty);
                mut_ty.mutbl.hash(&mut self.s);
            },
            TyKind::BareFn(bfn) => {
                bfn.unsafety.hash(&mut self.s);
                bfn.abi.hash(&mut self.s);
                for arg in bfn.decl.inputs {
                    self.hash_ty(&arg);
                }
                match bfn.decl.output {
                    FnRetTy::DefaultReturn(_) => {
                        ().hash(&mut self.s);
                    },
                    FnRetTy::Return(ref ty) => {
                        self.hash_ty(ty);
                    },
                }
                bfn.decl.c_variadic.hash(&mut self.s);
            },
            TyKind::Tup(ty_list) => {
                for ty in *ty_list {
                    self.hash_ty(ty);
                }
            },
            TyKind::Path(qpath) => match qpath {
                QPath::Resolved(ref maybe_ty, ref path) => {
                    if let Some(ref ty) = maybe_ty {
                        self.hash_ty(ty);
                    }
                    for segment in path.segments {
                        segment.ident.name.hash(&mut self.s);
                        self.hash_generic_args(segment.args().args);
                    }
                },
                QPath::TypeRelative(ref ty, ref segment) => {
                    self.hash_ty(ty);
                    segment.ident.name.hash(&mut self.s);
                },
                QPath::LangItem(lang_item, ..) => {
                    lang_item.hash(&mut self.s);
                },
            },
            TyKind::OpaqueDef(_, arg_list) => {
                self.hash_generic_args(arg_list);
            },
            TyKind::TraitObject(_, lifetime) => {
                self.hash_lifetime(lifetime);
            },
            TyKind::Typeof(anon_const) => {
                self.hash_body(anon_const.body);
            },
            TyKind::Err | TyKind::Infer | TyKind::Never => {},
        }
    }

    pub fn hash_body(&mut self, body_id: BodyId) {
        // swap out TypeckResults when hashing a body
        let old_maybe_typeck_results = self.maybe_typeck_results.replace(self.cx.tcx.typeck_body(body_id));
        self.hash_expr(&self.cx.tcx.hir().body(body_id).value);
        self.maybe_typeck_results = old_maybe_typeck_results;
    }

    fn hash_generic_args(&mut self, arg_list: &[GenericArg<'_>]) {
        for arg in arg_list {
            match arg {
                GenericArg::Lifetime(ref l) => self.hash_lifetime(l),
                GenericArg::Type(ref ty) => self.hash_ty(&ty),
                GenericArg::Const(ref ca) => self.hash_body(ca.value.body),
            }
        }
    }
}
