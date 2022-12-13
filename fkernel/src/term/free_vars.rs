//! Tests whether terms have free variables or are closed.

use fexpr::{basic::DeBruijnIndex, expr::*};

use crate::Db;

/// All de Bruijn indices used by this term are less than the return value.
/// For instance, if the term is `#0`, we return `#1`.
/// If the term is `let x = _ in #0`, we return `#0`, because the inner `#0` refers to `x`.
/// If the term is `let x = _ in #1`, we return `#0`, because the `#1` inside the `let` body
/// refers to what we would call `#0` from outside the term.
#[must_use]
#[salsa::tracked]
pub fn first_free_variable_index(db: &dyn Db, t: Term) -> DeBruijnIndex {
    match t.value(db) {
        ExpressionT::Local(Local { index })
        | ExpressionT::Borrow(Borrow { index })
        | ExpressionT::LocalRegion(LocalRegion { index }) => index.succ(),
        ExpressionT::Inst(_) => DeBruijnIndex::zero(),
        ExpressionT::Let(let_expr) => std::cmp::max(
            first_free_variable_index(db, let_expr.bound.ty),
            first_free_variable_index(db, let_expr.body).pred(),
        ),
        ExpressionT::Lambda(binder) | ExpressionT::Pi(binder) => std::cmp::max(
            first_free_variable_index(db, binder.structure.region),
            std::cmp::max(
                first_free_variable_index(db, binder.structure.bound.ty),
                first_free_variable_index(db, binder.result).pred(),
            ),
        ),
        ExpressionT::RegionLambda(reg) | ExpressionT::RegionPi(reg) => {
            first_free_variable_index(db, reg.body)
        }
        ExpressionT::Delta(delta) => std::cmp::max(
            first_free_variable_index(db, delta.region),
            first_free_variable_index(db, delta.ty),
        ),
        ExpressionT::Apply(apply) => std::cmp::max(
            first_free_variable_index(db, apply.function),
            first_free_variable_index(db, apply.argument),
        ),
        ExpressionT::Lifespan(lifespan) => first_free_variable_index(db, lifespan.ty),
        ExpressionT::Sort(_) => DeBruijnIndex::zero(),
        ExpressionT::Region | ExpressionT::StaticRegion => DeBruijnIndex::zero(),
        ExpressionT::Metavariable(_) => DeBruijnIndex::zero(),
        ExpressionT::LocalConstant(_) => DeBruijnIndex::zero(),
    }
}

/// An term is called *closed* if it contains no free variables.
/// In our context, an term is closed if all de Bruijn indices refer inside the term.
/// This doesn't track metavariables, and after a substitution, it's possible that closed terms
/// now contain free variables.
/// The opposite of [`has_free_variables`].
#[must_use]
#[salsa::tracked]
pub fn closed(db: &dyn Db, t: Term) -> bool {
    first_free_variable_index(db, t) == DeBruijnIndex::zero()
}

/// An term has *free variables* if there are any de Bruijn indices pointing outside the term.
/// The opposite of [`closed`].
#[must_use]
#[salsa::tracked]
pub fn has_free_variables(db: &dyn Db, t: Term) -> bool {
    !closed(db, t)
}
