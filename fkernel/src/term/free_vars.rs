//! Tests whether terms have free variables or are closed.

use fexpr::{basic::DeBruijnIndex, expr::*};
use upcast::Upcast;

#[salsa::query_group(FreeVarsStorage)]
pub trait FreeVars: TermIntern + Upcast<dyn TermIntern> {
    /// All de Bruijn indices used by this term are less than the return value.
    /// For instance, if the term is `#0`, we return `#1`.
    /// If the term is `let x = _ in #0`, we return `#0`, because the inner `#0` refers to `x`.
    /// If the term is `let x = _ in #1`, we return `#0`, because the `#1` inside the `let` body
    /// refers to what we would call `#0` from outside the term.
    fn first_free_variable_index(&self, t: Term) -> DeBruijnIndex;

    /// An term is called *closed* if it contains no free variables.
    /// In our context, an term is closed if all de Bruijn indices refer inside the term.
    /// This doesn't track metavariables, and after a substitution, it's possible that closed terms
    /// now contain free variables.
    /// The opposite of [`has_free_variables`].
    fn closed(&self, t: Term) -> bool;

    /// An term has *free variables* if there are any de Bruijn indices pointing outside the term.
    /// The opposite of [`closed`].
    fn has_free_variables(&self, t: Term) -> bool;
}

fn first_free_variable_index(db: &dyn FreeVars, t: Term) -> DeBruijnIndex {
    match t.lookup(db.up()) {
        ExpressionT::Bound(Bound { index }) => index.succ(),
        ExpressionT::Inst(_) => DeBruijnIndex::zero(),
        ExpressionT::Let(let_expr) => std::cmp::max(
            db.first_free_variable_index(let_expr.to_assign_ty),
            db.first_free_variable_index(let_expr.body).pred(),
        ),
        ExpressionT::Borrow(Borrow { region, value }) => {
            std::cmp::max(region.succ(), db.first_free_variable_index(value))
        }
        ExpressionT::Lambda(binder) | ExpressionT::Pi(binder) => std::cmp::max(
            db.first_free_variable_index(binder.region),
            std::cmp::max(
                db.first_free_variable_index(binder.parameter_ty),
                db.first_free_variable_index(binder.result).pred(),
            ),
        ),
        ExpressionT::RegionLambda(reg) | ExpressionT::RegionPi(reg) => {
            db.first_free_variable_index(reg.body)
        }
        ExpressionT::LetRegion(reg) => db.first_free_variable_index(reg.body),
        ExpressionT::Delta(delta) => std::cmp::max(
            db.first_free_variable_index(delta.region),
            db.first_free_variable_index(delta.ty),
        ),
        ExpressionT::Apply(apply) => std::cmp::max(
            db.first_free_variable_index(apply.function),
            db.first_free_variable_index(apply.argument),
        ),
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
fn closed(db: &dyn FreeVars, t: Term) -> bool {
    db.first_free_variable_index(t) == DeBruijnIndex::zero()
}

/// An term has *free variables* if there are any de Bruijn indices pointing outside the term.
/// The opposite of [`closed`].
fn has_free_variables(db: &dyn FreeVars, t: Term) -> bool {
    !db.closed(t)
}
