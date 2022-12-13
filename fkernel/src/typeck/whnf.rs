//! Converts expressions to weak head normal form.
//!
//! Conversion rules: <https://coq.inria.fr/refman/language/core/conversion.html>

use fexpr::expr::{Apply, ExpressionT, Term};

use crate::{term::instantiate, Db};

use super::unfold::unfold_definition;

/// Reduces an expression to weak head normal form.
#[salsa::tracked]
pub fn to_weak_head_normal_form(db: &dyn Db, t: Term) -> Term {
    // This variable is rebound mutably locally instead of just writing `mut t: Term` in the function definition
    // so that `#[salsa::tracked]` doesn't annoy clippy.
    let mut t = t;
    loop {
        t = whnf_core(db, t);
        // TODO: Normalise `match` expressions.
        match unfold_definition(db, t) {
            Some(new) => t = new,
            None => break t,
        }
    }
}

/// Does not perform delta reduction.
fn whnf_core(db: &dyn Db, t: Term) -> Term {
    match t.value(db) {
        ExpressionT::Let(let_expr) => {
            // We substitute the value into the body of the let expression, then continue to evaluate the expression.
            // This is called zeta-reduction.
            whnf_core(db, instantiate(db, let_expr.body, let_expr.to_assign))
        }
        ExpressionT::Apply(ap) => {
            // Try to reduce the function to weak head normal form first.
            let function = whnf_core(db, ap.function);
            if let ExpressionT::Lambda(lam) = ap.function.value(db) {
                // If the function is a lambda, we can apply a beta-reduction to expand the lambda.
                whnf_core(db, instantiate(db, lam.result, ap.argument))
            } else {
                Term::new(
                    db,
                    ExpressionT::Apply(Apply {
                        function,
                        argument: ap.argument,
                    }),
                )
            }
        }
        _ => t,
    }
}
