//! Converts expressions to weak head normal form.
//!
//! Conversion rules: <https://coq.inria.fr/refman/language/core/conversion.html>

use std::cmp::Ordering;

use fexpr::{
    basic::{DeBruijnIndex, DeBruijnOffset},
    expr::{
        Apply, Binder, BinderAnnotation, BinderStructure, BoundVariable, ExpressionT, Fix, Local,
        Match, Term,
    },
    multiplicity::{InvocationType, ParameterOwnership},
};

use crate::{
    term::{instantiate, lift_free_vars, replace_in_term, ReplaceResult},
    Db,
};

use super::{infer_type, unfold::unfold_definition};

/// Reduces an expression to weak head normal form.
#[salsa::tracked]
pub fn to_weak_head_normal_form(db: &dyn Db, t: Term) -> Term {
    // This variable is rebound mutably locally instead of just writing `mut t: Term` in the function definition
    // so that `#[salsa::tracked]` doesn't annoy clippy.
    let mut t = t;
    loop {
        t = whnf_core(db, t);
        match unfold_definition(db, t) {
            Some(new) => t = new,
            None => break,
        }
    }
    t
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
            if let ExpressionT::Lambda(lam) = function.value(db) {
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
        ExpressionT::Match(match_expr) => {
            // Try to reduce the major premise to weak head normal form first.
            let major_premise = to_weak_head_normal_form(db, match_expr.major_premise);
            if let ExpressionT::Intro(intro) = major_premise.value(db) {
                // We can unfold this match expression.
                // Since the match expression is type correct, the unwrap is ok.
                // This is called match-reduction.
                let premise = match_expr
                    .minor_premises
                    .iter()
                    .find(|premise| *premise.variant == *intro.variant)
                    .unwrap();
                whnf_core(
                    db,
                    intro
                        .parameters
                        .iter()
                        .rev()
                        .take(premise.fields as usize)
                        .fold(premise.result, |t, sub| instantiate(db, t, *sub)),
                )
            } else {
                Term::new(
                    db,
                    ExpressionT::Match(Match {
                        major_premise,
                        ..match_expr.clone()
                    }),
                )
            }
        }
        ExpressionT::Fix(fix) => {
            // Replace this expression with the body of the fixed point construction, where
            // any instances of the fixed point function are replaced with the original term
            // (with de Bruijn indices appropriately lifted).
            let replacement =
                replace_in_term(db, instantiate(db, fix.body, fix.argument), |t, offset| {
                    match t.value(db) {
                        ExpressionT::Local(Local { index }) => {
                            match index.cmp(&(DeBruijnIndex::zero() + offset)) {
                                Ordering::Less => ReplaceResult::Skip,
                                Ordering::Equal => {
                                    // Should have already been handled by the `Apply` case.
                                    // The only way we can invoke the recursive fixed point construction
                                    // is directly, using an `Apply` expression.
                                    unreachable!()
                                }
                                Ordering::Greater => ReplaceResult::ReplaceWith(Term::new(
                                    db,
                                    ExpressionT::Local(Local {
                                        index: index.pred(),
                                    }),
                                )),
                            }
                        }
                        ExpressionT::Apply(ap) => {
                            match ap.function.value(db) {
                                ExpressionT::Local(Local { index }) => {
                                    if *index == DeBruijnIndex::zero() + offset {
                                        // This is a recursive application of the fixed point function.
                                        ReplaceResult::ReplaceWith(Term::new(
                                            db,
                                            ExpressionT::Fix(Fix {
                                                argument: ap.argument,
                                                argument_name: fix.argument_name,
                                                fixpoint: BoundVariable {
                                                    ty: lift_free_vars(
                                                        db,
                                                        fix.fixpoint.ty,
                                                        DeBruijnOffset::zero().succ(),
                                                        offset,
                                                    ),
                                                    ..fix.fixpoint
                                                },
                                                body: lift_free_vars(
                                                    db,
                                                    fix.body,
                                                    DeBruijnOffset::zero().succ().succ(),
                                                    offset,
                                                ),
                                            }),
                                        ))
                                    } else {
                                        ReplaceResult::Skip
                                    }
                                }
                                _ => ReplaceResult::Skip,
                            }
                        }
                        _ => ReplaceResult::Skip,
                    }
                });
            whnf_core(db, replacement)
        }
        _ => t,
    }
}
