//! Converts expressions to weak head normal form.
//!
//! Conversion rules: <https://coq.inria.fr/refman/language/core/conversion.html>

use std::cmp::Ordering;

use crate::{
    basic::{DeBruijnIndex, DeBruijnOffset},
    expr::*,
};

impl<'cache> Expression<'cache> {
    /// Reduces an expression to weak head normal form.
    pub fn to_weak_head_normal_form(mut self, cache: &mut ExpressionCache<'cache>) -> Self {
        loop {
            self = whnf_core(cache, self);
            match self.unfold_definition(cache) {
                Some(new) => self = new,
                None => break,
            }
        }
        self
    }
}

/// Does not perform delta reduction.
fn whnf_core<'cache>(
    cache: &mut ExpressionCache<'cache>,
    e: Expression<'cache>,
) -> Expression<'cache> {
    match e.value(cache) {
        ExpressionT::Dereference(deref) => {
            // Reduce the argument of the dereference to weak head normal form first.
            let value = deref.value.to_weak_head_normal_form(cache);
            if let ExpressionT::Borrow(borrow) = value.value(cache) {
                whnf_core(cache, borrow.value)
            } else {
                Expression::new(
                    cache,
                    e.provenance(cache),
                    ExpressionT::Dereference(Dereference { value }),
                )
            }
        }
        ExpressionT::Let(let_expr) => {
            // We substitute the value into the body of the let expression, then continue to evaluate the expression.
            // This is called zeta-reduction.
            whnf_core(cache, let_expr.body.instantiate(cache, let_expr.to_assign))
        }
        ExpressionT::Apply(ap) => {
            // Reduce the function to weak head normal form first.
            let function = whnf_core(cache, ap.function);
            if let ExpressionT::Lambda(lam) = function.value(cache) {
                // If the function is a lambda, we can apply a beta-reduction to expand the lambda.
                whnf_core(cache, lam.result.instantiate(cache, ap.argument))
            } else {
                Expression::new(
                    cache,
                    e.provenance(cache),
                    ExpressionT::Apply(Apply {
                        function,
                        argument: ap.argument,
                    }),
                )
            }
        }
        ExpressionT::Match(match_expr) => {
            // Reduce the major premise to weak head normal form first.
            let major_premise = match_expr.major_premise.to_weak_head_normal_form(cache);
            if let ExpressionT::Intro(intro) = major_premise.value(cache) {
                // We can unfold this match expression.
                // Since the match expression is type correct, the unwrap is ok.
                // This is called match-reduction.
                let premise = match_expr
                    .minor_premises
                    .iter()
                    .find(|premise| *premise.variant == *intro.variant)
                    .unwrap();
                whnf_core(
                    cache,
                    intro
                        .parameters
                        .iter()
                        .rev()
                        .take(premise.fields as usize)
                        .fold(premise.result, |e, sub| e.instantiate(cache, *sub)),
                )
            } else if let ExpressionT::Borrow(borrow) = major_premise.value(cache) && let ExpressionT::Intro(intro) = borrow.value.value(cache) {
                // We can unfold this match expression operating on a borrowed value.
                let premise = match_expr
                    .minor_premises
                    .iter()
                    .find(|premise| *premise.variant == *intro.variant)
                    .unwrap();
                whnf_core(
                    cache,
                    intro
                        .parameters
                        .iter()
                        .rev()
                        .take(premise.fields as usize)
                        .fold(premise.result, |e, sub| e.instantiate(cache, Expression::new(cache, sub.provenance(cache), ExpressionT::Borrow(Borrow {
                            region: borrow.region,
                            value: *sub,
                        })))),
                )
            } else {
                Expression::new(
                    cache,
                    e.provenance(cache),
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
            let replacement = fix
                .body
                .instantiate(cache, fix.argument)
                .replace_in_expression(cache, &|e, offset| {
                    match e.value(cache) {
                        ExpressionT::Local(Local { index }) => {
                            match index.cmp(&(DeBruijnIndex::zero() + offset)) {
                                Ordering::Less => ReplaceResult::Skip,
                                Ordering::Equal => {
                                    // Should have already been handled by the `Apply` case.
                                    // The only way we can invoke the recursive fixed point construction
                                    // is directly, using an `Apply` expression.
                                    unreachable!()
                                }
                                Ordering::Greater => ReplaceResult::ReplaceWith(Expression::new(
                                    cache,
                                    e.provenance(cache),
                                    ExpressionT::Local(Local {
                                        index: index.pred(),
                                    }),
                                )),
                            }
                        }
                        ExpressionT::Apply(ap) => {
                            match ap.function.value(cache) {
                                ExpressionT::Local(Local { index }) => {
                                    if *index == DeBruijnIndex::zero() + offset {
                                        // This is a recursive application of the fixed point function.
                                        ReplaceResult::ReplaceWith(Expression::new(
                                            cache,
                                            e.provenance(cache),
                                            ExpressionT::Fix(Fix {
                                                argument: ap.argument,
                                                argument_name: fix.argument_name,
                                                fixpoint: BoundVariable {
                                                    ty: fix.fixpoint.ty.lift_free_vars(
                                                        cache,
                                                        DeBruijnOffset::zero().succ(),
                                                        offset,
                                                    ),
                                                    ..fix.fixpoint
                                                },
                                                body: fix.body.lift_free_vars(
                                                    cache,
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
            whnf_core(cache, replacement)
        }
        _ => e,
    }
}
