use std::cmp::Ordering;

use crate::{
    basic::{DeBruijnIndex, Provenance},
    expr::*,
    universe::Universe,
};

use super::{infer::infer_type_core, Ir};

impl<'cache> Expression<'cache> {
    /// Returns true if the two expressions are definitionally equal.
    /// This may return an error if the expressions were not type correct.
    ///
    /// TODO: This doesn't work with [`RegionBinder`] or [`Lifespan`] expressions yet.
    /// We also don't yet check all the parameters of binder structure.
    pub fn definitionally_equal(
        cache: &ExpressionCache<'cache>,
        mut left: Self,
        mut right: Self,
    ) -> Ir<bool> {
        // Start by reducing to weak head normal form.
        left = left.to_weak_head_normal_form(cache);
        right = right.to_weak_head_normal_form(cache);

        // Since terms are interned, we can very quickly check if they're syntactically identical.
        // This easily deals with all of the singleton variants, e.g. [`ExpressionT::Region`].
        if left == right {
            return Ok(true);
        }

        // Test for simple cases first.
        if let Some(result) = quick_definitionally_equal(cache, left, right) {
            return result;
        }

        // Test for equality based on proof irrelevance.
        if equal_propositions(cache, left, right)? {
            return Ok(true);
        }

        // Test for equality by performing delta reduction on `left` and `right`.
        // After invoking this, `left` and `right` should be in weak head normal form.
        if let Some(result) = lazy_delta_reduction(cache, &mut left, &mut right) {
            return result;
        }

        // Now test all the other cases.
        match (left.value(cache), right.value(cache)) {
            (ExpressionT::Inst(left), ExpressionT::Inst(right)) => {
                // Test if the two expressions are equal constants.
                if left.name.eq_ignoring_provenance(&right.name)
                    && left.universes.len() == right.universes.len()
                    && left.universes.iter().zip(&right.universes).all(
                        |(left_universe, right_universe)| {
                            universe_definitionally_equal(cache, left_universe, right_universe)
                        },
                    )
                {
                    return Ok(true);
                }
            }
            (ExpressionT::LocalConstant(left), ExpressionT::LocalConstant(right)) => {
                // Test if the two expressions are equal local constants.
                if left.structure.bound.name == right.structure.bound.name {
                    return Ok(true);
                }
            }
            (ExpressionT::Apply(left), ExpressionT::Apply(right)) => {
                // Test if the two expressions are applications of the same function with the same arguments.
                if Expression::definitionally_equal(cache, left.function, right.function)?
                    && Expression::definitionally_equal(cache, left.argument, right.argument)?
                {
                    return Ok(true);
                }
            }
            (ExpressionT::Intro(left), ExpressionT::Intro(right)) => {
                // Test if the two expressions are instantiations of the same inductive with the same fields.
                return Ok(left.inductive == right.inductive
                    && left
                        .universes
                        .iter()
                        .zip(&right.universes)
                        .all(|(left, right)| universe_definitionally_equal(cache, left, right))
                    && *left.variant == *right.variant
                    && left.parameters.iter().zip(&right.parameters).fold(
                        Ok(true),
                        |acc, (left, right)| {
                            Ok(acc? && Expression::definitionally_equal(cache, *left, *right)?)
                        },
                    )?);
            }
            (ExpressionT::Lambda(lambda), _) => {
                if !matches!(right.value(cache), ExpressionT::Lambda(_)) {
                    // Test if the we can eta-expand the right expression into the form of the left lambda.
                    if let Some(result) = try_eta_expansion(cache, lambda, right) {
                        return result;
                    }
                }
            }
            (_, ExpressionT::Lambda(lambda)) => {
                if !matches!(left.value(cache), ExpressionT::Lambda(_)) {
                    // Test if the we can eta-expand the left expression into the form of the right lambda.
                    if let Some(result) = try_eta_expansion(cache, lambda, left) {
                        return result;
                    }
                }
            }
            _ => {}
        }

        // All strategies to prove definitional equality failed.
        Ok(false)
    }
}

/// Tries some fast simplifications to test for definitional equality.
/// If this function returns a value, this is the answer to whether `left` and `right` are definitionally
/// equal. If this function doesn't return anything, we could not tell whether they were equal.
///
/// In particular, this function will return a value when both parameters are lambda, pi, or sort expressions.
fn quick_definitionally_equal<'cache>(
    cache: &ExpressionCache<'cache>,
    left: Expression<'cache>,
    right: Expression<'cache>,
) -> Option<Ir<bool>> {
    match (left.value(cache), right.value(cache)) {
        (ExpressionT::Borrow(left), ExpressionT::Borrow(right)) => {
            Some(borrow_definitionally_equal(cache, left, right))
        }
        (ExpressionT::Lambda(left), ExpressionT::Lambda(right))
        | (ExpressionT::Pi(left), ExpressionT::Pi(right)) => {
            Some(binder_definitionally_equal(cache, left, right))
        }
        (ExpressionT::Delta(left), ExpressionT::Delta(right)) => {
            Some(delta_definitionally_equal(cache, left, right))
        }
        (ExpressionT::Sort(left), ExpressionT::Sort(right)) => {
            Some(Ok(universe_definitionally_equal(cache, &left.0, &right.0)))
        }
        _ => None,
    }
}

/// Borrows are definitionally equal if their values and regions are equal.
fn borrow_definitionally_equal<'cache>(
    cache: &ExpressionCache<'cache>,
    left: Borrow<Expression<'cache>>,
    right: Borrow<Expression<'cache>>,
) -> Ir<bool> {
    Ok(
        Expression::definitionally_equal(cache, left.region, right.region)?
            && Expression::definitionally_equal(cache, left.value, right.value)?,
    )
}

/// Lambda and pi expressions are definitionally equal if their parameter types are equal and their bodies are equal.
fn binder_definitionally_equal<'cache>(
    cache: &ExpressionCache<'cache>,
    left: Binder<Expression<'cache>>,
    right: Binder<Expression<'cache>>,
) -> Ir<bool> {
    if left.structure.ownership != right.structure.ownership {
        return Ok(false);
    }

    if !Expression::definitionally_equal(cache, left.structure.region, right.structure.region)? {
        return Ok(false);
    }

    if !Expression::definitionally_equal(cache, left.structure.bound.ty, right.structure.bound.ty)?
    {
        return Ok(false);
    }

    // The parameter types are the same.
    // Now, substitute the parameter types in the body, and check if they are the same.
    let local = Expression::new(
        cache,
        Provenance::Synthetic,
        ExpressionT::LocalConstant(left.structure.generate_local_with_gen(
            &mut MetavariableGenerator::new(std::cmp::max(
                left.result.largest_unusable_metavariable(cache),
                right.result.largest_unusable_metavariable(cache),
            )),
        )),
    );
    let left_body = left.result.instantiate(cache, local);
    let right_body = right.result.instantiate(cache, local);
    Expression::definitionally_equal(cache, left_body, right_body)
}

/// Delta types are definitionally equal if their types and regions are definitionally equal.
fn delta_definitionally_equal<'cache>(
    cache: &ExpressionCache<'cache>,
    left: Delta<Expression<'cache>>,
    right: Delta<Expression<'cache>>,
) -> Ir<bool> {
    Ok(
        Expression::definitionally_equal(cache, left.region, right.region)?
            && Expression::definitionally_equal(cache, left.ty, right.ty)?,
    )
}

fn universe_definitionally_equal(
    cache: &ExpressionCache<'_>,
    left: &Universe,
    right: &Universe,
) -> bool {
    left.clone().normalise_universe(cache.db()) == right.clone().normalise_universe(cache.db())
}

/// Returns true if `left` and `right` are proofs of the same proposition.
/// Any two proofs of the same proposition are equal by definition; this property of our type system is called proof irrelevance.
fn equal_propositions<'cache>(
    cache: &ExpressionCache<'cache>,
    left: Expression<'cache>,
    right: Expression<'cache>,
) -> Ir<bool> {
    // If the type of `left_type` is `Prop` (that is, universe zero), then proof irrelevance applies.
    let left_type = infer_type_core(cache, left)?;
    if Expression::definitionally_equal(
        cache,
        infer_type_core(cache, left_type)?,
        Expression::sort_prop(cache),
    )? {
        let right_type = infer_type_core(cache, right)?;
        Expression::definitionally_equal(cache, left_type, right_type)
    } else {
        Ok(false)
    }
}

/// Perform delta reduction at the heads of the input expressions
/// to try to check if two expressions are definitionally equal.
/// While executing this check, `left` and `right` will be unfolded, so they are passed mutably.
fn lazy_delta_reduction<'cache>(
    cache: &ExpressionCache<'cache>,
    left: &mut Expression<'cache>,
    right: &mut Expression<'cache>,
) -> Option<Ir<bool>> {
    loop {
        // Check if either the left function or right function can be delta reduced.
        let left_height = left.head_definition_height(cache);
        let right_height = right.head_definition_height(cache);
        if left_height.is_none() && right_height.is_none() {
            // If neither head is a definition, we can't do any delta reduction in this step.
            break None;
        }

        match left_height.cmp(&right_height) {
            Ordering::Less => {
                // The right height was higher, so unfold that expression first.
                *right = right
                    .unfold_definition(cache)
                    .unwrap()
                    .to_weak_head_normal_form(cache);
            }
            Ordering::Greater => {
                // Conversely, in this case, the left height was heigher.
                *left = left
                    .unfold_definition(cache)
                    .unwrap()
                    .to_weak_head_normal_form(cache);
            }
            Ordering::Equal => {
                // Both had the same height (and are reducible).
                // Since we can't prioritise one over the other, we will just unfold both definitions.
                // First, we can optimise this path by comparing arguments.
                // This would short-circuit the delta reduction. Even if the
                // arguments are not definitionally equal, the function could still return the same
                // value in theory, so we can't always completely bypass the check.
                let left_args = left.apply_args(cache);
                let right_args = right.apply_args(cache);
                if left_args.len() == right_args.len()
                    && left_args
                        .iter()
                        .zip(&right_args)
                        .all(|(l, r)| Expression::definitionally_equal(cache, *l, *r) == Ok(true))
                {
                    return Some(Ok(true));
                }
                // The arguments didn't match, so continue as usual.
                *right = right
                    .unfold_definition(cache)
                    .unwrap()
                    .to_weak_head_normal_form(cache);
                *left = left
                    .unfold_definition(cache)
                    .unwrap()
                    .to_weak_head_normal_form(cache);
            }
        }

        // Now that we've done some delta reduction, check if the resulting terms match.
        match quick_definitionally_equal(cache, *left, *right) {
            Some(result) => break Some(result),
            None => continue,
        }
    }
}

/// Tries to check if the lambda and `t` are definitionally equal by eta-expanding `t`.
/// `t` should not be a lambda.
fn try_eta_expansion<'cache>(
    cache: &ExpressionCache<'cache>,
    lambda: Binder<Expression<'cache>>,
    t: Expression<'cache>,
) -> Option<Ir<bool>> {
    let t_type = match infer_type_core(cache, t) {
        Ok(value) => value.to_weak_head_normal_form(cache),
        Err(err) => return Some(Err(err)),
    };

    if lambda.structure.ownership == FunctionOwnership::Many {
        todo!()
    }

    if let ExpressionT::Pi(_) = t_type.value(cache) {
        let new_expr = Expression::new(
            cache,
            Provenance::Synthetic,
            ExpressionT::Lambda(Binder {
                structure: lambda.structure,
                result: Expression::new(
                    cache,
                    Provenance::Synthetic,
                    ExpressionT::Apply(Apply {
                        function: t,
                        argument: Expression::new(
                            cache,
                            Provenance::Synthetic,
                            ExpressionT::Local(Local {
                                index: DeBruijnIndex::zero(),
                            }),
                        ),
                    }),
                ),
            }),
        );
        Some(Expression::definitionally_equal(
            cache,
            Expression::new(cache, Provenance::Synthetic, ExpressionT::Lambda(lambda)),
            new_expr,
        ))
    } else {
        None
    }
}
