use std::cmp::Ordering;

use fexpr::{basic::DeBruijnIndex, expr::*, universe::Universe};

use crate::{term::instantiate, universe::normalise_universe, Db};

use super::{
    infer::infer_type_core,
    unfold::{head_definition_height, unfold_definition},
    whnf::to_weak_head_normal_form,
    Ir,
};

/// Returns true if the two expressions are definitionally equal.
/// This may return an error if the expressions were not type correct.
///
/// TODO: This doesn't work with [`RegionBinder`] or [`Lifespan`] expressions yet.
/// We also don't yet check all the parameters of binder structure.
pub fn definitionally_equal(db: &dyn Db, mut left: Term, mut right: Term) -> Ir<bool> {
    // Start by reducing to weak head normal form.
    left = to_weak_head_normal_form(db, left);
    right = to_weak_head_normal_form(db, right);

    // Since terms are interned, we can very quickly check if they're syntactically identical.
    // This easily deals with all of the singleton variants, e.g. [`ExpressionT::Region`].
    if left == right {
        return Ok(true);
    }

    // Test for simple cases first.
    if let Some(result) = quick_definitionally_equal(db, left, right) {
        return result;
    }

    // Test for equality based on proof irrelevance.
    if equal_propositions(db, left, right)? {
        return Ok(true);
    }

    // Test for equality by performing delta reduction on `left` and `right`.
    // After invoking this, `left` and `right` should be in weak head normal form.
    if let Some(result) = lazy_delta_reduction(db, &mut left, &mut right) {
        return result;
    }

    // Now test all the other cases.
    match (left.value(db), right.value(db)) {
        (ExpressionT::Inst(left), ExpressionT::Inst(right)) => {
            // Test if the two expressions are equal constants.
            if left.name.eq_ignoring_provenance(&right.name)
                && left.universes.len() == right.universes.len()
                && left.universes.iter().zip(&right.universes).all(
                    |(left_universe, right_universe)| {
                        universe_definitionally_equal(db, left_universe, right_universe)
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
            if definitionally_equal(db, left.function, right.function)?
                && definitionally_equal(db, left.argument, right.argument)?
            {
                return Ok(true);
            }
        }
        (ExpressionT::Lambda(lambda), _) => {
            if !matches!(right.value(db), ExpressionT::Lambda(_)) {
                // Test if the we can eta-expand the right expression into the form of the left lambda.
                if let Some(result) = try_eta_expansion(db, lambda, right) {
                    return result;
                }
            }
        }
        (_, ExpressionT::Lambda(lambda)) => {
            if !matches!(left.value(db), ExpressionT::Lambda(_)) {
                // Test if the we can eta-expand the left expression into the form of the right lambda.
                if let Some(result) = try_eta_expansion(db, lambda, left) {
                    return result;
                }
            }
        }
        _ => {}
    }

    // All strategies to prove definitional equality failed.
    Ok(false)
}

/// Tries some fast simplifications to test for definitional equality.
/// If this function returns a value, this is the answer to whether `left` and `right` are definitionally
/// equal. If this function doesn't return anything, we could not tell whether they were equal.
///
/// In particular, this function will return a value when both parameters are lambda, pi, or sort expressions.
fn quick_definitionally_equal(db: &dyn Db, left: Term, right: Term) -> Option<Ir<bool>> {
    match (left.value(db), right.value(db)) {
        (ExpressionT::Borrow(left), ExpressionT::Borrow(right)) => {
            Some(borrow_definitionally_equal(db, left, right))
        }
        (ExpressionT::Lambda(left), ExpressionT::Lambda(right)) => {
            Some(binder_definitionally_equal(db, left, right))
        }
        (ExpressionT::Pi(left), ExpressionT::Pi(right)) => {
            Some(binder_definitionally_equal(db, left, right))
        }
        (ExpressionT::Delta(left), ExpressionT::Delta(right)) => {
            Some(delta_definitionally_equal(db, left, right))
        }
        (ExpressionT::Sort(left), ExpressionT::Sort(right)) => {
            Some(Ok(universe_definitionally_equal(db, &left.0, &right.0)))
        }
        _ => None,
    }
}

/// Borrows are definitionally equal if their values and regions are equal.
fn borrow_definitionally_equal(db: &dyn Db, left: &Borrow<Term>, right: &Borrow<Term>) -> Ir<bool> {
    Ok(definitionally_equal(db, left.region, right.region)?
        && definitionally_equal(db, left.value, right.value)?)
}

/// Lambda and pi expressions are definitionally equal if their parameter types are equal and their bodies are equal.
fn binder_definitionally_equal(
    db: &dyn Db,
    left: &Binder<(), Term>,
    right: &Binder<(), Term>,
) -> Ir<bool> {
    if !definitionally_equal(db, left.structure.bound.ty, right.structure.bound.ty)? {
        return Ok(false);
    }

    // The parameter types are the same.
    // Now, substitute the parameter types in the body, and check if they are the same.
    let local = Term::new(
        db,
        ExpressionT::LocalConstant(left.structure.generate_local_with_gen(
            &mut MetavariableGenerator::new(std::cmp::max(
                largest_unusable_metavariable(db, left.result),
                largest_unusable_metavariable(db, right.result),
            )),
        )),
    );
    let left_body = instantiate(db, left.result, local);
    let right_body = instantiate(db, right.result, local);
    definitionally_equal(db, left_body, right_body)
}

/// Delta types are definitionally equal if their types and regions are definitionally equal.
fn delta_definitionally_equal(db: &dyn Db, left: &Delta<Term>, right: &Delta<Term>) -> Ir<bool> {
    Ok(definitionally_equal(db, left.region, right.region)?
        && definitionally_equal(db, left.ty, right.ty)?)
}

fn universe_definitionally_equal(db: &dyn Db, left: &Universe<()>, right: &Universe<()>) -> bool {
    normalise_universe(db, left.clone()) == normalise_universe(db, right.clone())
}

/// Returns true if `left` and `right` are proofs of the same proposition.
/// Any two proofs of the same proposition are equal by definition; this property of our type system is called proof irrelevance.
fn equal_propositions(db: &dyn Db, left: Term, right: Term) -> Ir<bool> {
    // If the type of `left_type` is `Prop` (that is, universe zero), then proof irrelevance applies.
    let left_type = infer_type_core(db, left)?;
    if to_weak_head_normal_form(db, infer_type_core(db, left_type)?) == Term::sort_prop(db) {
        let right_type = infer_type_core(db, right)?;
        definitionally_equal(db, left_type, right_type)
    } else {
        Ok(false)
    }
}

/// Perform delta reduction at the heads of the input expressions
/// to try to check if two expressions are definitionally equal.
/// While executing this check, `left` and `right` will be unfolded, so they are passed mutably.
fn lazy_delta_reduction(db: &dyn Db, left: &mut Term, right: &mut Term) -> Option<Ir<bool>> {
    loop {
        // Check if either the left function or right function can be delta reduced.
        let left_height = head_definition_height(db, *left);
        let right_height = head_definition_height(db, *right);
        if left_height.is_none() && right_height.is_none() {
            // If neither head is a definition, we can't do any delta reduction in this step.
            break None;
        }

        match left_height.cmp(&right_height) {
            Ordering::Less => {
                // The right height was higher, so unfold that expression first.
                *right = to_weak_head_normal_form(db, unfold_definition(db, *right).unwrap());
            }
            Ordering::Greater => {
                // Conversely, in this case, the left height was heigher.
                *left = to_weak_head_normal_form(db, unfold_definition(db, *left).unwrap());
            }
            Ordering::Equal => {
                // Both had the same height (and are reducible).
                // Since we can't prioritise one over the other, we will just unfold both definitions.
                // TODO: If the definitions to be unfolded match, we can optimise this path by
                // comparing arguments. This would short-circuit the delta reduction. Even if the
                // arguments are not definitionally equal, the function could still return the same
                // value in theory, so we can't always completely bypass the check.
                *right = to_weak_head_normal_form(db, unfold_definition(db, *right).unwrap());
                *left = to_weak_head_normal_form(db, unfold_definition(db, *left).unwrap());
            }
        }

        // Now that we've done some delta reduction, check if the resulting terms match.
        match quick_definitionally_equal(db, *left, *right) {
            Some(result) => break Some(result),
            None => continue,
        }
    }
}

/// Tries to check if the lambda and `t` are definitionally equal by eta-expanding `t`.
/// `t` should not be a lambda.
fn try_eta_expansion(db: &dyn Db, lambda: &Binder<(), Term>, t: Term) -> Option<Ir<bool>> {
    let t_type = match infer_type_core(db, t) {
        Ok(value) => to_weak_head_normal_form(db, value),
        Err(err) => return Some(Err(err)),
    };

    if let ExpressionT::Pi(_) = t_type.value(db) {
        let new_expr = Term::new(
            db,
            ExpressionT::Lambda(Binder {
                structure: lambda.structure,
                result: Term::new(
                    db,
                    ExpressionT::Apply(Apply {
                        function: t,
                        argument: Term::new(
                            db,
                            ExpressionT::Local(Local {
                                index: DeBruijnIndex::zero(),
                            }),
                        ),
                    }),
                ),
            }),
        );
        Some(definitionally_equal(
            db,
            Term::new(db, ExpressionT::Lambda(*lambda)),
            new_expr,
        ))
    } else {
        None
    }
}
