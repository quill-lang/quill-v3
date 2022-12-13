//! Provides utilities for working with n-ary functions, even though
//! function currying makes all functions behave like they are unary.

use fexpr::expr::*;

use crate::Db;

use super::abstract_binder;

/// If this term is a function application, return the leftmost function in the call chain.
/// For example, applying this function to `foo 1 2 3` returns `foo`,
/// and applying it to `(foo bar) 1 2 3` returns `foo bar`.
/// If this is not a function application, we interpret the term as a nullary function,
/// and return the whole term.
#[must_use]
pub fn leftmost_function(db: &dyn Db, t: Term) -> Term {
    if let ExpressionT::Apply(apply) = t.value(db) {
        leftmost_function(db, apply.function)
    } else {
        t
    }
}

/// If this is a function application, return the list of arguments applied to the
/// [leftmost function](leftmost_function) of the term.
/// Applying this function to `foo 1 2 3` returns `[1, 2, 3]`.
/// If this is not a function application, return `[]`.
#[must_use]
pub fn apply_args(db: &dyn Db, t: Term) -> Vec<Term> {
    if let ExpressionT::Apply(apply) = t.value(db) {
        let mut result = apply_args(db, apply.function);
        result.push(apply.argument);
        result
    } else {
        Vec::new()
    }
}

/// Returns the arguments, in order, to a [`Pi`].
/// Discards the return value.
#[must_use]
pub fn pi_args(
    db: &dyn Db,
    mut t: Term,
    meta_gen: &mut MetavariableGenerator<Term>,
) -> Vec<LocalConstant<(), Term>> {
    let mut result = Vec::new();
    while let ExpressionT::Pi(pi) = t.value(db) {
        t = pi.result;
        result.push(pi.generate_local_with_gen(meta_gen));
    }
    result
}

/// Suppose that this term is an n-ary function application, where n is zero or a positive integer.
/// Then, this function returns the [`leftmost_function`] of this term, and the list of [`apply_args`]
/// that were applied to it.
/// Applying this function to `foo 1 2 3` returns `(foo, [1, 2, 3])`.
#[must_use]
pub fn destructure_as_nary_application(db: &dyn Db, t: Term) -> (Term, Vec<Term>) {
    (leftmost_function(db, t), apply_args(db, t))
}

/// Creates an n-ary function application chain from the given function and arguments.
#[must_use]
pub fn create_nary_application(
    db: &dyn Db,
    function: Term,
    arguments: impl Iterator<Item = Term>,
) -> Term {
    arguments.fold(function, |function, argument| {
        Term::new(db, ExpressionT::Apply(Apply { function, argument }))
    })
}

/// Creates a [`Lambda`] term that can be evaluated with the given local constants in `arguments`
/// to produce the term `result`.
#[must_use]
pub fn abstract_nary_lambda(
    db: &dyn Db,
    locals: impl DoubleEndedIterator<Item = LocalConstant<(), Term>>,
    result: Term,
) -> Term {
    locals.rev().fold(result, |result, local| {
        Term::new(db, ExpressionT::Lambda(abstract_binder(db, local, result)))
    })
}

/// Creates a [`Pi`] term that can be evaluated with the given local constants in `arguments`
/// to produce the term `result`.
#[must_use]
pub fn abstract_nary_pi(
    db: &dyn Db,
    locals: impl DoubleEndedIterator<Item = LocalConstant<(), Term>>,
    result: Term,
) -> Term {
    locals.rev().fold(result, |result, local| {
        Term::new(db, ExpressionT::Pi(abstract_binder(db, local, result)))
    })
}
