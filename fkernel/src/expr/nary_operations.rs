//! Provides utilities for working with n-ary functions, even though
//! function currying makes all functions behave like they are unary.

use crate::{basic::Provenance, expr::*};

impl<'cache> Expression<'cache> {
    /// If this expression is a function application, return the leftmost function in the call chain.
    /// For example, applying this function to `foo 1 2 3` returns `foo`,
    /// and applying it to `(foo bar) 1 2 3` returns `foo bar`.
    /// If this is not a function application, we interpret the expression as a nullary function,
    /// and return the whole expression.
    #[must_use]
    pub fn head(self, cache: &ExpressionCache<'cache>) -> Self {
        if let ExpressionT::Apply(apply) = self.value(cache) {
            apply.function.head(cache)
        } else {
            self
        }
    }

    /// If this is a function application, return the list of arguments applied to the [`head`] of the expression.
    /// Applying this function to `foo 1 2 3` returns `[1, 2, 3]`.
    /// If this is not a function application, return `[]`.
    #[must_use]
    pub fn apply_args(self, cache: &ExpressionCache<'cache>) -> Vec<Self> {
        if let ExpressionT::Apply(apply) = self.value(cache) {
            let mut result = apply.function.apply_args(cache);
            result.push(apply.argument);
            result
        } else {
            Vec::new()
        }
    }

    /// Suppose that this expression is an n-ary function application, where n is zero or a positive integer.
    /// Then, this function returns the [`Expression::head`] of this expression, and the list of
    /// [`Expression::apply_args`] that were applied to it.
    /// Applying this function to `foo 1 2 3` returns `(foo, [1, 2, 3])`.
    #[must_use]
    pub fn destructure_as_nary_application(
        self,
        cache: &ExpressionCache<'cache>,
    ) -> (Self, Vec<Self>) {
        (self.head(cache), self.apply_args(cache))
    }

    /// Returns the arguments, in order, to a [`ExpressionT::Pi`].
    /// Discards the return value.
    #[must_use]
    pub fn pi_args(mut self, cache: &ExpressionCache<'cache>) -> Vec<LocalConstant<Self>> {
        let mut result = Vec::new();
        while let ExpressionT::Pi(pi) = self.value(cache) {
            self = pi.result;
            result.push(cache.gen_local(pi.structure));
        }
        result
    }

    /// Creates an n-ary function application chain from the given function (`self`) and arguments.
    #[must_use]
    pub fn create_nary_application(
        self,
        cache: &ExpressionCache<'cache>,
        arguments: impl Iterator<Item = (Provenance, Self)>,
    ) -> Self {
        arguments.fold(self, |function, (provenance, argument)| {
            Self::new(
                cache,
                provenance,
                ExpressionT::Apply(Apply { function, argument }),
            )
        })
    }

    /// Creates a [`ExpressionT::Lambda`] expression that can be evaluated with the given local constants in `arguments`
    /// to produce the *closed* expression `self`.
    #[must_use]
    pub fn abstract_nary_lambda(
        self,
        cache: &ExpressionCache<'cache>,
        locals: impl DoubleEndedIterator<Item = (Provenance, LocalConstant<Self>)>,
    ) -> Self {
        locals.rev().fold(self, |result, (provenance, local)| {
            Self::new(
                cache,
                provenance,
                ExpressionT::Lambda(result.abstract_binder(cache, local)),
            )
        })
    }

    /// Creates a [`ExpressionT::Pi`] expression that can be evaluated with the given local constants in `arguments`
    /// to produce the *closed* expression `self`.
    #[must_use]
    pub fn abstract_nary_pi(
        self,
        cache: &ExpressionCache<'cache>,
        locals: impl DoubleEndedIterator<Item = (Provenance, LocalConstant<Self>)>,
    ) -> Self {
        locals.rev().fold(self, |result, (provenance, local)| {
            Self::new(
                cache,
                provenance,
                ExpressionT::Pi(result.abstract_binder(cache, local)),
            )
        })
    }

    /// Converts an [`NaryBinder`] into a [`ExpressionT::Lambda`] expression that represents the same binders.
    #[must_use]
    pub fn nary_binder_to_lambda(
        cache: &ExpressionCache<'cache>,
        provenance: Provenance,
        nary_binder: NaryBinder<Self>,
    ) -> Self {
        nary_binder.structures.iter().copied().rev().fold(
            nary_binder.result,
            |result, structure| {
                Expression::new(
                    cache,
                    provenance,
                    ExpressionT::Lambda(Binder { structure, result }),
                )
            },
        )
    }

    /// Converts an [`NaryBinder`] into a [`ExpressionT::Pi`] expression that represents the same binders.
    #[must_use]
    pub fn nary_binder_to_pi(
        cache: &ExpressionCache<'cache>,
        provenance: Provenance,
        nary_binder: NaryBinder<Self>,
    ) -> Self {
        nary_binder.structures.iter().copied().rev().fold(
            nary_binder.result,
            |result, structure| {
                Expression::new(
                    cache,
                    provenance,
                    ExpressionT::Pi(Binder { structure, result }),
                )
            },
        )
    }
}
