use std::cmp::max;

use crate::{
    basic::{DeBruijnIndex, DeBruijnOffset},
    expr::*,
};

impl<'cache> Expression<'cache> {
    /// Returns the largest metavariable index that was referenced in the given term, or [`None`] if none were referenced.
    /// We are free to use metavariables with strictly higher indices than what is returned here without name clashing.
    #[must_use]
    pub fn largest_unusable_metavariable(self, cache: &ExpressionCache<'cache>) -> Option<u32> {
        if let Some(result) = cache.largest_unusable_metavariable.borrow().get(&self) {
            return *result;
        }

        let result = match self.value(cache).clone() {
            ExpressionT::Local(_) => None,
            ExpressionT::Borrow(t) => max(
                t.region.largest_unusable_metavariable(cache),
                t.value.largest_unusable_metavariable(cache),
            ),
            ExpressionT::Dereference(t) => t.value.largest_unusable_metavariable(cache),
            ExpressionT::Delta(t) => max(
                t.region.largest_unusable_metavariable(cache),
                t.ty.largest_unusable_metavariable(cache),
            ),
            ExpressionT::Inst(_) => None,
            ExpressionT::Let(t) => max(
                max(
                    t.bound.ty.largest_unusable_metavariable(cache),
                    t.to_assign.largest_unusable_metavariable(cache),
                ),
                t.body.largest_unusable_metavariable(cache),
            ),
            ExpressionT::Lambda(t) | ExpressionT::Pi(t) => max(
                max(
                    t.structure.bound.ty.largest_unusable_metavariable(cache),
                    t.structure.region.largest_unusable_metavariable(cache),
                ),
                t.result.largest_unusable_metavariable(cache),
            ),
            ExpressionT::RegionLambda(t) | ExpressionT::RegionPi(t) => {
                t.body.largest_unusable_metavariable(cache)
            }
            ExpressionT::Apply(t) => max(
                t.function.largest_unusable_metavariable(cache),
                t.argument.largest_unusable_metavariable(cache),
            ),
            ExpressionT::Intro(t) => t
                .parameters
                .iter()
                .map(|param| param.largest_unusable_metavariable(cache))
                .max()
                .unwrap_or(None),
            ExpressionT::Match(t) => max(
                max(
                    t.minor_premises
                        .into_iter()
                        .map(|premise| premise.result.largest_unusable_metavariable(cache))
                        .max()
                        .unwrap_or(None),
                    t.major_premise.largest_unusable_metavariable(cache),
                ),
                t.motive.largest_unusable_metavariable(cache),
            ),
            ExpressionT::Fix(t) => max(
                max(
                    t.fixpoint.ty.largest_unusable_metavariable(cache),
                    t.body.largest_unusable_metavariable(cache),
                ),
                t.argument.largest_unusable_metavariable(cache),
            ),
            ExpressionT::Sort(_)
            | ExpressionT::Region
            | ExpressionT::RegionT
            | ExpressionT::StaticRegion => None,
            ExpressionT::Lifespan(t) => t.ty.largest_unusable_metavariable(cache),
            ExpressionT::Metavariable(t) => Some(t.index),
            ExpressionT::LocalConstant(t) => Some(t.metavariable.index),
        };
        cache
            .largest_unusable_metavariable
            .borrow_mut()
            .insert(self, result);
        result
    }

    /// All de Bruijn indices used by this term are less than the return value.
    /// For instance, if the term is `#0`, we return `#1`.
    /// If the term is `let x = _ in #0`, we return `#0`, because the inner `#0` refers to `x`.
    /// If the term is `let x = _ in #1`, we return `#0`, because the `#1` inside the `let` body
    /// refers to what we would call `#0` from outside the term.
    #[must_use]
    pub fn first_free_variable_index(self, cache: &ExpressionCache<'cache>) -> DeBruijnIndex {
        if let Some(result) = cache.first_free_variable_index.borrow().get(&self) {
            return *result;
        }

        let result = match self.value(cache).clone() {
            ExpressionT::Local(Local { index }) => index.succ(),
            ExpressionT::Borrow(borrow) => max(
                borrow.region.first_free_variable_index(cache),
                borrow.value.first_free_variable_index(cache),
            ),
            ExpressionT::Dereference(deref) => deref.value.first_free_variable_index(cache),
            ExpressionT::Delta(delta) => max(
                delta.region.first_free_variable_index(cache),
                delta.ty.first_free_variable_index(cache),
            ),
            ExpressionT::Inst(_) => DeBruijnIndex::zero(),
            ExpressionT::Let(let_expr) => max(
                let_expr.bound.ty.first_free_variable_index(cache),
                let_expr.body.first_free_variable_index(cache).pred(),
            ),
            ExpressionT::Lambda(binder) | ExpressionT::Pi(binder) => max(
                binder.structure.region.first_free_variable_index(cache),
                max(
                    binder.structure.bound.ty.first_free_variable_index(cache),
                    binder.result.first_free_variable_index(cache).pred(),
                ),
            ),
            ExpressionT::RegionLambda(reg) | ExpressionT::RegionPi(reg) => {
                reg.body.first_free_variable_index(cache).pred()
            }
            ExpressionT::Apply(apply) => max(
                apply.function.first_free_variable_index(cache),
                apply.argument.first_free_variable_index(cache),
            ),
            ExpressionT::Intro(intro) => intro
                .parameters
                .iter()
                .map(|param| param.first_free_variable_index(cache))
                .max()
                .unwrap_or(DeBruijnIndex::zero()),
            ExpressionT::Match(match_expr) => max(
                max(
                    match_expr.major_premise.first_free_variable_index(cache),
                    match_expr.motive.first_free_variable_index(cache).pred()
                        - DeBruijnOffset::new(match_expr.index_params),
                ),
                match_expr
                    .minor_premises
                    .iter()
                    .map(|premise| {
                        premise.result.first_free_variable_index(cache)
                            - DeBruijnOffset::new(premise.fields)
                    })
                    .max()
                    .unwrap_or(DeBruijnIndex::zero()),
            ),
            ExpressionT::Fix(fix) => max(
                max(
                    fix.argument.first_free_variable_index(cache),
                    fix.fixpoint.ty.first_free_variable_index(cache).pred(),
                ),
                fix.body.first_free_variable_index(cache).pred().pred(),
            ),
            ExpressionT::Sort(_) => DeBruijnIndex::zero(),
            ExpressionT::Region | ExpressionT::RegionT | ExpressionT::StaticRegion => {
                DeBruijnIndex::zero()
            }
            ExpressionT::Lifespan(lifespan) => lifespan.ty.first_free_variable_index(cache),
            ExpressionT::Metavariable(_) => DeBruijnIndex::zero(),
            ExpressionT::LocalConstant(_) => DeBruijnIndex::zero(),
        };
        cache
            .first_free_variable_index
            .borrow_mut()
            .insert(self, result);
        result
    }

    /// An expression is called *closed* if it contains no free variables.
    /// In our context, an expression is closed if all de Bruijn indices refer inside the expression.
    /// This doesn't track metavariables, and after a substitution, it's possible that closed expressions
    /// now contain free variables.
    /// The opposite of [`Expression::has_free_variables`].
    #[must_use]
    pub fn closed(self, cache: &ExpressionCache<'cache>) -> bool {
        self.first_free_variable_index(cache) == DeBruijnIndex::zero()
    }

    /// An expression has *free variables* if there are any de Bruijn indices pointing outside the expression.
    /// The opposite of [`Expression::closed`].
    #[must_use]
    pub fn has_free_variables(self, cache: &ExpressionCache<'cache>) -> bool {
        !self.closed(cache)
    }
}
