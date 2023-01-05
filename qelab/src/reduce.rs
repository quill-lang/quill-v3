//! Performs various kinds of reduction.

use fkernel::expr::{Expression, ExpressionT};

use crate::elaborator::Elaborator;

impl<'a, 'cache> Elaborator<'a, 'cache> {
    /// Performs simple reductions on the head of the given expression.
    /// In particular, we perform:
    ///
    /// * beta-reduction, converting `(fn a => b a) c` into `b c`;
    /// * TODO: match-reduction, simplifying match expressions where the major premise is an [`ExpressionT::Intro`];
    /// * TODO: borrow-reduction, converting `*&a` into `a`;
    /// * TODO: fix-reduction.
    ///
    /// See also [`Expression::to_weak_head_normal_form`] for a more agressive simplifier.
    pub fn simple_reduce(&self, expr: Expression<'cache>) -> Expression<'cache> {
        match expr.value(self.cache()) {
            ExpressionT::Apply(ap) => {
                // Simplify the head of the expression first.
                let function = self.simple_reduce(ap.function);
                // If the function is a lambda, we can apply a beta-reduction to expand the lambda.
                if let ExpressionT::Lambda(lam) = function.value(self.cache()) {
                    self.simple_reduce(lam.result.instantiate(self.cache(), ap.argument))
                } else {
                    // Don't do anything.
                    expr
                }
            }
            _ => expr,
        }
    }
}
