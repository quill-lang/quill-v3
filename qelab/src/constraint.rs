use fcommon::Span;
use fkernel::{
    basic::Provenance,
    expr::{
        Expression, ExpressionCache, ExpressionT, LocalConstant, Metavariable, StuckExpression,
    },
};

use crate::elaborator::Elaborator;

/// An expression `actual` is required to be definitionall equal to `expected`.
pub struct UnificationConstraint<'cache> {
    pub expected: Expression<'cache>,
    pub actual: Expression<'cache>,
    pub justification: Justification,
}

/// The reason why a particular unification constraint was given.
pub enum Justification {
    Variable,
    Apply,
    PreprocessLambda { binder: Span },
}

impl Justification {
    pub fn display(&self, elab: &Elaborator) -> String {
        match self {
            Justification::Variable => "variable".to_owned(),
            Justification::Apply => "apply".to_owned(),
            Justification::PreprocessLambda { binder } => "preprocessing lambda".to_owned(),
        }
    }
}

/// A unification constraint with certain properties.
pub enum CategorisedConstraint<'cache> {
    Pattern(PatternConstraint<'cache>),
}

/// A pattern constraint is a constraint of the form `?m l_1 ... l_n == t`
/// where the arguments `l_i` are distinct local constants, and `t` is a replacement expression
/// that does not contain `t`.
pub struct PatternConstraint<'cache> {
    pub metavariable: Metavariable<Expression<'cache>>,
    pub arguments: Vec<(Provenance, LocalConstant<Expression<'cache>>)>,
    pub replacement: Expression<'cache>,
}

impl<'cache> UnificationConstraint<'cache> {
    /// Attempts to simplify this unification constraint into a list of simpler categorised constraints.
    pub fn simplify(
        self,
        cache: &ExpressionCache<'cache>,
    ) -> Vec<(CategorisedConstraint<'cache>, Justification)> {
        if self.expected == self.actual {
            // We have already solved this constraint.
            return Vec::new();
        }

        // Simplification occurs differently depending on which variables were stuck, and how.
        match (self.expected.stuck(cache), self.actual.stuck(cache)) {
            (Some(StuckExpression::Application(_)), None) => {
                let constraint = UnificationConstraint::categorise_stuck_application(
                    cache,
                    self.expected,
                    self.actual,
                );
                vec![(constraint, self.justification)]
            }
            (None, Some(StuckExpression::Application(_))) => {
                let constraint = UnificationConstraint::categorise_stuck_application(
                    cache,
                    self.actual,
                    self.expected,
                );
                vec![(constraint, self.justification)]
            }
            result => todo!("{:?}", result),
        }
    }

    /// Categorise a pattern, quasi-pattern, flex-rigid, or flex-flex unification constraint.
    /// `stuck_application` is an expression that is stuck by [`StuckExpression::Application`].
    fn categorise_stuck_application(
        cache: &ExpressionCache<'cache>,
        stuck_application: Expression<'cache>,
        other: Expression<'cache>,
    ) -> CategorisedConstraint<'cache> {
        let (head, args) = stuck_application.destructure_as_nary_application(cache);

        // The head expression is a metavariable by assumption.
        let head = if let ExpressionT::Metavariable(var) = head.value(cache) {
            var
        } else {
            unreachable!()
        };

        let arguments = args
            .iter()
            .filter_map(|expr| {
                if let ExpressionT::LocalConstant(local) = expr.value(cache) {
                    Some((expr.provenance(cache), local))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        if arguments.len() == args.len() {
            // This is a pattern or quasi-pattern constraint.
            // First, check if the result references the head symbol `?m`.
            if other.metavariable_occurs(cache, head) {
                // This is a quasi-pattern.
                todo!()
            } else {
                // Check that the arguments are all distinct.
                if arguments.iter().enumerate().all(|(i, (_, local))| {
                    arguments
                        .iter()
                        .skip(i + 1)
                        .all(|(_, other_local)| local != other_local)
                }) {
                    // This is a pattern.
                    CategorisedConstraint::Pattern(PatternConstraint {
                        metavariable: head,
                        arguments,
                        replacement: other,
                    })
                } else {
                    // This is a quasi-pattern.
                    todo!()
                }
            }
        } else {
            // Some argument was not a free variable, so this is a flex-rigid or flex-flex constraint.
            todo!()
        }
    }
}
