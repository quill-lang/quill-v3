use fcommon::Span;
use fkernel::{
    expr::{Expression, ExpressionCache, ExpressionT, Metavariable, StuckExpression},
    universe::Universe,
};

use crate::elaborator::Elaborator;

/// An expression `actual` is required to be definitionally equal to `expected`.
pub struct UnificationConstraint<'cache> {
    pub expected: Expression<'cache>,
    pub actual: Expression<'cache>,
    pub justification: Justification,
}

/// A universe `actual` is required to be definitionally equal to `expected`.
pub struct UniverseConstraint {
    pub expected: Universe,
    pub actual: Universe,
    pub justification: Justification,
}

/// The reason why a particular unification constraint was given.
#[derive(Clone)]
pub enum Justification {
    Variable,
    Apply,
    PreprocessLambda {
        binder: Span,
    },
    Join {
        first: Box<Justification>,
        second: Box<Justification>,
    },
    PatternSolution,
    PiParameter(Box<Justification>),
    PiRegion(Box<Justification>),
    PiBody(Box<Justification>),
}

impl Justification {
    pub fn display(&self, elab: &Elaborator) -> String {
        match self {
            Justification::Variable => "variable".to_owned(),
            Justification::Apply => "apply".to_owned(),
            Justification::PreprocessLambda { binder: _ } => "preprocessing lambda".to_owned(),
            Justification::Join { first, second } => {
                format!("{}; {}", first.display(elab), second.display(elab))
            }
            _ => todo!(),
        }
    }
}

/// A unification constraint with certain properties.
pub enum CategorisedConstraint<'cache> {
    StuckApplication(StuckApplicationConstraint<'cache>),
    Universe(UniverseConstraint),
}

impl<'cache> UnificationConstraint<'cache> {
    /// Attempts to simplify this unification constraint into a list of simpler categorised constraints.
    pub fn simplify(mut self, elab: &Elaborator<'_, 'cache>) -> Vec<CategorisedConstraint<'cache>> {
        if self.expected == self.actual {
            // We have already solved this constraint.
            return Vec::new();
        }

        // Perform some very simple reductions on the expressions.
        self.expected = elab.simple_reduce(self.expected);
        self.actual = elab.simple_reduce(self.actual);

        // Try the simple equality check again after performing reductions.
        if self.expected == self.actual {
            return Vec::new();
        }

        // Simplification occurs differently depending on which variables were stuck, and how.
        // First, we check if the expressions have particular forms that are easy to simplify.

        match (
            self.expected.value(elab.cache()),
            self.actual.value(elab.cache()),
        ) {
            (ExpressionT::Pi(expected), ExpressionT::Pi(actual)) => {
                // Two function types are equal if their parameters and return types match.
                assert_eq!(
                    expected.structure.function_ownership,
                    actual.structure.function_ownership
                );
                assert_eq!(
                    expected.structure.bound.ownership,
                    actual.structure.bound.ownership
                );

                // Unify their parameters, return types, and regions.
                let mut constraints = UnificationConstraint {
                    expected: expected.structure.bound.ty,
                    actual: actual.structure.bound.ty,
                    justification: Justification::PiParameter(Box::new(self.justification.clone())),
                }
                .simplify(elab);
                constraints.extend(
                    UnificationConstraint {
                        expected: expected.structure.region,
                        actual: actual.structure.region,
                        justification: Justification::PiRegion(Box::new(
                            self.justification.clone(),
                        )),
                    }
                    .simplify(elab),
                );
                let local = Expression::new(
                    elab.cache(),
                    expected.structure.bound.name.0.provenance,
                    ExpressionT::LocalConstant(expected.structure.generate_local(elab.cache())),
                );
                constraints.extend(
                    UnificationConstraint {
                        expected: expected.result.instantiate(elab.cache(), local),
                        actual: actual.result.instantiate(elab.cache(), local),
                        justification: Justification::PiRegion(Box::new(
                            self.justification.clone(),
                        )),
                    }
                    .simplify(elab),
                );
                return constraints;
            }
            (ExpressionT::Sort(expected), ExpressionT::Sort(actual)) => {
                return vec![CategorisedConstraint::Universe(UniverseConstraint {
                    expected: expected.0,
                    actual: actual.0,
                    justification: self.justification,
                })]
            }
            _ => (),
        }

        // It was not in any of the simple forms that we recognised.

        match (
            self.expected.stuck(elab.cache()),
            self.actual.stuck(elab.cache()),
        ) {
            (Some(StuckExpression::Application(metavariable)), None) => {
                vec![CategorisedConstraint::StuckApplication(
                    StuckApplicationConstraint {
                        metavariable,
                        arguments: self.expected.apply_args(elab.cache()),
                        replacement: self.actual,
                        justification: self.justification,
                    },
                )]
            }
            (None, Some(StuckExpression::Application(metavariable))) => {
                vec![CategorisedConstraint::StuckApplication(
                    StuckApplicationConstraint {
                        metavariable,
                        arguments: self.actual.apply_args(elab.cache()),
                        replacement: self.expected,
                        justification: self.justification,
                    },
                )]
            }
            result => todo!("{:?}", result),
        }
    }
}

/// A stuck application constraint is a constraint of the form `?m l_1 ... l_n == t`.
/// It is assumed that `t` is not also a stuck application.
///
/// * It is called a pattern constraint if the arguments `l_i` are pairwise distinct local constants,
///   and `t` is a replacement expression that does not contain `?m`.
/// * It is called a quasi-pattern constraint if the `l_i` are not pairwise distinct.
/// * It is called a flex-rigid constraint if at least one of the `l_i` is not a local constant.
#[derive(Clone)]
pub struct StuckApplicationConstraint<'cache> {
    pub metavariable: Metavariable<Expression<'cache>>,
    pub arguments: Vec<Expression<'cache>>,
    pub replacement: Expression<'cache>,
    pub justification: Justification,
}

/// Categorisations of stuck applications.
/// Smaller values in the provided ordering are considered "simpler" constraints to solve.
/// For instance, pattern constraints are very easy to solve.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum StuckApplicationType {
    Pattern,
    QuasiPattern,
    FlexRigid,
}

impl<'cache> StuckApplicationConstraint<'cache> {
    /// Categorise a pattern, quasi-pattern, flex-rigid, or flex-flex unification constraint.
    /// `stuck_application` is an expression that is stuck by [`StuckExpression::Application`].
    pub fn categorise(&self, cache: &ExpressionCache<'cache>) -> StuckApplicationType {
        let arguments = self
            .arguments
            .iter()
            .filter_map(|expr| {
                if let ExpressionT::LocalConstant(local) = expr.value(cache) {
                    Some((expr.provenance(cache), local))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        if arguments.len() == self.arguments.len() {
            // This is a pattern or quasi-pattern constraint.
            // First, check if the result references the head symbol `?m`.
            if self
                .replacement
                .metavariable_occurs(cache, self.metavariable)
            {
                // This is a quasi-pattern.
                StuckApplicationType::QuasiPattern
            } else {
                // Check that the arguments are all distinct.
                if arguments.iter().enumerate().all(|(i, (_, local))| {
                    arguments
                        .iter()
                        .skip(i + 1)
                        .all(|(_, other_local)| local != other_local)
                }) {
                    // This is a pattern.
                    StuckApplicationType::Pattern
                } else {
                    // This is a quasi-pattern.
                    StuckApplicationType::QuasiPattern
                }
            }
        } else {
            // Some argument was not a free variable, so this is a flex-rigid constraint.
            StuckApplicationType::FlexRigid
        }
    }
}
