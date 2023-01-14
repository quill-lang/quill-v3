use fcommon::Span;
use fkernel::{
    expr::{Apply, Expression, ExpressionCache, ExpressionT, Hole, StuckExpression},
    universe::Universe,
};

use crate::elaborator::Elaborator;

/// An expression `actual` is required to be definitionally equal to `expected`.
pub struct UnificationConstraint<'cache> {
    pub expected: Expression<'cache>,
    pub actual: Expression<'cache>,
    pub justification: Justification<'cache>,
}

/// A universe `actual` is required to be definitionally equal to `expected`.
pub struct UniverseConstraint<'cache> {
    pub expected: Universe,
    pub actual: Universe,
    pub justification: Justification<'cache>,
}

/// The reason why a particular unification constraint was given.
#[derive(Clone)]
pub enum Justification<'cache> {
    Variable,
    ApplyPreprocess,
    Apply { apply: Apply<Expression<'cache>> },
    PreprocessLambda { binder: Span },
    Join { first: Box<Self>, second: Box<Self> },
    PatternSolution,
    PiParameter(Box<Self>),
    PiRegion(Box<Self>),
    PiBody(Box<Self>),
    PiType,
    Borrow,
}

impl<'cache> Justification<'cache> {
    pub fn display(&self, elab: &Elaborator<'_, 'cache>) -> String {
        match self {
            Justification::Variable => "variable".to_owned(),
            Justification::ApplyPreprocess => "apply (preprocess)".to_owned(),
            Justification::Apply { apply } => format!(
                "apply function {} to argument {}",
                elab.pretty_print(apply.function),
                elab.pretty_print(apply.argument),
            ),
            Justification::PreprocessLambda { binder: _ } => "preprocessing lambda".to_owned(),
            Justification::Join { first, second } => {
                format!("{}; {}", first.display(elab), second.display(elab))
            }
            Justification::PatternSolution => "pattern solution".to_owned(),
            Justification::PiParameter(_) => "pi parameter".to_owned(),
            Justification::PiRegion(_) => "pi region".to_owned(),
            Justification::PiBody(_) => "pi body".to_owned(),
            Justification::PiType => "pi type".to_owned(),
            Justification::Borrow => "borrow".to_owned(),
        }
    }
}

/// A unification constraint with certain properties.
pub enum CategorisedConstraint<'cache> {
    StuckApplication(StuckApplicationConstraint<'cache>),
    FlexFlex(FlexFlexConstraint<'cache>),
    Universe(UniverseConstraint<'cache>),
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

        #[cfg(feature = "elaborator_diagnostics")]
        tracing::trace!(
            "simplifying {} =?= {}",
            elab.pretty_print(self.expected),
            elab.pretty_print(self.actual)
        );

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

                // Unify their parameters and return types.
                // Deal with regions later.
                let mut constraints = UnificationConstraint {
                    expected: expected.structure.bound.ty,
                    actual: actual.structure.bound.ty,
                    justification: Justification::PiParameter(Box::new(self.justification.clone())),
                }
                .simplify(elab);
                let local = Expression::new(
                    elab.cache(),
                    expected.structure.bound.name.0.provenance,
                    ExpressionT::LocalConstant(elab.cache().gen_local(expected.structure)),
                );
                constraints.extend(
                    UnificationConstraint {
                        expected: expected.result.instantiate(elab.cache(), local),
                        actual: actual.result.instantiate(elab.cache(), local),
                        justification: Justification::PiBody(Box::new(self.justification.clone())),
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
            (ExpressionT::LocalConstant(expected), ExpressionT::LocalConstant(actual)) => {
                if expected == actual {
                    // This case can occur if the expected and actual expressions differ only in provenance.
                    return Vec::new();
                } else {
                    todo!()
                }
            }
            _ => {}
        }

        // It was not in any of the simple forms that we recognised.

        match (
            self.expected.stuck(elab.cache()),
            self.actual.stuck(elab.cache()),
        ) {
            (Some(StuckExpression::Application(hole)), None) => {
                vec![CategorisedConstraint::StuckApplication(
                    StuckApplicationConstraint {
                        hole,
                        arguments: self.expected.apply_args(elab.cache()),
                        replacement: self.actual,
                        justification: self.justification,
                    },
                )]
            }
            (None, Some(StuckExpression::Application(hole))) => {
                vec![CategorisedConstraint::StuckApplication(
                    StuckApplicationConstraint {
                        hole,
                        arguments: self.actual.apply_args(elab.cache()),
                        replacement: self.expected,
                        justification: self.justification,
                    },
                )]
            }
            (
                Some(StuckExpression::Application(expected)),
                Some(StuckExpression::Application(actual)),
            ) => {
                // This is a flex-flex constraint.
                vec![CategorisedConstraint::FlexFlex(FlexFlexConstraint {
                    expected,
                    expected_arguments: self.expected.apply_args(elab.cache()),
                    actual,
                    actual_arguments: self.actual.apply_args(elab.cache()),
                    justification: self.justification,
                })]
            }
            result => {
                tracing::error!(
                    "don't know how to categorise {} =?= {}\n{:?} = {:?}\n{:?} = {:?}",
                    elab.pretty_print(self.expected),
                    elab.pretty_print(self.actual),
                    self.expected,
                    self.expected.value(elab.cache()),
                    self.actual,
                    self.actual.value(elab.cache()),
                );
                todo!("{:?}", result)
            }
        }
    }
}

/// A stuck application constraint is a constraint of the form `?m[l_1, ..., l_n] l_{n+1} ... l_m == t`.
/// It is assumed that `t` is not also a stuck application.
///
/// * It is called a pattern constraint if the arguments `l_i` are pairwise distinct local constants,
///   and `t` is a replacement expression that does not contain `?m`.
/// * It is called a quasi-pattern constraint if the `l_i` are not pairwise distinct.
/// * It is called a flex-rigid constraint if at least one of the `l_i` is not a local constant.
#[derive(Clone)]
pub struct StuckApplicationConstraint<'cache> {
    pub hole: Hole<Expression<'cache>>,
    /// The extra arguments, in addition to the ones implicitly in the hole.
    pub arguments: Vec<Expression<'cache>>,
    pub replacement: Expression<'cache>,
    pub justification: Justification<'cache>,
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
            .hole
            .args
            .iter()
            .chain(&self.arguments)
            .filter_map(|expr| {
                if let ExpressionT::LocalConstant(local) = expr.value(cache) {
                    Some((expr.provenance(cache), local))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        if arguments.len() == self.hole.args.len() + self.arguments.len() {
            // This is a pattern or quasi-pattern constraint.
            // First, check if the result references the head symbol `?m`.
            if self.replacement.hole_occurs(cache, self.hole.id) {
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

#[derive(Clone)]
pub struct FlexFlexConstraint<'cache> {
    pub expected: Hole<Expression<'cache>>,
    pub expected_arguments: Vec<Expression<'cache>>,
    pub actual: Hole<Expression<'cache>>,
    pub actual_arguments: Vec<Expression<'cache>>,
    pub justification: Justification<'cache>,
}
