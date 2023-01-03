use fcommon::Span;
use fkernel::expr::Expression;

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
