use fcommon::Span;
use fkernel::expr::Expression;

/// An expression `actual` is required to be definitionall equal to `expected`.
pub struct UnificationConstraint<'cache> {
    pub expected: Expression<'cache>,
    pub actual: Expression<'cache>,
    pub justification: Justification,
}

/// The reason why a particular unification constraint was given.
pub enum Justification {
    Variable,
    PreprocessLambda {
        binder: Span,
    }
}
