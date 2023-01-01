use std::collections::BTreeMap;

use fcommon::{Span, Str};
use fexpr::{
    basic::Provenance,
    expr::{Expression, LocalConstant, MetavariableGenerator},
    result::Dr,
};
use qparse::expr::PExpression;

use crate::Db;

/// The elaborator converts parsed quill expressions into feather expressions.
/// An elaborator keeps track of metavariable assignments and performs unification tasks.
///
/// When all necessary expressions have been passed through the elaborator, it can be *finalised*,
/// making a final decision on what terms metavariables should map to, ensuring that all metavariables
/// actually have an assignment, and that the result is type-correct.
pub struct Elaborator<'db> {
    db: &'db dyn Db,
    meta_gen: MetavariableGenerator<Box<Expression>>,
}

#[derive(Default)]
pub struct Context {
    /// A map from local variable names to the span at which they were defined, and
    /// local constants representing these local variables.
    local_variables: BTreeMap<Str, (Span, LocalConstant<Provenance, Box<Expression>>)>,
}

impl<'db> Elaborator<'db> {
    /// Creates a new elaborator.
    /// `largest_unusable` is used to instantiate the metavariable generator.
    pub fn new(db: &'db dyn Db, largest_unusable: Option<u32>) -> Self {
        Self {
            db,
            meta_gen: MetavariableGenerator::new(largest_unusable),
        }
    }

    /// Tries to elaborate the parsed expression.
    /// This process can create and unify metavariables stored in this elaborator.
    pub fn elaborate(
        &mut self,
        e: &PExpression,
        expected_type: Option<&Expression>,
        context: &Context,
    ) -> Dr<Expression> {
        match e {
            PExpression::Variable { .. } => todo!(),
            PExpression::Borrow { .. } => todo!(),
            PExpression::Dereference { .. } => todo!(),
            PExpression::Apply { .. } => todo!(),
            PExpression::Intro { .. } => todo!(),
            PExpression::Match { .. } => todo!(),
            PExpression::Fix { .. } => todo!(),
            PExpression::Let { .. } => todo!(),
            PExpression::Lambda { .. } => todo!(),
            PExpression::FunctionType { .. } => todo!(),
            PExpression::Sort { .. } => todo!(),
            PExpression::Type { .. } => todo!(),
            PExpression::Prop(_) => todo!(),
            PExpression::StaticRegion(_) => todo!(),
            PExpression::Region(_) => todo!(),
            PExpression::RegionT(_) => todo!(),
            PExpression::Inductive(_) => todo!(),
        }
    }
}
