//! Unfolds definitions.

use crate::expr::{Apply, Expression, ExpressionT, Inst};

use super::{definition::DefinitionHeight, get_certified_definition, Db, ReducibilityHints};

/// Returns a number if the head of this expression is a definition that we can unfold.
/// Intuitively, the number returned is higher for more complicated definitions.
///
/// # Dependencies
///
/// If the head of this expression is a definition, this query depends on the certified definition.
pub fn head_definition_height(e: Expression, db: &dyn Db) -> Option<DefinitionHeight> {
    match e.value(db) {
        ExpressionT::Inst(inst) => definition_height(db, inst),
        ExpressionT::Apply(ap) => head_definition_height(db, ap.function),
        _ => None,
    }
}

/// Returns the height of the definition that this [`Inst`] refers to.
/// If this instance could not be resolved, was not a definition, or was not reducible, return [`None`].
pub fn definition_height(db: &dyn Db, inst: &Inst) -> Option<DefinitionHeight> {
    get_certified_definition(db, inst.name.to_path(db)).and_then(|def| {
        if let ReducibilityHints::Regular { height } = def.reducibility_hints() {
            Some(*height)
        } else {
            None
        }
    })
}

/// If the head of this expression is a definition, unfold it,
/// even if it is marked as [`ReducibilityHints::Opaque`].
/// This is sometimes called delta-reduction.
///
/// If we couldn't unfold anything, return [`None`].
/// This will always return a value if [`head_definition_height`] returned a [`Some`] value.
pub fn unfold_definition(db: &dyn Db, t: Term) -> Option<Term> {
    match t.value(db) {
        ExpressionT::Inst(inst) => get_certified_definition(db, inst.name.to_path(db))
            .and_then(|def| def.def().contents.expr.as_ref())
            .map(|e| e.clone().to_term(db)),
        ExpressionT::Apply(ap) => unfold_definition(db, ap.function).map(|t| {
            Term::new(
                db,
                ExpressionT::Apply(Apply {
                    function: t,
                    argument: ap.argument,
                }),
            )
        }),
        _ => None,
    }
}
