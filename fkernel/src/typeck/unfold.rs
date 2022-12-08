//! Unfolds definitions.

use fexpr::expr::{Apply, ExpressionT, Inst, Term};

use crate::{
    typeck::{certify_definition, ReducibilityHints},
    Db,
};

use super::def::DefinitionHeight;

/// Returns a number if the head of this expression is a definition that we can unfold.
/// Intuitively, the number returned is higher for more complicated definitions.
///
/// # Dependencies
///
/// If the head of this expression is a definition, this query depends on the certified definition.
#[salsa::tracked]
pub fn head_definition_height(db: &dyn Db, t: Term) -> Option<DefinitionHeight> {
    match t.value(db) {
        ExpressionT::Inst(inst) => definition_height(db, inst),
        ExpressionT::Apply(ap) => head_definition_height(db, ap.function),
        _ => None,
    }
}

/// Returns the height of the definition that this [`Inst`] refers to.
/// If this instance could not be resolved, was not a definition, or was not reducible, return [`None`].
pub fn definition_height(db: &dyn Db, inst: Inst<()>) -> Option<DefinitionHeight> {
    certify_definition(db, inst.name.to_path(db))
        .value()
        .as_ref()
        .and_then(|def| {
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
/// This will always return a value if [`can_unfold_definition`] returned a [`Some`] value.
///
/// # Dependencies
///
/// If the head of this expression is a definition, this query depends on the certified definition.
#[salsa::tracked]
pub fn unfold_definition(db: &dyn Db, t: Term) -> Option<Term> {
    match t.value(db) {
        ExpressionT::Inst(inst) => certify_definition(db, inst.name.to_path(db))
            .value()
            .as_ref()
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
