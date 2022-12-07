//! Unfolds definitions.

use fexpr::expr::{ExpressionT, Inst, Term};

use crate::Db;

use super::def::DefinitionHeight;

/// Returns a number if the head of this expression is a definition that we can unfold.
/// Intuitively, the number returned is higher for more complicated definitions.
///
/// # Dependencies
///
/// If the head of this expression is a definition, this query depends on the certified definition.
#[salsa::tracked]
pub fn head_definition_height(db: &dyn Db, t: Term) -> Option<DefinitionHeight> {
    todo!()
    // match &e.contents {
    //     ExprContents::Inst(inst) => env
    //         .definitions
    //         .get(&inst.name.to_path(env.db.up()))
    //         .and_then(|def| {
    //             if let ReducibilityHints::Regular { height } = def.reducibility_hints() {
    //                 Some(*height)
    //             } else {
    //                 None
    //             }
    //         }),
    //     ExprContents::Apply(ap) => head_definition_height(env, &ap.function),
    //     _ => None,
    // }
}

/// Returns the height of the definition that this [`Inst`] refers to.
/// If this instance could not be resolved, was not a definition, or was not reducible, return [`None`].
pub fn definition_height(db: &dyn Db, inst: Inst<()>) -> Option<DefinitionHeight> {
    todo!()
    // env.definitions
    //     .get(&inst.name.to_path(env.db.up()))
    //     .and_then(|def| {
    //         if let ReducibilityHints::Regular { height } = def.reducibility_hints() {
    //             Some(*height)
    //         } else {
    //             None
    //         }
    //     })
}

/// Returns the unfolded definition that this [`Inst`] refers to.
/// If we could not unfold the definition, return `None`.
fn unfold_definition_core<'a>(db: &dyn Db, t: &Inst<()>) -> Option<Term> {
    todo!()
    // env.definitions
    //     .get(&e.name.to_path(env.db.up()))
    //     .and_then(|def| def.def().contents.expr.as_ref())
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
    todo!()
    // match &mut e.contents {
    //     ExprContents::Inst(inst) => {
    //         if let Some(expr) = unfold_definition_core(env, inst) {
    //             *e = expr.clone();
    //             true
    //         } else {
    //             false
    //         }
    //     }
    //     ExprContents::Apply(ap) => unfold_definition(env, &mut ap.function),
    //     _ => false,
    // }
}
