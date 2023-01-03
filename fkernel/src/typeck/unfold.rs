//! Unfolds definitions.

use crate::{
    expr::{Apply, Expression, ExpressionCache, ExpressionT, Inst},
    get_certified_definition, Db,
};

use super::{definition::DefinitionHeight, ReducibilityHints};

impl Inst {
    /// Returns the height of the definition that this [`Inst`] refers to.
    /// If this instance could not be resolved, was not a definition, or was not reducible, return [`None`].
    pub fn definition_height(&self, db: &dyn Db) -> Option<DefinitionHeight> {
        get_certified_definition(db, self.name.to_path(db))
            .as_ref()
            .and_then(|def| {
                if let ReducibilityHints::Regular { height } = def.reducibility_hints() {
                    Some(*height)
                } else {
                    None
                }
            })
    }
}

impl<'cache> Expression<'cache> {
    /// Returns a number if the head of this expression is a definition that we can unfold.
    /// Intuitively, the number returned is higher for more complicated definitions.
    pub fn head_definition_height(
        self,
        cache: &ExpressionCache<'cache>,
    ) -> Option<DefinitionHeight> {
        match self.value(cache) {
            ExpressionT::Inst(inst) => inst.definition_height(cache.db()),
            ExpressionT::Apply(ap) => ap.function.head_definition_height(cache),
            _ => None,
        }
    }

    /// If the head of this expression is a definition, unfold it,
    /// even if it is marked as [`ReducibilityHints::Opaque`].
    /// This is sometimes called delta-reduction.
    ///
    /// If we couldn't unfold anything, return [`None`].
    /// This will always return a value if [`head_definition_height`] returned a [`Some`] value.
    pub fn unfold_definition(self, cache: &ExpressionCache<'cache>) -> Option<Self> {
        match self.value(cache) {
            ExpressionT::Inst(inst) => {
                get_certified_definition(cache.db(), inst.name.to_path(cache.db()))
                    .as_ref()
                    .and_then(|def| def.def().contents.expr.as_ref())
                    .map(|e| e.clone().from_heap(cache))
            }
            ExpressionT::Apply(ap) => ap.function.unfold_definition(cache).map(|e| {
                Expression::new(
                    cache,
                    self.provenance(cache),
                    ExpressionT::Apply(Apply {
                        function: e,
                        argument: ap.argument,
                    }),
                )
            }),
            _ => None,
        }
    }
}
