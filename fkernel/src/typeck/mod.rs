use fcommon::Dr;
use fexpr::{
    basic::Provenance,
    definition::Definition,
    expr::{Expression, Inst, Term},
};

pub mod def;
mod unfold;

use def::*;
use unfold::*;

use crate::{term::free_vars::FreeVars, universe::UniverseOps};

#[salsa::query_group(TypeCheckerStorage)]
pub trait TypeChecker: FreeVars + UniverseOps {
    /// Type checks a definition.
    /// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
    fn check(
        &self,
        def: Definition<Provenance, Expression>,
        origin: DefinitionOrigin,
    ) -> Dr<CertifiedDefinition>;

    // -- Utilities for unfolding --

    /// Returns a number if the head of this expression is a definition that we can unfold.
    /// Intuitively, the number returned is higher for more complicated definitions.
    ///
    /// # Dependencies
    ///
    /// If the head of this expression is a definition, this query depends on the certified definition.
    fn head_definition_height(&self, t: Term) -> Option<DefinitionHeight>;

    /// Returns the height of the definition that this [`Inst`] refers to.
    /// If this instance could not be resolved, was not a definition, or was not reducible, return [`None`].
    ///
    /// # Dependencies
    ///
    /// This query depends on the certified definition.
    fn definition_height(&self, inst: Inst<()>) -> Option<DefinitionHeight>;

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
    fn unfold_definition(&self, t: Term) -> Option<Term>;
}

fn check(
    db: &dyn TypeChecker,
    def: Definition<Provenance, Expression>,
    origin: DefinitionOrigin,
) -> Dr<CertifiedDefinition> {
    todo!()
}
