use fcommon::Dr;
use fexpr::{basic::Provenance, definition::Definition, expr::Expression};

use crate::Db;

mod def;
mod unfold;

pub use def::*;
pub use unfold::*;

#[salsa::tracked]
pub struct Defn {
    #[return_ref]
    pub value: Definition<Provenance, Expression>,
}

/// Type checks a definition.
/// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
#[salsa::tracked]
pub fn check(
    db: &dyn Db,
    def: Defn,
    origin: DefinitionOrigin,
) -> Dr<CertifiedDefinition> {
    todo!()
}
