use fcommon::{Dr, Path};
use fexpr::{basic::Provenance, definition::Definition, expr::Expression};

use crate::Db;

mod def;
mod unfold;

pub use def::*;
pub use unfold::*;

/// Retrieves the definition with the given name.
/// This definition will not have been type checked.
#[salsa::tracked(return_ref)]
pub fn get_definition(db: &dyn Db, path: Path) -> Dr<Definition<Provenance, Expression>> {
    todo!()
}

/// Type checks the definition with the given name.
/// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
///
/// # Usage
///
/// When type checking a definition, we may depend on previously certified definitions.
/// These should only be accessed using `certify_definition(...).value()`, so that we don't double any error messages emitted.
#[salsa::tracked(return_ref)]
pub fn certify_definition(db: &dyn Db, path: Path) -> Dr<CertifiedDefinition> {
    todo!()
}
