use fcommon::{Dr, Path};
use fexpr::{basic::Provenance, definition::Definition, expr::Expression};

use crate::Db;

mod def;
mod defeq;
mod infer;
mod unfold;
mod whnf;

pub use def::*;
pub use defeq::*;
pub use infer::*;
pub use unfold::*;
pub use whnf::*;

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
/// These should only be accessed using [`get_certified_definition`], so that we don't double any error messages emitted.
#[salsa::tracked(return_ref)]
pub fn certify_definition(db: &dyn Db, path: Path) -> Dr<CertifiedDefinition> {
    todo!()
}

/// Type checks the definition with the given name, or retrieves it from the database if it was already type checked.
/// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
/// This function will discard any diagnostic messages produced by type checking the definition.
pub fn get_certified_definition(db: &dyn Db, path: Path) -> Option<&CertifiedDefinition> {
    certify_definition(db, path).value().as_ref()
}
