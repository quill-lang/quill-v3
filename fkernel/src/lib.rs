#![feature(let_chains)]
#![feature(trait_upcasting)]

use definition::Definition;
use fcommon::Path;
use inductive::{CertifiedInductive, Inductive};
use result::Dr;
use typeck::CertifiedDefinition;

pub mod basic;
pub mod definition;
pub mod deps;
pub mod expr;
pub mod inductive;
pub mod module;
pub mod multiplicity;
pub mod result;
pub mod typeck;
pub mod universe;

pub trait Db: fcommon::Db + salsa::DbWithJar<Jar> {
    /// Given a fully qualified path of a definition in a either a feather or a quill file,
    /// return the parsed and elaborated definition.
    /// This definition will not have been type checked.
    ///
    /// This function is later implemented by the `qelab` crate.
    fn get_definition_impl(&self, path: Path) -> Dr<Definition>;

    /// Given a fully qualified path of an inductive in a either a feather or a quill file,
    /// return the parsed and elaborated inductive.
    /// This inductive will not have been type checked.
    ///
    /// This function is later implemented by the `qelab` crate.
    fn get_inductive_impl(&self, path: Path) -> Dr<Inductive>;

    /// Type checks the definition with the given name.
    /// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
    ///
    /// This function is later implemented by the `qelab` crate.
    ///
    /// # Usage
    ///
    /// When type checking a definition, we may depend on previously certified definitions.
    /// These should only be accessed using [`get_certified_definition`], so that we don't double any error messages emitted.
    fn certify_definition_impl(&self, path: Path) -> Dr<CertifiedDefinition>;

    /// Type checks the inductive with the given name.
    /// This function returns a [`CertifiedInductive`], an inductive that has been verified by the type checker.
    ///
    /// This function is later implemented by the `qelab` crate.
    ///
    /// # Usage
    ///
    /// When certifying a definition or inductive, we may depend on previously certified inductives.
    /// These should only be accessed using [`get_certified_inductive`], so that we don't double any error messages emitted.
    fn certify_inductive_impl(&self, path: Path) -> Dr<CertifiedInductive>;
}

/// Given a fully qualified path of a definition in a either a feather or a quill file,
/// return the parsed and elaborated definition.
/// This definition will not have been type checked.
#[salsa::tracked(return_ref)]
pub fn get_definition(db: &dyn Db, path: Path) -> Dr<Definition> {
    db.get_definition_impl(path)
}

/// Given a fully qualified path of an inductive in a either a feather or a quill file,
/// return the parsed and elaborated inductive.
/// This inductive will not have been type checked.
#[salsa::tracked(return_ref)]
pub fn get_inductive(db: &dyn Db, path: Path) -> Dr<Inductive> {
    db.get_inductive_impl(path)
}

/// Type checks the definition with the given name.
/// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
///
/// See also [`typeck::certify_definition`].
///
/// # Usage
///
/// When type checking a definition, we may depend on previously certified definitions.
/// These should only be accessed using [`get_certified_definition`], so that we don't double any error messages emitted.
#[salsa::tracked(return_ref)]
pub fn certify_definition(db: &dyn Db, path: Path) -> Dr<CertifiedDefinition> {
    db.certify_definition_impl(path)
}

/// Type checks the inductive with the given name.
/// This function returns a [`CertifiedInductive`], an inductive that has been verified by the type checker.
///
/// See also [`inductive::certify::certify_inductive`].
///
/// # Usage
///
/// When certifying a definition or inductive, we may depend on previously certified inductives.
/// These should only be accessed using [`get_certified_inductive`], so that we don't double any error messages emitted.
#[salsa::tracked(return_ref)]
pub fn certify_inductive(db: &dyn Db, path: Path) -> Dr<CertifiedInductive> {
    db.certify_inductive_impl(path)
}

/// Type checks the definition with the given name, or retrieves it from the database if it was already type checked.
/// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
/// This function will discard any diagnostic messages produced by type checking the definition.
#[salsa::tracked(return_ref)]
pub fn get_certified_definition(db: &dyn Db, path: Path) -> Option<CertifiedDefinition> {
    certify_definition(db, path).value().clone()
}

/// Type checks the definition with the given name, or retrieves it from the database if it was already type checked.
/// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
/// This function will discard any diagnostic messages produced by type checking the definition.
#[salsa::tracked(return_ref)]
pub fn get_certified_inductive(db: &dyn Db, path: Path) -> Option<CertifiedInductive> {
    certify_inductive(db, path).value().clone()
}

#[salsa::jar(db = Db)]
pub struct Jar(
    module::module_from_feather_source,
    get_definition,
    get_inductive,
    certify_definition,
    certify_inductive,
    get_certified_definition,
    get_certified_inductive,
);
