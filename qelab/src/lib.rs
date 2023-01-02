//! Converts parsed quill expressions into fully elaborated feather expressions.
//! <https://doi.org/10.48550/arXiv.1505.04324>

#![feature(trait_upcasting)]

mod constraint;
pub mod elaborator;
mod preprocess;

#[salsa::jar(db = Db)]
pub struct Jar();

pub trait Db: fkernel::Db + qparse::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + fkernel::Db + qparse::Db + salsa::DbWithJar<Jar> {}
