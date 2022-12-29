#![feature(trait_upcasting)]

pub mod basic;
pub mod definition;
pub mod expr;
pub mod inductive;
pub mod module;
pub mod multiplicity;
pub mod universe;
pub mod result;

#[salsa::jar(db = Db)]
pub struct Jar(
    expr::largest_unusable_metavariable,
    expr::Term,
    module::module_from_feather_source,
);

pub trait Db: fcommon::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + fcommon::Db + salsa::DbWithJar<Jar> {}
