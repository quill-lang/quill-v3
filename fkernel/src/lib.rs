#![feature(let_chains)]
#![feature(trait_upcasting)]

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

#[salsa::jar(db = Db)]
pub struct Jar(
    module::module_from_feather_source,
    inductive::get_inductive,
    inductive::certify_inductive,
    typeck::certify_definition,
    typeck::get_definition,
);

pub trait Db: fcommon::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + fcommon::Db + salsa::DbWithJar<Jar> {}
