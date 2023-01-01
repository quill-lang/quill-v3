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
    deps::dependencies,
    inductive::get_inductive,
    inductive::certify_inductive,
    typeck::certify_definition,
    typeck::get_definition,
    typeck::infer_type,
    typeck::to_weak_head_normal_form,
);

pub trait Db: fcommon::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + fcommon::Db + salsa::DbWithJar<Jar> {}
