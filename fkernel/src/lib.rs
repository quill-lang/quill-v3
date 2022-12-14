#![feature(let_chains)]
#![feature(trait_upcasting)]

pub mod deps;
pub mod inductive;
pub mod term;
pub mod typeck;
pub mod universe;

#[salsa::jar(db = Db)]
pub struct Jar(
    deps::dependencies,
    inductive::get_inductive,
    inductive::certify_inductive,
    term::closed,
    term::first_free_variable_index,
    term::first_local_or_metavariable,
    term::get_max_height,
    term::has_free_variables,
    term::instantiate,
    typeck::certify_definition,
    typeck::get_definition,
    typeck::head_definition_height,
    typeck::infer_type,
    typeck::to_weak_head_normal_form,
    typeck::unfold_definition,
);

pub trait Db: fexpr::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + fexpr::Db + salsa::DbWithJar<Jar> {}
