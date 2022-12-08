#![feature(let_chains)]
#![feature(trait_upcasting)]

pub mod deps;
pub mod term;
pub mod typeck;
pub mod universe;

#[salsa::jar(db = Db)]
pub struct Jar(
    deps::dependencies,
    term::first_free_variable_index,
    term::closed,
    term::has_free_variables,
    term::first_local_or_metavariable,
    term::get_max_height,
    term::instantiate,
    typeck::get_definition,
    typeck::certify_definition,
    typeck::head_definition_height,
    typeck::unfold_definition,
    universe::normalise_universe,
    universe::universe_at_most,
);

pub trait Db: fexpr::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + fexpr::Db + salsa::DbWithJar<Jar> {}
