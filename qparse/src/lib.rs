#![feature(trait_upcasting)]
#![feature(let_chains)]

//! A parser for Quill files. Since syntax can be extended, we cannot easily separate the parsing
//! phase on a per-file scale like many other parsers do. Instead, we must parse each *item*
//! separately, and when new notation is introduced, add this to the parser that will be used with
//! subsequent items.

mod lex;
// mod parse;

use lex::*;
// pub use parse::*;

use fcommon::{Dr, Source, Span};

#[salsa::jar(db = Db)]
pub struct Jar(module_from_quill_source);

pub trait Db: fcommon::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + fcommon::Db + salsa::DbWithJar<Jar> {}

// #[tracing::instrument(level = "debug")]
// #[salsa::tracked(return_ref)]
// pub fn module_from_quill_source(db: &dyn Db, source: Source) -> Dr<Vec<(PItem, Span)>> {
//     fcommon::source(db, source).bind(|contents| {
//         parse_items(
//             db,
//             source,
//             TokenIterator::new(lex(contents.contents(db).chars())),
//         )
//     })
// }

#[tracing::instrument(level = "debug")]
#[salsa::tracked(return_ref)]
pub fn module_from_quill_source(db: &dyn Db, source: Source) -> Dr<Vec<TokenTree>> {
    fcommon::source(db, source)
        .bind(|contents| lex::tokenise(source, contents.contents(db).chars()))
}
