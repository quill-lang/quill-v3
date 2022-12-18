#![feature(trait_upcasting)]

//! A parser for Quill files. Since syntax can be extended, we cannot easily separate the parsing
//! phase on a per-file scale like many other parsers do. Instead, we must parse each *item*
//! separately, and when new notation is introduced, add this to the parser that will be used with
//! subsequent items.

mod parse;
mod pre_lex;

pub use parse::*;
use pre_lex::*;

use fcommon::{Dr, Source, Span};

#[salsa::jar(db = Db)]
pub struct Jar(module_from_quill_source);

pub trait Db: fcommon::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + fcommon::Db + salsa::DbWithJar<Jar> {}

#[tracing::instrument(level = "debug")]
#[salsa::tracked(return_ref)]
pub fn module_from_quill_source(db: &dyn Db, source: Source) -> Dr<Vec<(PItem, Span)>> {
    fcommon::source(db, source).bind(|contents| {
        parse_items(
            db,
            source,
            TokenIterator::new(pre_lex(contents.contents(db).chars())),
        )
    })
}
