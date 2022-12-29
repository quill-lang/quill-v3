use crate::{lex::TokenTree, parser::Parser};

impl<'db, 'a, I> Parser<'db, 'a, I> where I: Iterator<Item = TokenTree> {}
