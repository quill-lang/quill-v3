use fcommon::{Span, Spanned, Str};
use fkernel::{
    basic::{Name,  WithProvenance},
    multiplicity::ParameterOwnership,
    result::Dr,
};

use crate::{
    expr::PExpression,
    lex::{Bracket, ReservedSymbol, TokenTree},
    parser::Parser,
};

#[derive(Debug, PartialEq, Eq)]
pub struct PField {
    /// The name given to the field.
    pub name: Name,
    /// The type of the field.
    pub ty: PExpression,
    /// The multiplicity for which the field is stored.
    /// If absent, it is inferred by the elaborator.
    pub ownership: Option<(ParameterOwnership, Span)>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct PVariant {
    /// The name of the variant.
    pub name: Name,
    /// The fields of the variant.
    pub fields: Vec<PField>,
    /// If the type of this variant was given explicitly, it is stored here.
    pub ty: Option<PExpression>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct PInductive {
    pub inductive_token: Span,
    /// The variants of this inductively defined type.
    pub variants: Vec<PVariant>,
}

impl Spanned for PInductive {
    fn span(&self) -> Span {
        self.inductive_token
    }
}

impl<'db, 'a, I> Parser<'db, 'a, I>
where
    I: Iterator<Item = TokenTree>,
{
    /// Parse a single field of an inductive variant.
    fn parse_inductive_field(&mut self, min_indent: usize, indent: usize) -> Dr<PField> {
        let ownership = self.parse_ownership();
        self.require_lexical().bind(|(name, name_span)| {
            self.require_reserved(ReservedSymbol::Colon).bind(|_| {
                self.parse_expr(min_indent, indent).map(|ty| PField {
                    name: Name(WithProvenance::new_with_provenance(
                        self.provenance(name_span),
                        Str::new(self.config().db, name),
                    )),
                    ty,
                    ownership,
                })
            })
        })
    }

    /// Parse the fields of an inductive variant.
    fn parse_inductive_fields(&mut self, min_indent: usize) -> Dr<Vec<PField>> {
        let mut fields = Vec::new();
        while self.peek().is_some() {
            let newline = self.require_newline();
            // Parse a field.
            if self.peek().is_some() {
                fields.push(newline.bind(|(_, newline_indent)| {
                    self.parse_inductive_field(min_indent, newline_indent)
                }));
            } else {
                break;
            }
        }

        Dr::sequence(fields).bind(|fields| self.assert_end("inductive variant").map(|()| fields))
    }

    /// Parse a variant of an inductive.
    fn parse_inductive_variant(&mut self, min_indent: usize, indent: usize) -> Dr<PVariant> {
        self.require_lexical().bind(|(name, name_span)| {
            // After the name, we optionally have a block of fields delimited with brace brackets,
            // and optionally the result type.
            let fields = if let Some(TokenTree::Block {
                bracket: Bracket::Brace,
                ..
            }) = self.peek()
            {
                if let Some(TokenTree::Block {
                    open,
                    close,
                    contents,
                    ..
                }) = self.next()
                {
                    self.with_vec(open, close, contents)
                        .parse_inductive_fields(0)
                } else {
                    unreachable!()
                }
            } else {
                Dr::ok(Vec::new())
            };

            fields.bind(|fields| {
                let ty = if let Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Arrow,
                    ..
                }) = self.peek()
                {
                    self.next();
                    self.parse_expr(min_indent, indent).map(Some)
                } else {
                    Dr::ok(None)
                };

                ty.map(|ty| PVariant {
                    name: Name(WithProvenance::new_with_provenance(
                        self.provenance(name_span),
                        Str::new(self.config().db, name),
                    )),
                    fields,
                    ty,
                })
            })
        })
    }

    /// Assuming that the next token is `inductive`, parse a `inductive` expression.
    fn parse_inductive(&mut self, min_indent: usize, indent: usize) -> Dr<PInductive> {
        self.require_reserved(ReservedSymbol::Inductive)
            .bind(|inductive_token| {
                let mut variants = Vec::new();
                while let Some(TokenTree::Newline {
                    indent: newline_indent,
                    ..
                }) = self.peek()
                {
                    let newline_indent = *newline_indent;
                    if newline_indent > indent {
                        // This is a variant.
                        self.next();
                        variants.push(self.parse_inductive_variant(min_indent, newline_indent));
                    } else {
                        break;
                    }
                }

                Dr::sequence(variants).map(|variants| PInductive {
                    inductive_token,
                    variants,
                })
            })
    }

    pub fn parse_inductive_expr(&mut self, min_indent: usize, indent: usize) -> Dr<PExpression> {
        self.parse_inductive(min_indent, indent)
            .map(PExpression::Inductive)
    }
}
