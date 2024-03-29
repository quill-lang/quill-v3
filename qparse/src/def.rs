use fcommon::{Label, LabelType, Report, ReportKind, Spanned, Str};
use fkernel::{
    basic::{Name, WithProvenance},
    message,
    result::Dr,
};

use crate::{
    expr::{PExpression, PLambdaBinder},
    inductive::PInductive,
    lex::{ReservedSymbol, TokenTree},
    parser::Parser,
};

/// A parsed lambda binder.
#[derive(Debug, PartialEq, Eq)]
pub struct PDefinition {
    /// The name given to the definition.
    pub name: Name,
    /// The type, if explicitly given.
    /// If it is not given, it must be inferred by the elaborator.
    pub ty: Option<PExpression>,
    /// The body of the definition.
    pub body: PExpression,
}

impl PDefinition {
    /// If this definition defines an inductive type, return the sequence of global parameters and the inductive being defined.
    pub fn as_inductive(&self) -> Option<(&[PLambdaBinder], &PInductive)> {
        // Check if we're actually elaborating a definition, or we're elaborating an inductive.
        if let PExpression::Lambda {
            binders, result, ..
        } = &self.body
        {
            if let PExpression::Inductive(inductive) = &**result {
                Some((binders, inductive))
            } else {
                None
            }
        } else if let PExpression::Inductive(inductive) = &self.body {
            Some((&[], inductive))
        } else {
            None
        }
    }
}

impl<'db, 'a, I> Parser<'db, 'a, I>
where
    I: Iterator<Item = TokenTree>,
{
    /// Parses a definition.
    /// TODO: Check that after a definition is a newline with indent level zero, or nothing.
    pub fn parse_def(&mut self) -> Dr<PDefinition> {
        self.require_lexical().bind(|(name, name_span)| {
            // Either this name is followed by a type ascription with `:`,
            // or an assignment with `=`.
            match self.next() {
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Colon,
                    ..
                }) => {
                    // We first need to parse a type ascription.
                    self.parse_expr(0, 0).bind(|ty| {
                        self.require_reserved(ReservedSymbol::Assign).bind(|_| {
                            // Parse the body of the definition.
                            self.parse_expr(0, 0).map(|body| PDefinition {
                                name: Name(WithProvenance::new(
                                    self.provenance(name_span),
                                    Str::new(self.config().db, name),
                                )),
                                ty: Some(ty),
                                body,
                            })
                        })
                    })
                }
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Assign,
                    ..
                }) => {
                    // Parse the body of the definition.
                    self.parse_expr(0, 0).map(|body| PDefinition {
                        name: Name(WithProvenance::new(
                            self.provenance(name_span),
                            Str::new(self.config().db, name),
                        )),
                        ty: None,
                        body,
                    })
                }
                Some(tt) => Dr::fail(
                    Report::new(ReportKind::Error, self.config().source, tt.span().start)
                        .with_message(message![
                            "expected ",
                            ReservedSymbol::Colon,
                            " or ",
                            ReservedSymbol::Assign,
                            ", found ",
                            &tt
                        ])
                        .with_label(
                            Label::new(self.config().source, tt.span(), LabelType::Error)
                                .with_message(message!["unexpected ", &tt, " found here"]),
                        ),
                ),
                _ => todo!(),
            }
        })
    }

    pub fn parse_defs(&mut self) -> Dr<Vec<PDefinition>> {
        let mut result = Vec::new();
        let mut reports = Vec::new();
        while self.peek().is_some() {
            // Consume any extra new lines.
            while matches!(self.peek(), Some(TokenTree::Newline { .. })) {
                self.next();
            }

            match self.parse_def().destructure() {
                (Some(def), more_reports) => {
                    result.push(def);
                    reports.extend(more_reports);
                }
                (None, more_reports) => {
                    reports.extend(more_reports);
                }
            }
            if self.peek().is_none() {
                break;
            }

            if reports
                .iter()
                .any(|report| report.kind == ReportKind::Error)
            {
                // If we errored, just ignore everything until the next newline.
                while !matches!(self.peek(), Some(TokenTree::Newline { .. })) {
                    self.next();
                }
            }

            let (_, more_reports) = self.require_newline().destructure();
            reports.extend(more_reports);
        }
        Dr::ok_with_many(result, reports)
            .bind(|result| self.assert_end("definitions").map(|_| result))
    }
}
