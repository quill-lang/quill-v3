//! Feather nodes can be serialised into S-expressions.
//! This module provides functionality for both serialisation and deserialisation.

use std::fmt::Display;

use chumsky::prelude::*;
use fcommon::{Dr, Label, LabelType, Report, ReportKind, Source, Span};

use crate::{ParseError, ParseErrorReason};

/// Represents a node in a tree of S-expressions.
/// All values are stored as strings, and have no semantic meaning.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SexprNode {
    pub contents: SexprNodeContents,
    /// If this S-expression came from a file on disk, the span is stored here.
    pub span: Option<Span>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SexprNodeContents {
    Atom(String),
    List(Vec<SexprNode>),
}

/// Parses an S-expression.
/// Normally, you should use the query [`crate::SexprParser::parse_sexpr`] instead of calling this function directly.
pub(crate) fn parse_sexpr_from_string(source: Source, source_contents: &str) -> Dr<SexprNode> {
    match sexpr_parser().parse(source_contents) {
        Ok(value) => value.into(),
        Err(errs) => {
            let mut reports = Vec::new();
            for e in errs.into_iter() {
                let msg = format!(
                    "{}{}, expected {}",
                    if e.found().is_some() {
                        "unexpected token"
                    } else {
                        "unexpected end of input"
                    },
                    if let Some(label) = e.label() {
                        format!(" while parsing {label}")
                    } else {
                        String::new()
                    },
                    if e.expected().len() == 0 {
                        "something else".to_string()
                    } else {
                        e.expected()
                            .map(|expected| match expected {
                                Some(expected) => expected.to_string(),
                                None => "end of input".to_string(),
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    },
                );

                let report = Report::new(ReportKind::Error, source, e.span().start)
                    .with_message(msg)
                    .with_label(
                        Label::new(source, e.span().into(), LabelType::Error).with_message(
                            format!(
                                "unexpected {}",
                                e.found()
                                    .map(|c| format!("token {c}"))
                                    .unwrap_or_else(|| "end of input".to_string())
                            ),
                        ),
                    );

                let report = match e.reason() {
                    chumsky::error::SimpleReason::Unclosed { span, delimiter } => report
                        .with_label(
                            Label::new(source, span.into(), LabelType::Error)
                                .with_message(format!("unclosed delimiter {delimiter}")),
                        ),
                    chumsky::error::SimpleReason::Unexpected => report,
                    chumsky::error::SimpleReason::Custom(msg) => report.with_label(
                        Label::new(source, e.span().into(), LabelType::Error).with_message(msg),
                    ),
                };

                reports.push(report);
            }
            Dr::fail_many(reports)
        }
    }
}

/// Parses an S-expression.
fn sexpr_parser() -> impl Parser<char, SexprNode, Error = Simple<char>> {
    // Adapted from the JSON example <https://github.com/zesterer/chumsky/blob/master/examples/json.rs>.
    let expr = recursive(|sexpr| {
        let escape = just('\\').ignore_then(
            just('\\')
                .or(just('/'))
                .or(just('"'))
                .or(just('b').to('\x08'))
                .or(just('f').to('\x0C'))
                .or(just('n').to('\n'))
                .or(just('r').to('\r'))
                .or(just('t').to('\t')),
        );

        let string = just('"')
            .ignore_then(filter(|c| *c != '\\' && *c != '"').or(escape).repeated())
            .then_ignore(just('"'))
            .collect::<String>()
            .map(SexprNodeContents::Atom)
            .labelled("string");

        let other_atom = filter::<_, _, Simple<char>>(|c: &char| {
            !c.is_whitespace() && !matches!(c, '(' | ')' | '"')
        })
        .repeated()
        .at_least(1)
        .map(|chars| SexprNodeContents::Atom(chars.into_iter().collect()))
        .labelled("other_atom");

        let atom = string.or(other_atom);

        let list = sexpr
            .padded()
            .repeated()
            .map(SexprNodeContents::List)
            .delimited_by(just('('), just(')'))
            .labelled("list");

        list.or(atom).map_with_span(|contents, span| SexprNode {
            contents,
            span: Some(span.into()),
        })
    });
    expr.padded().then_ignore(end())
}

/// Suppose that this node is of the form `(kwd ...)`.
/// Then return `kwd`, or a parse error if this was not the case.
pub fn find_keyword_from_list(node: &SexprNode) -> Result<String, ParseError> {
    match &node.contents {
        SexprNodeContents::Atom(_) => Err(ParseError {
            span: node.span.unwrap_or_default(),
            reason: ParseErrorReason::ExpectedList,
        }),
        SexprNodeContents::List(entries) => {
            if let Some(first) = entries.first() {
                match &first.contents {
                    SexprNodeContents::Atom(kwd) => Ok(kwd.clone()),
                    SexprNodeContents::List(_) => Err(ParseError {
                        span: node.span.unwrap_or_default(),
                        reason: ParseErrorReason::ExpectedKeywordFoundList {
                            expected: "<any expression info>",
                        },
                    }),
                }
            } else {
                Err(ParseError {
                    span: node.span.unwrap_or_default(),
                    reason: ParseErrorReason::ExpectedKeywordFoundEmpty {
                        expected: "<any expression info>",
                    },
                })
            }
        }
    }
}

impl SexprNode {
    /// Converts this in-memory S-expression representation into a string.
    /// This is not the [`std::fmt::Display`] trait; we need to pass additional parameters to control
    /// pretty-printing, for instance.
    ///
    /// TODO: Better pretty-printer.
    pub fn fmt(
        &self,
        f: &mut (dyn std::fmt::Write),
        indent_levels: usize,
    ) -> Result<(), std::fmt::Error> {
        fn indent(
            f: &mut (dyn std::fmt::Write),
            indent_levels: usize,
        ) -> Result<(), std::fmt::Error> {
            for _ in 0..(4 * indent_levels) {
                write!(f, " ")?;
            }
            Ok(())
        }

        match &self.contents {
            SexprNodeContents::Atom(atom) => {
                // Unambiguously write this atom as a string.
                if atom.chars().all(|ch| !ch.is_whitespace() && ch != '"') {
                    write!(f, "{atom}")
                } else {
                    // Escape any problematic characters.
                    write!(f, "{atom:?}")
                }
            }
            SexprNodeContents::List(elements) => {
                // Depending on pretty-printing settings, we should consider indentation.
                write!(f, "(")?;
                if let Some((first, elts)) = elements.split_first() {
                    if let SexprNodeContents::Atom(_first_atom) = &first.contents {
                        first.fmt(f, indent_levels + 1)?;
                        for elt in elts {
                            write!(f, " ")?;
                            elt.fmt(f, indent_levels + 1)?;
                        }
                    } else {
                        // Indent all elements.
                        writeln!(f)?;
                        indent(f, indent_levels + 1)?;
                        first.fmt(f, indent_levels + 1)?;
                        for elt in elts {
                            writeln!(f)?;
                            indent(f, indent_levels + 1)?;
                            elt.fmt(f, indent_levels + 1)?;
                        }
                        writeln!(f)?;
                        indent(f, indent_levels)?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

impl Display for SexprNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt(f, 0)
    }
}

#[cfg(test)]
mod tests {
    use crate::s_expr::*;

    #[test]
    fn atom() {
        let value = sexpr_parser().parse("123").unwrap();
        let expected = SexprNode {
            contents: SexprNodeContents::Atom("123".to_string()),
            span: Some((0..3).into()),
        };
        assert_eq!(value, expected);
    }

    #[test]
    fn list() {
        let value = sexpr_parser().parse("(a b c)").unwrap();
        let expected = SexprNode {
            contents: SexprNodeContents::List(vec![
                SexprNode {
                    contents: SexprNodeContents::Atom("a".to_string()),
                    span: Some((1..2).into()),
                },
                SexprNode {
                    contents: SexprNodeContents::Atom("b".to_string()),
                    span: Some((3..4).into()),
                },
                SexprNode {
                    contents: SexprNodeContents::Atom("c".to_string()),
                    span: Some((5..6).into()),
                },
            ]),
            span: Some((0..7).into()),
        };
        assert_eq!(value, expected);
    }

    #[test]
    fn string() {
        let value = sexpr_parser()
            .parse(r#"("Hello, world!" "escaping\\\"")"#)
            .unwrap();
        let expected = SexprNode {
            contents: SexprNodeContents::List(vec![
                SexprNode {
                    contents: SexprNodeContents::Atom("Hello, world!".to_string()),
                    span: Some((1..16).into()),
                },
                SexprNode {
                    contents: SexprNodeContents::Atom("escaping\\\"".to_string()),
                    span: Some((17..31).into()),
                },
            ]),
            span: Some((0..32).into()),
        };
        assert_eq!(value, expected);
    }

    #[test]
    fn hierarchy() {
        let value = sexpr_parser().parse("(a b (c d) ((e) f))").unwrap();
        let expected = SexprNode {
            contents: SexprNodeContents::List(vec![
                SexprNode {
                    contents: SexprNodeContents::Atom("a".to_string()),
                    span: Some((1..2).into()),
                },
                SexprNode {
                    contents: SexprNodeContents::Atom("b".to_string()),
                    span: Some((3..4).into()),
                },
                SexprNode {
                    contents: SexprNodeContents::List(vec![
                        SexprNode {
                            contents: SexprNodeContents::Atom("c".to_string()),
                            span: Some((6..7).into()),
                        },
                        SexprNode {
                            contents: SexprNodeContents::Atom("d".to_string()),
                            span: Some((8..9).into()),
                        },
                    ]),
                    span: Some((5..10).into()),
                },
                SexprNode {
                    contents: SexprNodeContents::List(vec![
                        SexprNode {
                            contents: SexprNodeContents::List(vec![SexprNode {
                                contents: SexprNodeContents::Atom("e".to_string()),
                                span: Some((13..14).into()),
                            }]),
                            span: Some((12..15).into()),
                        },
                        SexprNode {
                            contents: SexprNodeContents::Atom("f".to_string()),
                            span: Some((16..17).into()),
                        },
                    ]),
                    span: Some((11..18).into()),
                },
            ]),
            span: Some((0..19).into()),
        };
        assert_eq!(value, expected);
    }
}
