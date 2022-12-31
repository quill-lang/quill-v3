//! We parse expressions in two stages.
//! We create an explicit recursive descent parser for expressions themselves,
//! and use a Pratt parser for the "Pratt expressions", a specific kind of sub-expression
//! that deals only with prefix, infix, and postfix operators, as well as function application.

use fcommon::{Label, LabelType, Report, ReportKind, Span, Spanned, Str};
use fexpr::{
    basic::{Name, Provenance, QualifiedName, WithProvenance},
    expr::BinderAnnotation,
    message,
    multiplicity::ParameterOwnership,
    result::Dr,
};

use crate::{
    lex::{Bracket, OperatorInfo, ReservedSymbol, TokenTree},
    parser::Parser,
};

/// A parsed universe.
#[derive(Debug, PartialEq, Eq)]
pub enum PUniverse {
    /// A universe variable.
    Variable(Name<Provenance>),
}

/// A parsed `let` binder.
/// A single `let` expression may contain multiple such binders.
#[derive(Debug, PartialEq, Eq)]
pub struct PLetBinder {
    /// The name given to the bound variable.
    pub name: Name<Provenance>,
    /// The type, if explicitly given.
    /// If it is not given, it must be inferred by the elaborator.
    pub ty: Option<PExpression>,
    /// The value to assign to the new bound variable.
    pub to_assign: PExpression,
}

/// A parsed lambda binder.
#[derive(Debug, PartialEq, Eq)]
pub struct PLambdaBinder {
    /// The name given to the bound variable.
    pub name: Name<Provenance>,
    /// The annotation on the associated lambda abstraction.
    pub annotation: BinderAnnotation,
    /// If brackets were given explicitly, their spans are here.
    pub brackets: Option<(Span, Span)>,
    /// The ownership annotation on the bound variable, if explicitly given.
    /// If absent, it is inferred by the elaborator.
    pub ownership: Option<(ParameterOwnership, Span)>,
    /// The type, if explicitly given.
    /// If it is not given, it must be inferred by the elaborator.
    pub ty: Option<PExpression>,
}

/// A parsed function type.
#[derive(Debug, PartialEq, Eq)]
pub struct PFunctionBinder {
    /// The name given to the bound variable, if present.
    pub name: Option<Name<Provenance>>,
    /// The annotation on the associated lambda abstraction.
    pub annotation: BinderAnnotation,
    /// If brackets were given explicitly, their spans are here.
    pub brackets: Option<(Span, Span)>,
    /// The ownership annotation on the bound variable, if explicitly given.
    /// If absent, it is inferred by the elaborator.
    pub ownership: Option<(ParameterOwnership, Span)>,
    /// The type of the bound variable.
    pub ty: Box<PExpression>,
}

/// A parsed expression.
#[derive(Debug, PartialEq, Eq)]
pub enum PExpression {
    /// A local variable or an instantiated constant.
    Variable {
        name: QualifiedName<Provenance>,
        /// If present, the spans are the opening and closing brackets,
        /// and the universes are the universe parameters.
        /// This is somewhat like Rust's turbofish syntax,
        /// but this is used for universes, not type parameters.
        universe_ascription: Option<(Span, Vec<PUniverse>, Span)>,
    },
    Apply {
        function: Box<PExpression>,
        argument: Box<PExpression>,
    },
    Let {
        let_token: Span,
        binders: Vec<PLetBinder>,
        body: Box<PExpression>,
    },
    Lambda {
        fn_token: Span,
        binders: Vec<PLambdaBinder>,
        result: Box<PExpression>,
    },
    FunctionType {
        binder: PFunctionBinder,
        arrow_token: Span,
        result: Box<PExpression>,
    },
    Sort {
        span: Span,
        universe: PUniverse,
    },
    StaticRegion(Span),
    Region(Span),
    RegionT(Span),
    Type {
        span: Span,
        /// If this was present, the expression was `Type::{u}` for some `u`.
        /// The spans are the opening and closing brackets.
        /// Otherwise, the expression was just `Type`.
        universe: Option<(Span, PUniverse, Span)>,
    },
}

impl Spanned for PExpression {
    fn span(&self) -> Span {
        todo!()
    }
}

/// A piece of syntax in an expression constructed from (relatively) few tokens.
/// Easily parsable.
enum SmallExpression {
    QualifiedName {
        /// A list of name segments, their spans, and the spans of the following `::` token.
        segments: Vec<(String, Span, Span)>,
        final_segment: String,
        final_span: Span,
        /// If present, the spans are the opening and closing brackets,
        /// and the universes are the universe parameters.
        /// This is somewhat like Rust's turbofish syntax,
        /// but this is used for universes, not type parameters.
        universe_ascription: Option<(Span, Vec<PUniverse>, Span)>,
    },
    Operator {
        text: String,
        info: OperatorInfo,
        span: Span,
    },
    PExpression(PExpression),
}

impl<'db, 'a, I> Parser<'db, 'a, I>
where
    I: Iterator<Item = TokenTree>,
{
    /// Parse a universe, and then the end of the stream.
    fn parse_universe_end(&mut self) -> Dr<PUniverse> {
        self.require_lexical().bind(|(name, span)| {
            self.assert_end().map(|()| {
                PUniverse::Variable(Name(WithProvenance::new_with_provenance(
                    self.provenance(span),
                    Str::new(self.config().db, name),
                )))
            })
        })
    }

    /// Parse a sequence of comma-separated universes, and then the end of the stream.
    fn parse_universes_end(&mut self) -> Dr<Vec<PUniverse>> {
        todo!()
    }

    fn parse_qualified_name(&mut self) -> Dr<SmallExpression> {
        if let Some(TokenTree::Lexical { text, span }) = self.next() {
            if let Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Scope,
                span: scope_span,
            }) = self.peek()
            {
                let scope_span = *scope_span;
                // Consume the `::` token.
                self.next();
                if let Some(TokenTree::Block {
                    bracket: Bracket::Brace,
                    ..
                }) = self.peek()
                {
                    // This is the end of the qualified name, with a universe ascription.
                    // Consume the block.
                    if let Some(TokenTree::Block {
                        bracket: Bracket::Brace,
                        open,
                        close,
                        contents,
                    }) = self.next()
                    {
                        self.with_vec(open, close, contents)
                            .parse_universes_end()
                            .map(|universe_ascription| SmallExpression::QualifiedName {
                                segments: Vec::new(),
                                final_segment: text,
                                final_span: span,
                                universe_ascription: Some((open, universe_ascription, close)),
                            })
                    } else {
                        unreachable!()
                    }
                } else {
                    // Consume the tail qualified name.
                    self.parse_qualified_name().map(|mut tail| {
                        if let SmallExpression::QualifiedName { segments, .. } = &mut tail {
                            segments.insert(0, (text, span, scope_span));
                            tail
                        } else {
                            unreachable!()
                        }
                    })
                }
            } else {
                // This name has only one segment.
                Dr::ok(SmallExpression::QualifiedName {
                    segments: Vec::new(),
                    final_segment: text,
                    final_span: span,
                    universe_ascription: None,
                })
            }
        } else {
            todo!()
        }
    }

    /// Parse all token trees that could be part of a Pratt expression.
    fn parse_pratt_expr_terms(&mut self, mut indent: usize) -> Dr<Vec<SmallExpression>> {
        let original_indent = indent;
        let mut result = Vec::new();
        loop {
            match self.peek() {
                Some(TokenTree::Lexical { .. }) => result.push(self.parse_qualified_name()),
                Some(TokenTree::Operator { .. }) => {
                    if let Some(TokenTree::Operator { text, info, span }) = self.next() {
                        result.push(Dr::ok(SmallExpression::Operator { text, info, span }));
                    } else {
                        unreachable!()
                    }
                }
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Sort,
                    span,
                }) => {
                    let span = *span;
                    self.next();
                    let required = self.require_reserved(ReservedSymbol::Scope);
                    if let Some(TokenTree::Block {
                        bracket: Bracket::Brace,
                        open,
                        close,
                        contents,
                    }) = self.next()
                    {
                        result.push(required.bind(|_| {
                            self.with_vec(open, close, contents)
                                .parse_universe_end()
                                .map(|universe| {
                                    SmallExpression::PExpression(PExpression::Sort {
                                        span,
                                        universe,
                                    })
                                })
                        }));
                    } else {
                        todo!()
                    }
                }
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Type,
                    span,
                }) => {
                    let span = *span;
                    self.next();
                    if let Some(TokenTree::Block {
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
                            result.push(
                                self.with_vec(open, close, contents)
                                    .parse_universe_end()
                                    .map(|universe| {
                                        SmallExpression::PExpression(PExpression::Type {
                                            span,
                                            universe: Some((open, universe, close)),
                                        })
                                    }),
                            );
                        } else {
                            unreachable!()
                        }
                    } else {
                        result.push(Dr::ok(SmallExpression::PExpression(PExpression::Type {
                            span,
                            universe: None,
                        })));
                    }
                }
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Static,
                    span,
                }) => {
                    let span = *span;
                    self.next();
                    result.push(Dr::ok(SmallExpression::PExpression(
                        PExpression::StaticRegion(span),
                    )));
                }
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Region,
                    span,
                }) => {
                    let span = *span;
                    self.next();
                    result.push(Dr::ok(SmallExpression::PExpression(PExpression::Region(
                        span,
                    ))));
                }
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::RegionT,
                    span,
                }) => {
                    let span = *span;
                    self.next();
                    result.push(Dr::ok(SmallExpression::PExpression(PExpression::RegionT(
                        span,
                    ))));
                }
                Some(TokenTree::Block {
                    bracket: Bracket::Paren,
                    ..
                }) => {
                    if let Some(TokenTree::Block {
                        open,
                        close,
                        contents,
                        ..
                    }) = self.next()
                    {
                        let mut inner = self.with_vec(open, close, contents);
                        result.push(inner.parse_expr(indent, indent).bind(|expr| {
                            inner
                                .assert_end()
                                .map(|()| SmallExpression::PExpression(expr))
                        }));
                    } else {
                        unreachable!()
                    }
                }
                Some(TokenTree::Newline {
                    indent: newline_indent,
                    ..
                }) => {
                    if *newline_indent > original_indent {
                        indent = *newline_indent;
                        self.next();
                    } else {
                        return Dr::sequence(result);
                    }
                }
                _ => return Dr::sequence(result),
            }
        }
    }

    /// Parses a Pratt expression.
    /// TODO: Write this complete function. For now, we just parse function applications.
    pub fn parse_pratt_expr(&mut self, indent: usize) -> Dr<PExpression> {
        self.parse_pratt_expr_terms(indent).bind(|terms| {
            let result = terms
                .into_iter()
                .map(|small_expr| match small_expr {
                    SmallExpression::QualifiedName {
                        segments,
                        final_segment,
                        final_span,
                        universe_ascription,
                    } => PExpression::Variable {
                        name: QualifiedName(WithProvenance::new_with_provenance(
                            self.provenance(match segments.first() {
                                Some((_, first_span, _)) => Span {
                                    start: first_span.start,
                                    end: final_span.end,
                                },
                                None => final_span,
                            }),
                            segments
                                .into_iter()
                                .map(|(name, name_span, _)| {
                                    Name(WithProvenance::new_with_provenance(
                                        self.provenance(name_span),
                                        Str::new(self.config().db, name),
                                    ))
                                })
                                .chain(std::iter::once(Name(WithProvenance::new_with_provenance(
                                    self.provenance(final_span),
                                    Str::new(self.config().db, final_segment),
                                ))))
                                .collect(),
                        )),
                        universe_ascription,
                    },
                    SmallExpression::Operator { .. } => todo!(),
                    SmallExpression::PExpression(pexpr) => pexpr,
                })
                .reduce(|acc, expr| PExpression::Apply {
                    function: Box::new(acc),
                    argument: Box::new(expr),
                });

            // TODO: Once we have actual Pratt parsing, we should make some report messages for using things like
            // `let` or `fn` in an incorrect position, i.e. not parsed by `parse_expr`.

            let source = self.config().source;
            match result {
                Some(result) => Dr::ok(result),
                None => match self.peek() {
                    Some(tt) => Dr::fail(
                        Report::new(ReportKind::Error, source, tt.span().start)
                            .with_message("expected an expression".into())
                            .with_label(
                                Label::new(source, tt.span(), LabelType::Error).with_message(
                                    message!["expected an expression but found ", tt],
                                ),
                            ),
                    ),
                    None => match self.block_brackets() {
                        Some((open, close)) => Dr::fail(
                            Report::new(ReportKind::Error, source, close.start)
                                .with_message("expected an expression".into())
                                .with_label(
                                    Label::new(source, close, LabelType::Error).with_message(
                                        "expected an expression before the end of this block"
                                            .into(),
                                    ),
                                )
                                .with_label(
                                    Label::new(source, open, LabelType::Note)
                                        .with_message("the block started here".into()),
                                ),
                        ),
                        None => todo!(),
                    },
                },
            }
        })
    }

    /// If the next token was an ownership label (`erased`, `owned`, `copyable`), consume and return it.
    fn parse_ownership(&mut self) -> Option<(ParameterOwnership, Span)> {
        match self.peek() {
            Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Erased,
                span,
            }) => {
                let span = *span;
                self.next();
                Some((ParameterOwnership::PZero, span))
            }
            Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Owned,
                span,
            }) => {
                let span = *span;
                self.next();
                Some((ParameterOwnership::POwned, span))
            }
            Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Copyable,
                span,
            }) => {
                let span = *span;
                self.next();
                Some((ParameterOwnership::PCopyable, span))
            }
            _ => None,
        }
    }

    fn parse_let_binder(&mut self, min_indent: usize, indent: usize) -> Dr<PLetBinder> {
        self.require_lexical().bind(|(name, name_span)| {
            // We may have a type ascription with `:`.
            if let Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Colon,
                ..
            }) = self.peek()
            {
                // We have a type ascription.
                self.parse_expr(min_indent, indent).bind(|ty| {
                    self.require_reserved(ReservedSymbol::Assign).bind(|_| {
                        self.parse_expr(min_indent, indent)
                            .map(|to_assign| PLetBinder {
                                name: Name(WithProvenance::new_with_provenance(
                                    self.provenance(name_span),
                                    Str::new(self.config().db, name),
                                )),
                                ty: Some(ty),
                                to_assign,
                            })
                    })
                })
            } else {
                self.require_reserved(ReservedSymbol::Assign).bind(|_| {
                    self.parse_expr(min_indent, indent)
                        .map(|to_assign| PLetBinder {
                            name: Name(WithProvenance::new_with_provenance(
                                self.provenance(name_span),
                                Str::new(self.config().db, name),
                            )),
                            ty: None,
                            to_assign,
                        })
                })
            }
        })
    }

    /// Assuming that the next token is a `let`, parse a `let` expression.
    fn parse_let_expr(&mut self, min_indent: usize, indent: usize) -> Dr<PExpression> {
        self.require_reserved(ReservedSymbol::Let)
            .bind(|let_token| {
                // Allow a new line before the first binder.
                let first_binder = if let Some(TokenTree::Newline { .. }) = self.peek() {
                    Dr::ok(None)
                } else {
                    self.parse_let_binder(min_indent, indent + 4).map(Some)
                };

                first_binder.bind(|binder| {
                    // Parse any extra binders.
                    let mut more_binders = Vec::new();
                    while let Some(TokenTree::Newline {
                        indent: newline_indent,
                        ..
                    }) = self.peek()
                    {
                        let newline_indent = *newline_indent;
                        if newline_indent == indent + 4 {
                            // This is another binder.
                            self.next();
                            more_binders.push(self.parse_let_binder(min_indent, newline_indent));
                        } else {
                            break;
                        }
                    }
                    Dr::sequence(more_binders).bind(|mut binders| {
                        if let Some(binder) = binder {
                            binders.insert(0, binder)
                        };
                        if binders.is_empty() {
                            Dr::fail(
                                Report::new(
                                    ReportKind::Error,
                                    self.config().source,
                                    let_token.start,
                                )
                                .with_message(message![
                                    ReservedSymbol::Let,
                                    " expression bound no variables"
                                ])
                                .with_label(
                                    Label::new(self.config().source, let_token, LabelType::Error)
                                        .with_message(message![
                                            "this ",
                                            ReservedSymbol::Let,
                                            " expression bound no variables"
                                        ]),
                                ),
                            )
                        } else {
                            self.require_newline()
                                .bind(|(newline_span, newline_indent)| {
                                    if newline_indent != indent {
                                        Dr::fail(
                                            Report::new(
                                                ReportKind::Error,
                                                self.config().source,
                                                newline_span.start,
                                            )
                                            .with_message("new line had incorrect indent".into())
                                            .with_label(
                                                Label::new(
                                                    self.config().source,
                                                    newline_span,
                                                    LabelType::Error,
                                                )
                                                .with_message(message![
                                                    "line had ",
                                                    newline_indent.to_string(),
                                                    " spaces of indent, but expected ",
                                                    indent.to_string(),
                                                    " spaces"
                                                ]),
                                            )
                                            .with_note(message![
                                                "to add another variable to the ",
                                                ReservedSymbol::Let,
                                                " expression, use ",
                                                (indent + 4).to_string(),
                                                " spaces"
                                            ]),
                                        )
                                    } else {
                                        self.parse_expr(min_indent, indent).map(|body| {
                                            PExpression::Let {
                                                let_token,
                                                binders,
                                                body: Box::new(body),
                                            }
                                        })
                                    }
                                })
                        }
                    })
                })
            })
    }

    /// Parses a single lambda abstraction binder.
    fn parse_lambda_binder(&mut self, indent: usize, fn_token: Span) -> Dr<PLambdaBinder> {
        match self.next() {
            // A single lexical token is interpreted as a binder with no explicit type, using
            // the explicit binder annotation.
            Some(TokenTree::Lexical { text, span }) => Dr::ok(PLambdaBinder {
                name: Name(WithProvenance::new_with_provenance(
                    self.provenance(span),
                    Str::new(self.config().db, text),
                )),
                annotation: BinderAnnotation::Explicit,
                brackets: None,
                ownership: None,
                ty: None,
            }),
            Some(TokenTree::Block {
                bracket,
                open,
                close,
                contents,
            }) => {
                // This is either a binder of the form `(ownership? name)`, using any bracket style, or
                // `(ownership? name : type)`, again using any bracket style.
                let mut inner = self.with_vec(open, close, contents);
                // First, parse all of the ownership symbols.
                let ownership = inner.parse_ownership();
                if inner.one_tree_left() {
                    // This is a binder which does not explicitly declare the type of the parameter.
                    match inner.next() {
                        Some(TokenTree::Lexical { text, span }) => Dr::ok(PLambdaBinder {
                            name: Name(WithProvenance::new_with_provenance(
                                inner.provenance(span),
                                Str::new(inner.config().db, text),
                            )),
                            annotation: bracket.into(),
                            brackets: Some((open, close)),
                            ownership,
                            ty: None,
                        }),
                        _ => todo!(),
                    }
                } else {
                    // This is a binder which explicitly declares its type.
                    // The form is `name : type`.
                    let name = if let Some(TokenTree::Lexical { text, span }) = inner.next() {
                        Name(WithProvenance::new_with_provenance(
                            inner.provenance(span),
                            Str::new(inner.config().db, text),
                        ))
                    } else {
                        todo!()
                    };
                    inner
                        .require_reserved(ReservedSymbol::Colon)
                        .bind(|_| inner.parse_expr(indent, indent))
                        .bind(|ty| {
                            inner.assert_end().map(|()| PLambdaBinder {
                                name,
                                annotation: bracket.into(),
                                brackets: Some((open, close)),
                                ownership,
                                ty: Some(ty),
                            })
                        })
                }
            }
            Some(tt) => Dr::fail(
                Report::new(ReportKind::Error, self.config().source, tt.span().start)
                    .with_message(message!["expected a parameter name, but found ", &tt])
                    .with_label(
                        Label::new(self.config().source, tt.span(), LabelType::Error)
                            .with_message("expected a parameter name".into()),
                    )
                    .with_label(
                        Label::new(self.config().source, fn_token, LabelType::Note)
                            .with_message("while parsing this function".into()),
                    )
                    .with_note(
                        "use '=>' to end the sequence of parameters and begin the function body"
                            .into(),
                    ),
            ),
            None => todo!(),
        }
    }

    /// Assuming that the next token is a `fn`, parse a `fn <binders> => e` expression.
    fn parse_fn_expr(&mut self, min_indent: usize, indent: usize) -> Dr<PExpression> {
        let fn_token = self.next().unwrap().span();

        // Parse one or more binders.
        let mut binders = Vec::new();
        loop {
            match self.peek() {
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::DoubleArrow,
                    ..
                }) => {
                    self.next();
                    break;
                }
                _ => {
                    let binder = self.parse_lambda_binder(indent, fn_token);
                    let errored = binder.errored();
                    binders.push(binder);
                    if errored {
                        break;
                    }
                }
            }
        }

        Dr::sequence(binders).bind(|binders| {
            // TODO: Check that there is at least one binder?
            self.parse_expr(min_indent, indent)
                .map(|result| PExpression::Lambda {
                    fn_token,
                    binders,
                    result: Box::new(result),
                })
        })
    }

    /// Parses syntax of the form `ownership? name : type` or `ownership? type`.
    fn parse_function_binder(
        &mut self,
        indent: usize,
        annotation: BinderAnnotation,
        brackets: Option<(Span, Span)>,
    ) -> Dr<PFunctionBinder> {
        // Parse an ownership token if one exists.
        let ownership = self.parse_ownership();

        // Look ahead two token trees to check if it is a `:` token.
        let tt = if let Some(tt) = self.next() {
            tt
        } else {
            todo!("binders should be nonempty")
        };

        if let Some(TokenTree::Reserved {
            symbol: ReservedSymbol::Colon,
            ..
        }) = self.peek()
        {
            // This is syntax of the form `name : type`.
            // `tt` is a lexical token, representing the name of the function.
            // Consume the token.
            self.next();
            if let TokenTree::Lexical { text, span } = tt {
                // Parse the type of the parameter.
                self.parse_expr(indent, indent).bind(|ty| {
                    self.assert_end().map(|()| PFunctionBinder {
                        name: Some(Name(WithProvenance::new_with_provenance(
                            self.provenance(span),
                            Str::new(self.config().db, text),
                        ))),
                        annotation,
                        brackets,
                        ownership,
                        ty: Box::new(ty),
                    })
                })
            } else {
                todo!()
            }
        } else {
            // This is syntax of the form `type`.
            self.push(tt);
            self.parse_expr(indent, indent).bind(|ty| {
                self.assert_end().map(|()| PFunctionBinder {
                    name: None,
                    annotation,
                    brackets,
                    ownership,
                    ty: Box::new(ty),
                })
            })
        }
    }

    /// An expression is:
    /// - a `let` expression;
    /// - a lambda, written `fn <binders> => e`;
    /// - a function type, written `<binder> -> e`; or
    /// - a Pratt expression.
    /// The indent parameter gives the indent level of the surrounding environment.
    /// New line tokens are consumed if their indent is greater than the environment's indent level.
    /// TODO: Check if any newlines are less indented than `min_indent`.
    pub fn parse_expr(&mut self, min_indent: usize, indent: usize) -> Dr<PExpression> {
        let result = match self.peek() {
            Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Let,
                ..
            }) => self.parse_let_expr(min_indent, indent),
            Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Fn,
                ..
            }) => self.parse_fn_expr(min_indent, indent),
            Some(TokenTree::Block { .. }) => {
                // We can check if this is a function type by peeking at the token tree after this block.
                let block = self.next().unwrap();

                if let Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Arrow,
                    span,
                }) = self.peek()
                {
                    let arrow_token = *span;
                    // This is a function type.
                    // Consume the arrow token.
                    self.next();
                    if let TokenTree::Block {
                        bracket,
                        open,
                        close,
                        contents,
                    } = block
                    {
                        let mut inner = self.with_vec(open, close, contents);
                        inner
                            .parse_function_binder(indent, bracket.into(), Some((open, close)))
                            .bind(|binder| {
                                self.parse_expr(indent, indent).map(|result| {
                                    PExpression::FunctionType {
                                        binder,
                                        arrow_token,
                                        result: Box::new(result),
                                    }
                                })
                            })
                    } else {
                        unreachable!()
                    }
                } else {
                    // This wasn't a function type.
                    // Push the block back, and fall back to the Pratt expression parser.
                    self.push(block);
                    self.parse_pratt_expr(indent)
                }
            }
            Some(TokenTree::Newline {
                indent: newline_indent,
                ..
            }) => {
                let newline_indent = *newline_indent;
                self.next();
                self.parse_expr(min_indent, newline_indent)
            }
            _ => self.parse_pratt_expr(indent),
        };

        // After we parse the initial expression, it's possible that we have an arrow token `->`
        // defining a function type.
        result.bind(|expr| {
            if let Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Arrow,
                span,
            }) = self.peek()
            {
                let arrow_token = *span;
                self.next();
                self.parse_expr(min_indent, indent)
                    .map(|result| PExpression::FunctionType {
                        binder: PFunctionBinder {
                            name: None,
                            annotation: BinderAnnotation::Explicit,
                            brackets: None,
                            ownership: None,
                            ty: Box::new(expr),
                        },
                        arrow_token,
                        result: Box::new(result),
                    })
            } else {
                Dr::ok(expr)
            }
        })
    }
}
