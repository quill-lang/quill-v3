use std::{
    collections::BTreeMap,
    fmt::{Debug, Display},
};

use fcommon::{Dr, Label, LabelType, Report, ReportKind, Source, SourceSpan, Span, Str};
use fexpr::{
    basic::{Name, Provenance, QualifiedName, WithProvenance},
    expr::BinderAnnotation,
};

use crate::{lex::TokenTree, Db};

/// A lexical token in the source file. One or more of these is created for each pre-token,
/// except non-documentation comment pre-tokens, which are removed.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum LexicalToken {
    Lexical {
        text: String,
    },
    Operator {
        text: String,
        info: OperatorInfo,
    },
    /// `->`
    Arrow,
    /// `::`
    Scope,
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `{`
    LBrace,
    /// `}`
    RBrace,
    /// `:`
    Type,
    /// `=`
    Assign,
    /// `,`
    Comma,
    /// `|`
    Pipe,
    /// `&`
    Borrow,
    /// `erased`. 0 ownership.
    Erased,
    /// `owned`. 1 ownership.
    Owned,
    /// `copyable`. omega-ownership.
    Copyable,
    /// `borrowed`. Represents the type of borrowed values, not the borrowed values themselves.
    Borrowed,
    /// `def`
    Def,
    /// `inductive`
    Inductive,
    /// `fn`
    Fn,
    /// `let`
    Let,
    /// `Sort`
    Sort,
    /// `Region`
    Region,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum OperatorInfo {
    Prefix {
        precedence: i32,
    },
    Infix {
        left_precedence: i32,
        right_precedence: i32,
    },
    Postfix {
        precedence: i32,
    },
}

impl LexicalToken {
    /// Gets the amount of Unicode characters in the underlying string.
    fn chars_count(&self) -> usize {
        match self {
            LexicalToken::Lexical { text } => text.chars().count(),
            LexicalToken::Operator { text, .. } => text.chars().count(),
            LexicalToken::Arrow => 2,
            LexicalToken::Scope => 2,
            LexicalToken::LParen => 1,
            LexicalToken::RParen => 1,
            LexicalToken::LBrace => 1,
            LexicalToken::RBrace => 1,
            LexicalToken::Type => 1,
            LexicalToken::Assign => 1,
            LexicalToken::Comma => 1,
            LexicalToken::Pipe => 1,
            LexicalToken::Borrow => 1,
            LexicalToken::Erased => "erased".chars().count(),
            LexicalToken::Owned => "owned".chars().count(),
            LexicalToken::Copyable => "copyable".chars().count(),
            LexicalToken::Borrowed => "borrowed".chars().count(),
            LexicalToken::Def => "def".chars().count(),
            LexicalToken::Inductive => "inductive".chars().count(),
            LexicalToken::Fn => "fn".chars().count(),
            LexicalToken::Let => "let".chars().count(),
            LexicalToken::Sort => "sort".chars().count(),
            LexicalToken::Region => "region".chars().count(),
        }
    }
}

impl Display for LexicalToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LexicalToken::Lexical { text } => write!(f, "\"{text}\""),
            LexicalToken::Operator { text, .. } => write!(f, "operator \"{text}\""),
            LexicalToken::Arrow => write!(f, "->"),
            LexicalToken::Scope => write!(f, "'::'"),
            LexicalToken::LParen => write!(f, "'('"),
            LexicalToken::RParen => write!(f, "')'"),
            LexicalToken::LBrace => write!(f, "'{{'"),
            LexicalToken::RBrace => write!(f, "'}}'"),
            LexicalToken::Type => write!(f, "':'"),
            LexicalToken::Assign => write!(f, "'='"),
            LexicalToken::Comma => write!(f, "','"),
            LexicalToken::Pipe => write!(f, "'|'"),
            LexicalToken::Borrow => write!(f, "'&'"),
            LexicalToken::Erased => write!(f, "'erased'"),
            LexicalToken::Owned => write!(f, "'owned'"),
            LexicalToken::Copyable => write!(f, "'copyable'"),
            LexicalToken::Borrowed => write!(f, "'borrowed'"),
            LexicalToken::Def => write!(f, "'def'"),
            LexicalToken::Inductive => write!(f, "'inductive'"),
            LexicalToken::Fn => write!(f, "'fn'"),
            LexicalToken::Let => write!(f, "'let'"),
            LexicalToken::Sort => write!(f, "'Sort'"),
            LexicalToken::Region => write!(f, "'Region'"),
        }
    }
}

/// Converts a stream of pre-tokens into a stream of tokens.
/// TODO: Add functionality that allows this iterator to be given operators that it can then parse.
pub struct TokenIterator<I>
where
    I: Iterator<Item = TokenTree>,
{
    pre_tokens: I,
    /// If we just parsed a pre-token, this list is filled up with the tokens that the pre-token
    /// split up into, so that we can return them later with calls to [`Iterator::next()`].
    /// The list is reversed so [`Vec::pop()`] can be used to get the next token.
    parsed_tokens_rev: Vec<(LexicalToken, Span)>,
    /// The map of known operators to this token iterator.
    /// The innermost map converts operators as strings into their information.
    /// The outermost map tracks the size of each operator; in particular, an operator with string
    /// `s` should be stored in `operators[s.len()][s]`. This allows us to parse longer operators
    /// first, which deals with situations like favouring `++` over `+`. The structure [`BTreeMap`]
    /// is used for determinism.
    operators: BTreeMap<usize, BTreeMap<String, OperatorInfo>>,
    /// Used for emitting diagnostics at the end of the file.
    /// When a token is emitted using `next`, its span is stored here.
    last_token: Span,
}

impl<I> TokenIterator<I>
where
    I: Iterator<Item = TokenTree>,
{
    pub fn new(pre_tokens: impl IntoIterator<IntoIter = I>) -> Self {
        Self {
            pre_tokens: pre_tokens.into_iter(),
            parsed_tokens_rev: Vec::new(),
            operators: BTreeMap::new(),
            last_token: Span { start: 0, end: 1 },
        }
    }

    /// Undoes an invocation to [`Iterator::next`].
    /// This is implemented in place of any kind of "peekable" trait.
    fn push(&mut self, token: LexicalToken, span: Span) {
        self.parsed_tokens_rev.push((token, span))
    }

    fn split_pre_token(&self, text: &str, span: Span) -> Vec<(LexicalToken, Span)> {
        // Search for known operators, longest first.
        for (_, operators) in self.operators.iter().rev() {
            for (operator, info) in operators {
                if let Some((before, after)) = text.split_once(operator) {
                    // We found an operator.
                    return self.split_pre_token_recursive(
                        before,
                        after,
                        LexicalToken::Operator {
                            text: operator.clone(),
                            info: *info,
                        },
                        span,
                    );
                }
            }
        }

        // We didn't find any operators in this text.
        // Now search for important tokens like left and right parentheses.
        if let Some((before, after)) = text.split_once("::") {
            self.split_pre_token_recursive(before, after, LexicalToken::Scope, span)
        } else if let Some((before, after)) = text.split_once('(') {
            self.split_pre_token_recursive(before, after, LexicalToken::LParen, span)
        } else if let Some((before, after)) = text.split_once(')') {
            self.split_pre_token_recursive(before, after, LexicalToken::RParen, span)
        } else if let Some((before, after)) = text.split_once('{') {
            self.split_pre_token_recursive(before, after, LexicalToken::LBrace, span)
        } else if let Some((before, after)) = text.split_once('}') {
            self.split_pre_token_recursive(before, after, LexicalToken::RBrace, span)
        } else if let Some((before, after)) = text.split_once(':') {
            self.split_pre_token_recursive(before, after, LexicalToken::Type, span)
        } else if let Some((before, after)) = text.split_once('=') {
            self.split_pre_token_recursive(before, after, LexicalToken::Assign, span)
        } else if let Some((before, after)) = text.split_once(',') {
            self.split_pre_token_recursive(before, after, LexicalToken::Comma, span)
        } else if let Some((before, after)) = text.split_once('|') {
            self.split_pre_token_recursive(before, after, LexicalToken::Pipe, span)
        } else if let Some((before, after)) = text.split_once('&') {
            self.split_pre_token_recursive(before, after, LexicalToken::Borrow, span)
        } else {
            // We didn't find any other tokens in this text.
            if text.is_empty() {
                Vec::new()
            } else {
                // Treat the text as a single token.
                // TODO: Warn the user if this doesn't look like a single token.
                vec![(
                    match text {
                        "erased" => LexicalToken::Erased,
                        "owned" => LexicalToken::Owned,
                        "copyable" => LexicalToken::Copyable,
                        "borrowed" => LexicalToken::Borrowed,
                        "def" => LexicalToken::Def,
                        "inductive" => LexicalToken::Inductive,
                        "fn" => LexicalToken::Fn,
                        "let" => LexicalToken::Let,
                        "Sort" => LexicalToken::Sort,
                        "Region" => LexicalToken::Region,
                        _ => LexicalToken::Lexical {
                            text: text.to_owned(),
                        },
                    },
                    span,
                )]
            }
        }
    }

    /// Splits on `before` and `after`, and concatenates the results with `token` in between.
    fn split_pre_token_recursive(
        &self,
        before: &str,
        after: &str,
        token: LexicalToken,
        span: Span,
    ) -> Vec<(LexicalToken, Span)> {
        let before_len = before.chars().count();
        let token_len = token.chars_count();
        let mut result = self.split_pre_token(
            before,
            Span {
                start: span.start,
                end: span.start + before_len,
            },
        );
        result.push((
            token,
            Span {
                start: span.start + before_len,
                end: span.start + before_len + token_len,
            },
        ));
        result.extend(self.split_pre_token(
            after,
            Span {
                start: span.start + before_len + token_len,
                end: span.end,
            },
        ));
        result
    }
}

impl<I> Iterator for TokenIterator<I>
where
    I: Iterator<Item = TokenTree>,
{
    type Item = (LexicalToken, Span);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(token) = self.parsed_tokens_rev.pop() {
            self.last_token = token.1;
            Some(token)
        } else {
            // Consume and parse the next pre-token.
            if let Some((pre_token, span)) = self.pre_tokens.next() {
                match pre_token {
                    PreToken::Lexical { text } => {
                        self.parsed_tokens_rev = self.split_pre_token(&text, span);
                        self.parsed_tokens_rev.reverse();
                    }
                    PreToken::Comment { .. } => {
                        // Ignore comments that are not documentation comments.
                    }
                }
                self.next()
            } else {
                None
            }
        }
    }
}

/// A parsed item from the input stream.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum PItem {
    Definition { def: PDefinition },
    Inductive { ind: PInductive },
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct PDefinition {
    pub def_token: Span,
    pub name: Name<Provenance>,
    pub ty: PExpr,
    pub value: PExpr,
    pub universe_params: Vec<Name<Provenance>>,
}

impl Debug for PDefinition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<pdef>")
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct PInductive {
    pub inductive_token: Span,
    pub name: Name<Provenance>,
    pub ty: PExpr,
    pub global_params: u32,
    pub intro_rules: Vec<(Name<Provenance>, PExpr)>,
    pub universe_params: Vec<Name<Provenance>>,
}

impl Debug for PInductive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<pind>")
    }
}

/// A parsed expression from the input stream.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PExpr {
    pub provenance: Provenance,
    pub contents: PExprContents,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PExprContents {
    QualifiedName {
        qualified_name: QualifiedName<Provenance>,
        universes: Vec<PUniverse>,
    },
    Apply {
        left: Box<PExpr>,
        right: Box<PExpr>,
    },
    UnaryOp {
        operator: String,
        operator_span: Span,
        param: Box<PExpr>,
    },
    BinaryOp {
        operator: String,
        operator_span: Span,
        left: Box<PExpr>,
        right: Box<PExpr>,
    },
    Forall {
        binder: PBinder,
        inner_expr: Box<PExpr>,
    },
    Function {
        binder: PBinder,
        inner_expr: Box<PExpr>,
    },
    Let {
        name_to_assign: Name<Provenance>,
        to_assign: Box<PExpr>,
        to_assign_ty: Box<PExpr>,
        body: Box<PExpr>,
    },
    Borrow {
        region: Box<PExpr>,
        value: Box<PExpr>,
    },
    Borrowed {
        region: Box<PExpr>,
        ty: Box<PExpr>,
    },
    Sort {
        universe: PUniverse,
    },
    Region,
}

/// A parsed universe from the input stream.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PUniverse {
    pub provenance: Provenance,
    pub contents: PUniverseContents,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PUniverseContents {
    Lexical { text: String },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PBinder {
    pub keyword: Span,
    pub binder_annotation: BinderAnnotation,
    pub name: Name<Provenance>,
    pub ty: Box<PExpr>,
}

/// Parses a list of items from a stream of pre-tokens.
pub(crate) fn parse_items(
    db: &dyn Db,
    source: Source,
    stream: TokenIterator<impl Iterator<Item = (PreToken, Span)>>,
) -> Dr<Vec<(PItem, Span)>> {
    let mut parser = Parser { db, source, stream };
    parser.parse_items()
}

struct Parser<'a, I>
where
    I: Iterator<Item = (PreToken, Span)>,
{
    db: &'a dyn Db,
    source: Source,
    stream: TokenIterator<I>,
}

impl<'a, I> Parser<'a, I>
where
    I: Iterator<Item = (PreToken, Span)>,
{
    fn parse_items(&mut self) -> Dr<Vec<(PItem, Span)>> {
        self.parse_item().bind(|result| {
            if let Some(result) = result {
                self.parse_items().map(|mut more_items| {
                    more_items.insert(0, result);
                    more_items
                })
            } else {
                Dr::ok(Vec::new())
            }
        })
    }

    /// Parses a single item from a stream of pre-tokens.
    /// If the stream was empty, return [`None`].
    fn parse_item(&mut self) -> Dr<Option<(PItem, Span)>> {
        match self.stream.next() {
            Some((LexicalToken::Def, span)) => self.parse_definition(span).map(Some),
            Some((LexicalToken::Inductive, span)) => self.parse_inductive(span).map(Some),
            Some((token, span)) => Dr::fail(
                Report::new(ReportKind::Error, self.source, span.start)
                    .with_message(format!("expected item, got {token}"))
                    .with_label(
                        Label::new(self.source, span, LabelType::Error)
                            .with_message("expected item here"),
                    ),
            ),
            None => Dr::ok(None),
        }
    }

    /// The keyword `def` has already been parsed.
    fn parse_definition(&mut self, def_token: Span) -> Dr<(PItem, Span)> {
        // Parse the name of the definition.
        self.parse_name().bind(|name| {
            // We might have a sequence of universe parameters `::{...}` here.
            let universe_parameters = match self.stream.next() {
                Some((LexicalToken::Scope, _)) => self
                    .parse_exact(LexicalToken::LBrace)
                    .bind(|_| self.parse_universe_parameters()),
                Some((token, span)) => {
                    self.stream.push(token, span);
                    Dr::ok(Vec::new())
                }
                None => Dr::ok(Vec::new()),
            };
            universe_parameters.bind(|universe_params| {
                self.parse_exact(LexicalToken::Type).bind(|_type_span| {
                    self.parse_expr().bind(|ty| {
                        self.parse_exact(LexicalToken::Assign).bind(|_assign_span| {
                            self.parse_expr().map(|value| {
                                let span = name.0.provenance.span();
                                (
                                    PItem::Definition {
                                        def: PDefinition {
                                            def_token,
                                            name,
                                            ty,
                                            value,
                                            universe_params,
                                        },
                                    },
                                    span,
                                )
                            })
                        })
                    })
                })
            })
        })
    }

    /// The keyword `inductive` has already been parsed.
    fn parse_inductive(&mut self, _inductive_token: Span) -> Dr<(PItem, Span)> {
        todo!()
    }

    fn parse_expr(&mut self) -> Dr<PExpr> {
        // Run a Pratt-style parser to parse this expression.
        self.parse_expr_with_precedence(i32::MIN)
    }

    /// Parses an expression with a minimum precedence.
    /// If any operator with higher precedence is met, that is not considered part of this parsed expression.
    fn parse_expr_with_precedence(&mut self, min_precedence: i32) -> Dr<PExpr> {
        let mut lhs = match self.stream.next() {
            Some((LexicalToken::Lexical { text }, span)) => self
                .parse_qualified_name(Name(WithProvenance {
                    provenance: Provenance::Quill(SourceSpan {
                        source: self.source,
                        span,
                    }),
                    contents: Str::new(self.db, text),
                }))
                .map(|(qualified_name, universes)| PExpr {
                    provenance: qualified_name.0.provenance,
                    contents: PExprContents::QualifiedName {
                        qualified_name,
                        universes,
                    },
                }),
            Some((LexicalToken::LParen, lparen_span)) => self.parse_expr().bind(|expr| {
                self.parse_exact(LexicalToken::RParen)
                    .map(|rparen_span| PExpr {
                        provenance: Provenance::Quill(SourceSpan {
                            source: self.source,
                            span: Span {
                                start: lparen_span.start,
                                end: rparen_span.end,
                            },
                        }),
                        contents: expr.contents,
                    })
            }),
            Some((LexicalToken::Fn, fn_span)) => {
                // Parse a binder, then parse the resulting expression.
                self.parse_binder(fn_span).bind(|binder| {
                    self.parse_exact(LexicalToken::Comma).bind(|_comma_span| {
                        self.parse_expr_with_precedence(min_precedence)
                            .map(|inner_expr| PExpr {
                                provenance: Provenance::Quill(SourceSpan {
                                    source: self.source,
                                    span: Span {
                                        start: fn_span.start,
                                        end: inner_expr.provenance.span().end,
                                    },
                                }),
                                contents: PExprContents::Function {
                                    binder,
                                    inner_expr: Box::new(inner_expr),
                                },
                            })
                    })
                })
            }
            Some((LexicalToken::Forall, forall_span)) => {
                // Parse a binder, then parse the resulting expression.
                self.parse_binder(forall_span).bind(|binder| {
                    self.parse_exact(LexicalToken::Comma).bind(|_comma_span| {
                        self.parse_expr_with_precedence(min_precedence)
                            .map(|inner_expr| PExpr {
                                provenance: Provenance::Quill(SourceSpan {
                                    source: self.source,
                                    span: Span {
                                        start: forall_span.start,
                                        end: inner_expr.provenance.span().end,
                                    },
                                }),
                                contents: PExprContents::Forall {
                                    binder,
                                    inner_expr: Box::new(inner_expr),
                                },
                            })
                    })
                })
            }
            Some((LexicalToken::Let, let_span)) => {
                // Parse the name, then parse the value we're assigning, then parse the resulting expression.
                // The structure is `let a : b = c, d`.
                self.parse_name().bind(|name_to_assign| {
                    self.parse_exact(LexicalToken::Type).bind(|_| {
                        self.parse_expr().bind(|to_assign_ty| {
                            self.parse_exact(LexicalToken::Assign).bind(|_| {
                                self.parse_expr().bind(|to_assign| {
                                    self.parse_exact(LexicalToken::Comma).bind(|_| {
                                        self.parse_expr().map(|body| PExpr {
                                            provenance: Provenance::Quill(SourceSpan {
                                                source: self.source,
                                                span: Span {
                                                    start: let_span.start,
                                                    end: body.provenance.span().end,
                                                },
                                            }),
                                            contents: PExprContents::Let {
                                                name_to_assign,
                                                to_assign: Box::new(to_assign),
                                                to_assign_ty: Box::new(to_assign_ty),
                                                body: Box::new(body),
                                            },
                                        })
                                    })
                                })
                            })
                        })
                    })
                })
            }
            Some((LexicalToken::Borrow, borrow_span)) => {
                // Parse a region, then parse the value to borrow.
                self.parse_expr().bind(|region| {
                    self.parse_exact(LexicalToken::Comma).bind(|_comma_span| {
                        self.parse_expr_with_precedence(min_precedence)
                            .map(|value| PExpr {
                                provenance: Provenance::Quill(SourceSpan {
                                    source: self.source,
                                    span: Span {
                                        start: borrow_span.start,
                                        end: value.provenance.span().end,
                                    },
                                }),
                                contents: PExprContents::Borrow {
                                    region: Box::new(region),
                                    value: Box::new(value),
                                },
                            })
                    })
                })
            }
            Some((LexicalToken::Borrowed, borrow_span)) => {
                // Parse a region, then parse the type that is to be borrowed.
                self.parse_expr().bind(|region| {
                    self.parse_exact(LexicalToken::Comma).bind(|_comma_span| {
                        self.parse_expr_with_precedence(min_precedence)
                            .map(|ty| PExpr {
                                provenance: Provenance::Quill(SourceSpan {
                                    source: self.source,
                                    span: Span {
                                        start: borrow_span.start,
                                        end: ty.provenance.span().end,
                                    },
                                }),
                                contents: PExprContents::Borrowed {
                                    region: Box::new(region),
                                    ty: Box::new(ty),
                                },
                            })
                    })
                })
            }
            Some((LexicalToken::Sort, span)) => self.parse_universe(false).map(|universe| PExpr {
                provenance: Provenance::Quill(SourceSpan {
                    source: self.source,
                    span: Span {
                        start: span.start,
                        end: universe.provenance.span().end,
                    },
                }),
                contents: PExprContents::Sort { universe },
            }),
            Some((LexicalToken::Region, span)) => Dr::ok(PExpr {
                provenance: Provenance::Quill(SourceSpan {
                    source: self.source,
                    span,
                }),
                contents: PExprContents::Region,
            }),
            Some((
                LexicalToken::Operator {
                    text,
                    info: OperatorInfo::Prefix { precedence },
                },
                span,
            )) => self
                .parse_expr_with_precedence(precedence)
                .map(|rhs| PExpr {
                    provenance: Provenance::Quill(SourceSpan {
                        source: self.source,
                        span: Span {
                            start: span.start,
                            end: rhs.provenance.span().end,
                        },
                    }),
                    contents: PExprContents::UnaryOp {
                        operator: text,
                        operator_span: span,
                        param: Box::new(rhs),
                    },
                }),
            Some((token, span)) => Dr::fail(
                Report::new(ReportKind::Error, self.source, span.start)
                    .with_message(format!("expected expression, got {token}"))
                    .with_label(
                        Label::new(self.source, span, LabelType::Error)
                            .with_message("unexpected token found here"),
                    ),
            ),
            None => Dr::fail(
                Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                    .with_message("end of file reached, but expected an expression")
                    .with_label(
                        Label::new(self.source, self.stream.last_token, LabelType::Error)
                            .with_message("end of file reached here"),
                    ),
            ),
        };

        loop {
            match self.stream.next() {
                Some((LexicalToken::Lexical { text }, span)) => {
                    lhs = lhs.bind(|lhs| {
                        self.parse_qualified_name(Name(WithProvenance {
                            provenance: Provenance::Quill(SourceSpan {
                                source: self.source,
                                span,
                            }),
                            contents: Str::new(self.db, text),
                        }))
                        .map(|(qualified_name, universes)| PExpr {
                            provenance: Provenance::Quill(SourceSpan {
                                source: self.source,
                                span: Span {
                                    start: lhs.provenance.span().start,
                                    end: qualified_name.0.provenance.span().end,
                                },
                            }),
                            contents: PExprContents::Apply {
                                left: Box::new(lhs),
                                right: Box::new(PExpr {
                                    provenance: qualified_name.0.provenance,
                                    contents: PExprContents::QualifiedName {
                                        qualified_name,
                                        universes,
                                    },
                                }),
                            },
                        })
                    });
                }
                Some((LexicalToken::LParen, lparen_span)) => {
                    lhs = lhs.bind(|lhs| {
                        self.parse_expr().bind(|rhs| {
                            self.parse_exact(LexicalToken::RParen)
                                .map(|rparen_span| PExpr {
                                    provenance: Provenance::Quill(SourceSpan {
                                        source: self.source,
                                        span: Span {
                                            start: lhs.provenance.span().start,
                                            end: rparen_span.end,
                                        },
                                    }),
                                    contents: PExprContents::Apply {
                                        left: Box::new(lhs),
                                        right: Box::new(PExpr {
                                            provenance: Provenance::Quill(SourceSpan {
                                                source: self.source,
                                                span: Span {
                                                    start: lparen_span.start,
                                                    end: rparen_span.end,
                                                },
                                            }),
                                            contents: rhs.contents,
                                        }),
                                    },
                                })
                        })
                    });
                }
                Some((
                    LexicalToken::Operator {
                        text,
                        info: OperatorInfo::Postfix { precedence },
                    },
                    span,
                )) => {
                    if precedence < min_precedence {
                        self.stream.push(
                            LexicalToken::Operator {
                                text,
                                info: OperatorInfo::Postfix { precedence },
                            },
                            span,
                        );
                        break;
                    }

                    lhs = lhs.map(|lhs| PExpr {
                        provenance: Provenance::Quill(SourceSpan {
                            source: self.source,
                            span: Span {
                                start: lhs.provenance.span().start,
                                end: span.end,
                            },
                        }),
                        contents: PExprContents::UnaryOp {
                            operator: text,
                            operator_span: span,
                            param: Box::new(lhs),
                        },
                    });
                }
                Some((
                    LexicalToken::Operator {
                        text,
                        info:
                            OperatorInfo::Infix {
                                left_precedence,
                                right_precedence,
                            },
                    },
                    span,
                )) => {
                    if left_precedence < min_precedence {
                        self.stream.push(
                            LexicalToken::Operator {
                                text,
                                info: OperatorInfo::Infix {
                                    left_precedence,
                                    right_precedence,
                                },
                            },
                            span,
                        );
                        break;
                    }
                    lhs = lhs.bind(|lhs| {
                        self.parse_expr_with_precedence(right_precedence)
                            .map(|rhs| PExpr {
                                provenance: Provenance::Quill(SourceSpan {
                                    source: self.source,
                                    span: Span {
                                        start: lhs.provenance.span().start,
                                        end: rhs.provenance.span().end,
                                    },
                                }),
                                contents: PExprContents::BinaryOp {
                                    operator: text,
                                    operator_span: span,
                                    left: Box::new(lhs),
                                    right: Box::new(rhs),
                                },
                            })
                    })
                }
                Some((token, span)) => {
                    self.stream.push(token, span);
                    break;
                }
                None => break,
            }
        }

        lhs
    }

    fn parse_binder(&mut self, keyword: Span) -> Dr<PBinder> {
        self.parse_exact(LexicalToken::LParen).bind(|_lparen_span| {
            self.parse_name().bind(|name| {
                self.parse_exact(LexicalToken::Type).bind(|_ty_span| {
                    self.parse_expr().bind(|ty| {
                        self.parse_exact(LexicalToken::RParen)
                            .map(|_rparen_span| PBinder {
                                keyword,
                                binder_annotation: BinderAnnotation::Explicit,
                                name,
                                ty: Box::new(ty),
                            })
                    })
                })
            })
        })
    }

    /// Parses a universe from the input stream. If `parenthesised` is true, we allow expressions
    /// such as `u + k` and `max u v` which can only be parsed when inside a set of parentheses.
    fn parse_universe(&mut self, _parenthesised: bool) -> Dr<PUniverse> {
        match self.stream.next() {
            Some((LexicalToken::Lexical { text }, span)) => match text.as_str() {
                "max" => todo!(),
                "imax" => todo!(),
                _ => Dr::ok(PUniverse {
                    provenance: Provenance::Quill(SourceSpan {
                        source: self.source,
                        span,
                    }),
                    contents: PUniverseContents::Lexical { text },
                }),
            },
            Some((LexicalToken::LParen, lparen_span)) => self.parse_universe(true).bind(|univ| {
                self.parse_exact(LexicalToken::RParen)
                    .map(|rparen_span| PUniverse {
                        provenance: Provenance::Quill(SourceSpan {
                            source: self.source,
                            span: Span {
                                start: lparen_span.start,
                                end: rparen_span.end,
                            },
                        }),
                        contents: univ.contents,
                    })
            }),
            _ => todo!(),
        }
    }

    /// Parses a qualified name with the given initial token.
    /// If universe parameters were provided to this qualified name, return them as well.
    fn parse_qualified_name(
        &mut self,
        initial: Name<Provenance>,
    ) -> Dr<(QualifiedName<Provenance>, Vec<PUniverse>)> {
        match self.stream.next() {
            Some((LexicalToken::Scope, _)) => {
                // What follows should either be more name segments or a `{` to start a sequence of universe parameters.
                match self.stream.next() {
                    Some((LexicalToken::Lexical { text }, span)) => self
                        .parse_qualified_name(Name(WithProvenance {
                            provenance: Provenance::Quill(SourceSpan {
                                source: self.source,
                                span,
                            }),
                            contents: Str::new(self.db, text),
                        }))
                        .map(|(mut name, universes)| {
                            name.0.provenance = Provenance::Quill(SourceSpan {
                                source: self.source,
                                span: Span {
                                    start: initial.0.provenance.span().start,
                                    end: name.0.provenance.span().end,
                                },
                            });
                            name.0.contents.insert(0, initial);
                            (name, universes)
                        }),
                    Some((LexicalToken::LBrace, _span)) => {
                        // This is a sequence of universe parameters.
                        self.parse_universes().map(|(universes, rbrace_span)| {
                            (
                                QualifiedName(WithProvenance {
                                    provenance: Provenance::Quill(SourceSpan {
                                        source: self.source,
                                        span: Span {
                                            start: initial.0.provenance.span().start,
                                            end: rbrace_span.end,
                                        },
                                    }),
                                    contents: vec![initial],
                                }),
                                universes,
                            )
                        })
                    }
                    Some((token, _span)) => Dr::fail(
                        Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                            .with_message(format!(
                                "expected a name segment or '{{' for this qualified name, got {token}"
                            ))
                            .with_label(
                                Label::new(
                                    self.source,
                                    self.stream.last_token,
                                    LabelType::Error,
                                )
                                .with_message("unexpected token found here"),
                            ),
                    ),
                    None => Dr::fail(
                        Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                            .with_message(
                                "end of file reached, but this qualified name was not complete",
                            )
                            .with_label(
                                Label::new(
                                    self.source,
                                    self.stream.last_token,
                                    LabelType::Error,
                                )
                                .with_message("end of file reached here"),
                            ),
                    ),
                }
            }
            Some((token, span)) => {
                self.stream.push(token, span);
                Dr::ok((
                    QualifiedName(WithProvenance {
                        provenance: initial.0.provenance,
                        contents: vec![initial],
                    }),
                    Vec::new(),
                ))
            }
            None => Dr::ok((
                QualifiedName(WithProvenance {
                    provenance: initial.0.provenance,
                    contents: vec![initial],
                }),
                Vec::new(),
            )),
        }
    }

    /// The initial brace `{` is assumed to have been parsed.
    /// The final brace is returned as a [`Span`].
    fn parse_universes(&mut self) -> Dr<(Vec<PUniverse>, Span)> {
        let mut universes = Dr::ok(Vec::new());
        loop {
            match self.stream.next() {
                Some((LexicalToken::RBrace, span)) => {
                    // This is the end of the list of universe parameters.
                    break universes.map(|universes| (universes, span));
                }
                Some((token, span)) => {
                    self.stream.push(token, span);
                    universes = universes.bind(|mut universes| {
                        self.parse_universe(false).map(|univ| {
                            universes.push(univ);
                            universes
                        })
                    });
                }
                None => {
                    break Dr::fail(
                        Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                            .with_message("end of file reached, but expected a universe")
                            .with_label(
                                Label::new(self.source, self.stream.last_token, LabelType::Error)
                                    .with_message("end of file reached here"),
                            ),
                    )
                }
            }
        }
    }

    /// The initial brace `{` is assumed to have been parsed.
    fn parse_universe_parameters(&mut self) -> Dr<Vec<Name<Provenance>>> {
        let mut universe_parameters = Dr::ok(Vec::new());
        loop {
            match self.stream.next() {
                Some((LexicalToken::RBrace, _span)) => {
                    // This is the end of the list of universe parameters.
                    break universe_parameters;
                }
                Some((token, span)) => {
                    self.stream.push(token, span);
                    universe_parameters = universe_parameters.bind(|mut universes| {
                        self.parse_name().map(|name| {
                            universes.push(name);
                            universes
                        })
                    });
                }
                None => {
                    break Dr::fail(
                        Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                            .with_message("end of file reached, but expected a universe")
                            .with_label(
                                Label::new(self.source, self.stream.last_token, LabelType::Error)
                                    .with_message("end of file reached here"),
                            ),
                    )
                }
            }
        }
    }

    fn parse_name(&mut self) -> Dr<Name<Provenance>> {
        match self.stream.next() {
            Some((LexicalToken::Lexical { text }, span)) => Dr::ok(Name(WithProvenance {
                provenance: Provenance::Quill(SourceSpan {
                    source: self.source,
                    span,
                }),
                contents: Str::new(self.db, text),
            })),
            Some((token, span)) => Dr::fail(
                Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                    .with_message(format!("expected a name, got {token}"))
                    .with_label(
                        Label::new(self.source, span, LabelType::Error)
                            .with_message("unexpected token found here"),
                    ),
            ),
            None => Dr::fail(
                Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                    .with_message("end of file reached, but expected a name")
                    .with_label(
                        Label::new(self.source, self.stream.last_token, LabelType::Error)
                            .with_message("end of file reached here"),
                    ),
            ),
        }
    }

    fn parse_exact(&mut self, token: LexicalToken) -> Dr<Span> {
        match self.stream.next() {
            Some((other_token, span)) => {
                if token == other_token {
                    Dr::ok(span)
                } else {
                    Dr::ok_with(
                        span,
                        Report::new(ReportKind::Error, self.source, span.start)
                            .with_message(format!("expected {token}, got {other_token}"))
                            .with_label(
                                Label::new(self.source, span, LabelType::Error)
                                    .with_message("unexpected token found here"),
                            ),
                    )
                }
            }
            _ => Dr::fail(
                Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                    .with_message(format!("end of file reached, but expected {token}"))
                    .with_label(
                        Label::new(self.source, self.stream.last_token, LabelType::Error)
                            .with_message("end of file reached here"),
                    ),
            ),
        }
    }
}
