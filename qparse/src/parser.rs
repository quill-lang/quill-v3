use std::collections::BTreeMap;

use fcommon::{Label, LabelType, Report, ReportKind, Source, Span, Spanned};
use fexpr::{
    basic::{Provenance, QualifiedName, WithProvenance},
    message,
    result::{Dr, Message},
};

use crate::{
    lex::{OperatorInfo, ReservedSymbol, TokenTree},
    Db,
};

pub struct ParserConfiguration<'db> {
    pub db: &'db dyn Db,
    pub source: Source,
    /// The map of known operators to this token iterator.
    /// The innermost map converts operators as strings into their information.
    /// The outermost map tracks the size of each operator; in particular, an operator with string
    /// `s` should be stored in `operators[s.len()][s]`. This allows us to parse longer operators
    /// first, which deals with situations like favouring `++` over `+`. The structure [`BTreeMap`]
    /// is used for determinism.
    ///
    /// This map should always have entries for `1` and `2`, although they can be empty.
    operators: BTreeMap<usize, BTreeMap<String, OperatorInfo>>,
}

impl<'db> ParserConfiguration<'db> {
    pub fn new(db: &'db dyn Db, source: Source) -> Self {
        let mut operators: BTreeMap<usize, BTreeMap<String, OperatorInfo>> = BTreeMap::new();
        operators.insert(1, Default::default());
        operators.insert(2, Default::default());
        // Add prefix operators for `*` and `&`.
        for op in ["*", "&"] {
            operators.get_mut(&1).unwrap().insert(
                op.to_owned(),
                OperatorInfo {
                    prefix: Some((0, QualifiedName(WithProvenance::new_synthetic(Vec::new())))),
                    infix: None,
                    postfix: None,
                },
            );
        }
        Self {
            db,
            source,
            operators,
        }
    }

    /// Splits a lexical token tree into a string of real lexical tokens based on the
    /// operators registered to this parser.
    fn split_lexical_token(&self, text: &str, span: Span) -> Vec<TokenTree> {
        // Search for known operators, longest first.
        for (token_len, operators) in self.operators.iter().rev() {
            let reserved_symbols: &[ReservedSymbol] = match token_len {
                1 => &[
                    ReservedSymbol::Colon,
                    ReservedSymbol::Assign,
                    ReservedSymbol::Comma,
                    ReservedSymbol::Pipe,
                ],
                2 => &[
                    ReservedSymbol::Arrow,
                    ReservedSymbol::DoubleArrow,
                    ReservedSymbol::Scope,
                ],
                _ => &[],
            };

            // First, check the reserved symbols.
            for symbol in reserved_symbols {
                if let Some((before, after)) = text.split_once(&symbol.to_string()) {
                    // We found this symbol.
                    let before_len = before.chars().count();
                    let mut result = self.split_lexical_token(
                        before,
                        Span {
                            start: span.start,
                            end: span.start + before_len,
                        },
                    );
                    result.push(TokenTree::Reserved {
                        symbol: *symbol,
                        span: Span {
                            start: span.start + before_len,
                            end: span.start + before_len + token_len,
                        },
                    });
                    result.extend(self.split_lexical_token(
                        after,
                        Span {
                            start: span.start + before_len + token_len,
                            end: span.end,
                        },
                    ));
                    return result;
                }
            }

            // Now check the user-defined operators.
            for (operator, info) in operators {
                if let Some((before, after)) = text.split_once(operator) {
                    // We found an operator.
                    let before_len = before.chars().count();
                    let mut result = self.split_lexical_token(
                        before,
                        Span {
                            start: span.start,
                            end: span.start + before_len,
                        },
                    );
                    result.push(TokenTree::Operator {
                        text: operator.clone(),
                        info: info.clone(),
                        span: Span {
                            start: span.start + before_len,
                            end: span.start + before_len + token_len,
                        },
                    });
                    result.extend(self.split_lexical_token(
                        after,
                        Span {
                            start: span.start + before_len + token_len,
                            end: span.end,
                        },
                    ));
                    return result;
                }
            }
        }

        // We didn't find any other tokens in this text.
        if text.is_empty() {
            Vec::new()
        } else {
            // Treat the text as a single token.
            // TODO: Warn the user if this doesn't look like a single token.
            let symbol = match text {
                "erased" => ReservedSymbol::Erased,
                "owned" => ReservedSymbol::Owned,
                "copyable" => ReservedSymbol::Copyable,
                "borrowed" => ReservedSymbol::Borrowed,
                "def" => ReservedSymbol::Def,
                "inductive" => ReservedSymbol::Inductive,
                "fn" => ReservedSymbol::Fn,
                "let" => ReservedSymbol::Let,
                "static" => ReservedSymbol::Static,
                "Sort" => ReservedSymbol::Sort,
                "Type" => ReservedSymbol::Type,
                "Region" => ReservedSymbol::Region,
                "RegionT" => ReservedSymbol::RegionT,
                _ => {
                    return vec![TokenTree::Lexical {
                        text: text.to_owned(),
                        span,
                    }]
                }
            };
            vec![TokenTree::Reserved { symbol, span }]
        }
    }
}

/// A parser, structured in the style of monadic parser combinators.
pub struct Parser<'db, 'a, I>
where
    I: Iterator<Item = TokenTree>,
{
    config: &'a ParserConfiguration<'db>,
    /// If we're parsing in a block delimited by brackets, their spans are stored here.
    block_brackets: Option<(Span, Span)>,
    /// A peekable iterator of token trees.
    /// Should not be accessed directly.
    trees: I,
    /// A sequence of token trees to yield before returning from `trees`.
    pushed: Vec<TokenTree>,
}

impl<'db, 'a, I> Parser<'db, 'a, I>
where
    I: Iterator<Item = TokenTree>,
{
    pub fn new(config: &'a ParserConfiguration<'db>, trees: I) -> Self {
        Self {
            config,
            block_brackets: None,
            trees,
            pushed: Vec::new(),
        }
    }

    /// Constructs a "child" parser, initialised with the configuration of this parser.
    /// Usually, this is used with [`TokenTree::Block`] where `vec` is the `contents` field.
    pub fn with_vec(
        &self,
        open: Span,
        close: Span,
        vec: Vec<TokenTree>,
    ) -> Parser<'db, 'a, std::vec::IntoIter<crate::lex::TokenTree>> {
        Parser {
            config: self.config,
            block_brackets: Some((open, close)),
            trees: vec.into_iter(),
            pushed: Vec::new(),
        }
    }

    pub fn config(&self) -> &'a ParserConfiguration {
        self.config
    }

    pub fn provenance(&self, span: Span) -> Provenance {
        Provenance::Quill(fcommon::SourceSpan {
            source: self.config().source,
            span,
        })
    }

    /// Parses the next token tree.
    /// Only this function, `next`, and `push` access `trees` and `pushed` directly.
    pub fn next(&mut self) -> Option<TokenTree> {
        match self.pushed.pop() {
            Some(tt) => Some(tt),
            None => match self.trees.next() {
                Some(TokenTree::Lexical { text, span }) => {
                    self.pushed = self.config.split_lexical_token(&text, span);
                    self.pushed.reverse();
                    self.pushed.pop()
                }
                tt => tt,
            },
        }
    }

    /// Peeks at the next token tree to be parsed.
    /// Only this function, `next`, and `push` access `trees` and `pushed` directly.
    pub fn peek(&mut self) -> Option<&TokenTree> {
        if self.pushed.is_empty() {
            match self.trees.next() {
                Some(TokenTree::Lexical { text, span }) => {
                    self.pushed = self.config.split_lexical_token(&text, span);
                    self.pushed.reverse();
                }
                Some(tt) => {
                    self.pushed.push(tt);
                }
                None => {}
            }
        }

        self.pushed.last()
    }

    /// Reverses a `next` operation.
    /// Only this function, `next`, and `peek` access `trees` and `pushed` directly.
    pub fn push(&mut self, tt: TokenTree) {
        self.pushed.push(tt);
    }

    /// Returns `true` if exactly one more invocation of `next` will yield a [`Some`] value.
    pub fn one_tree_left(&mut self) -> bool {
        match self.next() {
            Some(tt) => {
                let peek_is_none = self.peek().is_none();
                self.push(tt);
                peek_is_none
            }
            None => false,
        }
    }

    /// Parses the next token tree, and asserts that it is a lexical token.
    pub fn require_lexical(&mut self) -> Dr<(String, Span)> {
        match self.next() {
            Some(TokenTree::Lexical { text, span }) => Dr::ok((text, span)),
            Some(tt) => Dr::fail(
                Report::new(ReportKind::Error, self.config().source, tt.span().start)
                    .with_message(message!["expected a name, found ", &tt])
                    .with_label(
                        Label::new(self.config().source, tt.span(), LabelType::Error)
                            .with_message(message!["unexpected ", &tt, " found here"]),
                    ),
            ),
            None => todo!(),
        }
    }

    /// Parses the next token tree, and asserts that it is this reserved symbol.
    pub fn require_reserved(&mut self, symbol: ReservedSymbol) -> Dr<Span> {
        match self.next() {
            Some(TokenTree::Reserved {
                symbol: found_symbol,
                span,
            }) => {
                if symbol == found_symbol {
                    Dr::ok(span)
                } else {
                    Dr::fail(
                        Report::new(ReportKind::Error, self.config().source, span.start)
                            .with_message(message!["expected ", symbol, ", found ", found_symbol])
                            .with_label(
                                Label::new(self.config().source, span, LabelType::Error)
                                    .with_message(message![
                                        "unexpected ",
                                        found_symbol,
                                        " found here"
                                    ]),
                            ),
                    )
                }
            }
            Some(tt) => Dr::fail(
                Report::new(ReportKind::Error, self.config().source, tt.span().start)
                    .with_message(message!["expected ", symbol, ", found ", &tt])
                    .with_label(
                        Label::new(self.config().source, tt.span(), LabelType::Error)
                            .with_message(message!["unexpected ", &tt, " found here"]),
                    ),
            ),
            None => todo!("{symbol}"),
        }
    }

    /// Parses the next token tree, and asserts that it is a newline token tree.
    pub fn require_newline(&mut self) -> Dr<(Span, usize)> {
        match self.next() {
            Some(TokenTree::Newline { span, indent }) => Dr::ok((span, indent)),
            Some(tt) => Dr::fail(
                Report::new(ReportKind::Error, self.config().source, tt.span().start)
                    .with_message(message!["expected new line, found ", &tt])
                    .with_label(
                        Label::new(self.config().source, tt.span(), LabelType::Error)
                            .with_message(message!["unexpected ", &tt, " found here"]),
                    ),
            ),
            None => todo!(),
        }
    }

    pub fn assert_end(&mut self) -> Dr<()> {
        let source = self.config().source;
        let block_brackets = self.block_brackets;
        match self.peek() {
            Some(tt) => {
                Dr::ok_with(
                    (),
                    if let Some((open, close)) = block_brackets {
                        Report::<Message>::new(ReportKind::Error, source, tt.span().start)
                            .with_message("unexpected extra tokens".into())
                            .with_label(
                                Label::new(source, tt.span(), LabelType::Error).with_message(
                                    message!["did not expect ", tt, " while parsing this block"],
                                ),
                            )
                            .with_label(
                                Label::new(source, open, LabelType::Note)
                                    .with_message("block started here".into()),
                            )
                            .with_label(
                                Label::new(source, close, LabelType::Note)
                                    .with_message("block ended here".into()),
                            )
                    } else {
                        Report::new(ReportKind::Error, source, tt.span().start)
                            .with_message("unexpected extra tokens".into())
                            .with_label(
                                Label::new(source, tt.span(), LabelType::Error).with_message(
                                    message!["did not expect ", tt, " while parsing the file"],
                                ),
                            )
                    },
                )
            }
            None => Dr::ok(()),
        }
    }

    pub fn block_brackets(&self) -> Option<(Span, Span)> {
        self.block_brackets
    }
}
