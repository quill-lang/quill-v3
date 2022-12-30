use std::{fmt::Display, iter::Peekable};

use fcommon::{Label, LabelType, Report, ReportKind, Source, Span, Spanned};
use fexpr::{
    expr::BinderAnnotation,
    result::{Dr, Message, Style},
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Bracket {
    /// `(` and `)`.
    Paren,
    /// `[` and `]`.
    Square,
    /// `{` and `}`.
    Brace,
    /// `{{` and `}}`.
    DoubleBrace,
}

impl From<Bracket> for BinderAnnotation {
    fn from(value: Bracket) -> Self {
        match value {
            Bracket::Paren => BinderAnnotation::Explicit,
            Bracket::Square => BinderAnnotation::ImplicitTypeclass,
            Bracket::Brace => BinderAnnotation::ImplicitEager,
            Bracket::DoubleBrace => BinderAnnotation::ImplicitWeak,
        }
    }
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

/// The reserved operators and keywords.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ReservedSymbol {
    /// `->`
    Arrow,
    /// `=>`
    DoubleArrow,
    /// `::`
    Scope,
    /// `:`
    Colon,
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
    /// `Type`
    Type,
    /// `Region`
    Region,
}

impl Display for ReservedSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReservedSymbol::Arrow => write!(f, "->"),
            ReservedSymbol::DoubleArrow => write!(f, "=>"),
            ReservedSymbol::Scope => write!(f, "::"),
            ReservedSymbol::Colon => write!(f, ":"),
            ReservedSymbol::Assign => write!(f, "="),
            ReservedSymbol::Comma => write!(f, ","),
            ReservedSymbol::Pipe => write!(f, "|"),
            ReservedSymbol::Borrow => write!(f, "&"),
            ReservedSymbol::Erased => write!(f, "erased"),
            ReservedSymbol::Owned => write!(f, "owned"),
            ReservedSymbol::Copyable => write!(f, "copyable"),
            ReservedSymbol::Borrowed => write!(f, "borrowed"),
            ReservedSymbol::Def => write!(f, "def"),
            ReservedSymbol::Inductive => write!(f, "inductive"),
            ReservedSymbol::Fn => write!(f, "fn"),
            ReservedSymbol::Let => write!(f, "let"),
            ReservedSymbol::Sort => write!(f, "Sort"),
            ReservedSymbol::Type => write!(f, "Type"),
            ReservedSymbol::Region => write!(f, "Region"),
        }
    }
}

impl From<ReservedSymbol> for Message {
    fn from(value: ReservedSymbol) -> Self {
        Message::Styled {
            style: Style::token_tree(),
            message: Box::new(format!("'{value}'").into()),
        }
    }
}

/// A lexical token tree is string of input text, not enclosed in a comment or string literal, which
/// is not directly adjacent to any other non-space characters. Many of these are tokens, but some
/// token tree will need to be further split up into actual tokens. For instance, `<1>` is a
/// single token tree because it contains no spaces, but (unless `<1>` is defined as an operator
/// somewhere) it will then be converted into the tokens `<`, `1`, `>`.
///
/// A token tree is either a lexical token, a comment token, or a block enclosed in a matching pair of brackets.
/// Later, we may add string and char literals as extra variants to this enum.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TokenTree {
    /// A token such as a variable name.
    Lexical { text: String, span: Span },
    /// A token used as an operator.
    Operator {
        text: String,
        info: OperatorInfo,
        span: Span,
    },
    /// A reserved symbol such as a language operator or a keyword.
    Reserved { symbol: ReservedSymbol, span: Span },
    /// A comment string.
    Comment { text: String, span: Span },
    /// A block enclosed in a matching pair of brackets.
    Block {
        bracket: Bracket,
        open: Span,
        close: Span,
        contents: Vec<TokenTree>,
    },
    /// The *start* of a new line.
    /// The amount of indentation at the start of this line is given.
    Newline { span: Span, indent: usize },
}

impl Display for TokenTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenTree::Lexical { text, .. } => write!(f, "'{text}'"),
            TokenTree::Operator { text, .. } => write!(f, "'{text}'"),
            TokenTree::Reserved { symbol, .. } => write!(f, "'{symbol}'"),
            TokenTree::Comment { .. } => write!(f, "comment"),
            TokenTree::Block { .. } => write!(f, "block"),
            TokenTree::Newline { .. } => write!(f, "new line"),
        }
    }
}

impl From<&TokenTree> for Message {
    fn from(value: &TokenTree) -> Self {
        Message::Styled {
            style: Style::token_tree(),
            message: Box::new(value.to_string().into()),
        }
    }
}

impl Spanned for TokenTree {
    fn span(&self) -> Span {
        match self {
            TokenTree::Lexical { span, .. } => *span,
            TokenTree::Operator { span, .. } => *span,
            TokenTree::Reserved { span, .. } => *span,
            TokenTree::Comment { span, .. } => *span,
            TokenTree::Block { open, close, .. } => Span {
                start: open.start,
                end: close.end,
            },
            TokenTree::Newline { span, .. } => *span,
        }
    }
}

/// Tokenises the input stream until the next character is `\r`, `\n`, or absent.
/// Returns the amount of leading whitespace characters on the line, then a list of things on the line.
fn tokenise_line(
    source: Source,
    stream: &mut Peekable<impl Iterator<Item = (usize, char)>>,
) -> Dr<(usize, Vec<(String, Span)>)> {
    // Compute the leading whitespace of the line.
    let mut leading_whitespace = 0;
    while stream.next_if(|(_, c)| *c == ' ').is_some() {
        // This is a character of leading whitespace.
        leading_whitespace += 1;
    }

    // The main content of the line now follows.
    let mut tokens = Vec::new();
    let mut current_token = String::new();
    let mut current_token_span: Option<Span> = None;
    while let Some((index, c)) = stream.next_if(|(_, c)| *c != '\r' && *c != '\n') {
        // This is a character from the line.
        if c.is_whitespace() {
            if c == '\t' {
                return Dr::fail(
                    Report::new(ReportKind::Error, source, index)
                        .with_message("tabs should be converted into spaces".into())
                        .with_label(Label::new(
                            source,
                            Span {
                                start: index,
                                end: index + 1,
                            },
                            LabelType::Error,
                        ).with_message("tab character was found here".into()))
                        .with_note("explicit spaces are preferred to tab characters because the parser is whitespace-sensitive, and inconsistent use of tabs and spaces can cause ambiguity".into()),
                );
            }
            // The current token is finished, if indeed we just parsed one.
            if let Some(span) = current_token_span {
                tokens.push((std::mem::take(&mut current_token), span));
                current_token_span = None;
            }
        } else if ['(', ')', '[', ']', '{', '}'].contains(&c) {
            // This is a bracket character.
            // Bracket characters never mix with previous tokens.
            match current_token_span {
                Some(span) => {
                    // We just parsed a token.
                    tokens.push((std::mem::take(&mut current_token), span));
                    tokens.push((
                        c.into(),
                        Span {
                            start: index,
                            end: index + 1,
                        },
                    ));
                    current_token_span = None;
                }
                None => {
                    tokens.push((
                        c.into(),
                        Span {
                            start: index,
                            end: index + 1,
                        },
                    ));
                }
            }
        } else {
            // Append this character to the current token.
            // First, update the span information on the current token.
            match &mut current_token_span {
                Some(span) => {
                    span.end = index + 1;
                }
                None => {
                    // This was the first character in the current token.
                    current_token_span = Some(Span {
                        start: index,
                        end: index + 1,
                    });
                }
            }
            current_token.push(c);
        }
    }

    if let Some(span) = current_token_span {
        tokens.push((std::mem::take(&mut current_token), span));
    }

    Dr::ok((leading_whitespace, tokens))
}

/// We opened a bracket that must be closed by a matching bracket.
#[derive(Debug)]
struct StackEntry {
    bracket: Bracket,
    span: Span,
}

struct Stack {
    source: Source,
    /// The base list of token trees that we will return at the end.
    result: Vec<TokenTree>,
    stack: Vec<(StackEntry, Vec<TokenTree>)>,
}

impl Stack {
    fn push(&mut self, entry: StackEntry) {
        self.stack.push((entry, Vec::new()));
    }

    fn pop(&mut self) -> Option<(StackEntry, Vec<TokenTree>)> {
        self.stack.pop()
    }

    /// Push this token tree to the top stack entry.
    fn push_top(&mut self, tt: TokenTree) {
        match self.stack.last_mut() {
            Some((_, tokens)) => tokens.push(tt),
            None => self.result.push(tt),
        }
    }

    fn pop_bracket(&mut self, bracket: Bracket, span: Span) -> Dr<()> {
        match self.pop() {
            Some((
                StackEntry {
                    bracket: found_bracket,
                    span: found_span,
                },
                contents,
            )) => {
                if bracket == found_bracket {
                    // We combine the tokens in the stack into a single token tree.
                    self.push_top(TokenTree::Block {
                        bracket,
                        open: found_span,
                        close: span,
                        contents,
                    });
                    Dr::ok(())
                } else {
                    todo!()
                }
            }
            None => Dr::fail(
                Report::new(ReportKind::Error, self.source, span.start)
                    .with_message("found unmatched closing bracket".into())
                    .with_label(
                        Label::new(self.source, span, LabelType::Error).with_message(
                            "this closing bracket did not pair with an opening bracket".into(),
                        ),
                    ),
            ),
        }
    }
}

/// Splits the input stream up into token trees.
/// The [`TokenTree::Operator`] and [`TokenTree::Reserved`] variants do not appear in the returned token trees;
/// the `Parser` manages splitting up the [`TokenTree::Lexical`] tokens into these.
pub fn tokenise(source: Source, stream: impl Iterator<Item = char>) -> Dr<Vec<TokenTree>> {
    let mut stream = stream.enumerate().peekable();
    let mut reports = Vec::new();

    // The stack of open brackets and indentations.
    let mut stack = Stack {
        source,
        result: Vec::new(),
        stack: Vec::new(),
    };

    let mut previous_newline_span = Span { start: 0, end: 0 };

    // Peek at the next character in the stream.
    loop {
        let (result, more_reports) = tokenise_line(source, &mut stream).destructure();
        reports.extend(more_reports);
        let (indent, tokens) = match result {
            Some(result) => result,
            None => break,
        };

        stack.push_top(TokenTree::Newline {
            span: previous_newline_span,
            indent,
        });

        // If there are no tokens on the line, just ignore the line entirely.
        if tokens.first().is_none() {
            // Consume the newline character at the end of the line.
            let mut consumed_anything = false;
            while stream.next_if(|(_, c)| *c == '\r' || *c == '\n').is_some() {
                consumed_anything = true;
            }
            if consumed_anything {
                continue;
            } else {
                break;
            }
        };

        // Operate on each token on the line.
        for (token, span) in tokens {
            match token.as_str() {
                "(" => stack.push(StackEntry {
                    bracket: Bracket::Paren,
                    span,
                }),
                "[" => stack.push(StackEntry {
                    bracket: Bracket::Square,
                    span,
                }),
                "{" => stack.push(StackEntry {
                    bracket: Bracket::Brace,
                    span,
                }),
                ")" => {
                    let (_, more_reports) = stack.pop_bracket(Bracket::Paren, span).destructure();
                    reports.extend(more_reports);
                }
                "]" => {
                    let (_, more_reports) = stack.pop_bracket(Bracket::Square, span).destructure();
                    reports.extend(more_reports);
                }
                "}" => {
                    let (_, more_reports) = stack.pop_bracket(Bracket::Brace, span).destructure();
                    reports.extend(more_reports);
                }
                _ => stack.push_top(TokenTree::Lexical { text: token, span }),
            }
        }

        // Consume the newline(s), or we're at the end of the file.
        let mut span: Option<Span> = None;
        while let Some((index, _)) = stream.next_if(|(_, c)| *c == '\r' || *c == '\n') {
            match &mut span {
                Some(span) => span.end = index + 1,
                None => {
                    span = Some(Span {
                        start: index,
                        end: index + 1,
                    })
                }
            }
        }
        match span {
            Some(span) => {
                previous_newline_span = Span {
                    start: span.end,
                    end: span.end + 1,
                }
            }
            None => {
                // We must be at the end of the file.
                break;
            }
        }
    }

    if !reports
        .iter()
        .any(|report| report.kind == ReportKind::Error)
    {
        // There were no errors emitted so far.
        if let Some((last, _)) = stack.stack.last() {
            reports.push(
                Report::new(ReportKind::Error, source, last.span.start)
                    .with_message("this bracket was not closed".into())
                    .with_label(
                        Label::new(source, last.span, LabelType::Error)
                            .with_message("opening bracket found here".into()),
                    ),
            )
        }

        if stream.next().is_some() {
            todo!()
        }
    }

    Dr::ok_with_many(stack.result, reports).deny()
}
