use std::{cmp::Ordering, fmt::Display, iter::Peekable};

use fcommon::{Dr, Label, LabelType, Report, ReportKind, Source, Span, Spanned};
use fexpr::expr::BinderAnnotation;

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
            ReservedSymbol::Region => write!(f, "Region"),
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
    /// An indented block of tokens.
    Indented { contents: Vec<TokenTree> },
    /// A line terminator.
    Newline { span: Span },
}

impl Display for TokenTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenTree::Lexical { text, .. } => write!(f, "'{text}'"),
            TokenTree::Operator { text, .. } => write!(f, "'{text}'"),
            TokenTree::Reserved { symbol, .. } => write!(f, "'{symbol}'"),
            TokenTree::Comment { .. } => write!(f, "comment"),
            TokenTree::Block { .. } => write!(f, "block"),
            TokenTree::Indented { .. } => write!(f, "indented block"),
            TokenTree::Newline { .. } => write!(f, "newline"),
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
            TokenTree::Indented { contents } => {
                if let Some(first) = contents.first() {
                    Span {
                        start: first.span().start,
                        end: contents.last().unwrap().span().end,
                    }
                } else {
                    unreachable!("indented token trees should be nonempty")
                }
            }
            TokenTree::Newline { span } => *span,
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
                        .with_message("tabs should be converted into spaces")
                        .with_label(Label::new(
                            source,
                            Span {
                                start: index,
                                end: index + 1,
                            },
                            LabelType::Error,
                        ).with_message("tab character was found here"))
                        .with_note("explicit spaces are preferred to tab characters because the parser is whitespace-sensitive, and inconsistent use of tabs and spaces can cause ambiguity"),
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

#[derive(Debug)]
enum StackEntry {
    /// We have entered into a deeper indentation level.
    /// The field `level` is the amount of characters the indent is.
    /// This is typically a multiple of 4.
    Indent { level: usize, span: Span },
    /// We opened a bracket that must be closed by a matching bracket.
    OpenBracket { bracket: Bracket, span: Span },
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

    fn pop_indent(&mut self, new_indent: usize, new_indent_span: Span) -> Dr<()> {
        match self.pop() {
            Some((StackEntry::OpenBracket { bracket: _, span }, _)) => Dr::fail(
                Report::new(ReportKind::Error, self.source, new_indent_span.start)
                    .with_message("decrease in indentation level was unexpected inside block")
                    .with_label(
                        Label::new(self.source, new_indent_span, LabelType::Error)
                            .with_message("decrease in indentation level found here"),
                    ).with_label(Label::new(self.source, span, LabelType::Note)
                        .with_message("opening bracket found here, this bracket must be closed before the indent level can be reduced")),
            ),
            Some((StackEntry::Indent { level, .. }, contents)) => {
                // Check if the new indentation level matches the given one.
                match (new_indent + 4).cmp(&level) {
                    Ordering::Less => {
                        // We can skip over this level on the stack.
                        self.push_top(TokenTree::Indented { contents });
                        self.pop_indent(new_indent, new_indent_span)
                    }
                    Ordering::Equal => {
                        // We are exactly at the correct level.
                        self.push_top(TokenTree::Indented { contents });
                        Dr::ok(())
                    }
                    Ordering::Greater => {
                        // We removed too many levels of indentation.
                        todo!()
                    }
                }
            }
            None => Dr::fail(
                Report::new(ReportKind::Error, self.source, new_indent_span.start)
                    .with_message("decrease in indentation level was unexpected, because there was no increase before")
                    .with_label(
                        Label::new(self.source, new_indent_span, LabelType::Error)
                            .with_message("decrease in indentation level found here"),
                    ),
            ),
        }
    }

    /// Call this at EOF. Pops all indents.
    fn pop_all_indents(&mut self) {
        while let Some((StackEntry::Indent { .. }, _)) = self.stack.last() {
            match self.stack.pop() {
                Some((StackEntry::Indent { .. }, contents)) => {
                    self.push_top(TokenTree::Indented { contents });
                }
                _ => unreachable!(),
            }
        }
    }

    fn pop_bracket(&mut self, bracket: Bracket, span: Span) {
        match self.pop() {
            Some((
                StackEntry::OpenBracket {
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
                }
            }
            Some((StackEntry::Indent { .. }, _)) => {
                // We're allowed to resolve indents *after* closing brackets.
                todo!()
            }
            None => todo!(),
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
    let mut current_indent = 0;

    // Peek at the next character in the stream.
    loop {
        let (result, more_reports) = tokenise_line(source, &mut stream).destructure();
        reports.extend(more_reports);
        let (indentation, tokens) = match result {
            Some(result) => result,
            None => break,
        };

        // Get the span of the first character on the line.
        // If there are no tokens on the line, just ignore the line entirely.
        let start_span = match tokens.first() {
            Some((_, span)) => Span {
                start: span.start,
                end: span.start + 1,
            },
            None => {
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
            }
        };

        // If our indentation increased or decreased, resolve this on the stack.
        match indentation.cmp(&current_indent) {
            Ordering::Less => {
                let (value, more_reports) = stack.pop_indent(indentation, start_span).destructure();
                reports.extend(more_reports);
                if value.is_none() {
                    break;
                }
            }
            Ordering::Equal => {}
            Ordering::Greater => {
                // The indentation level should have increased by exactly 4.
                if indentation - current_indent != 4 {
                    todo!()
                }
                stack.push(StackEntry::Indent {
                    level: indentation,
                    span: start_span,
                });
            }
        }
        current_indent = indentation;

        // Operate on each token on the line.
        for (token, span) in tokens {
            match token.as_str() {
                "(" => stack.push(StackEntry::OpenBracket {
                    bracket: Bracket::Paren,
                    span,
                }),
                "[" => stack.push(StackEntry::OpenBracket {
                    bracket: Bracket::Square,
                    span,
                }),
                "{" => stack.push(StackEntry::OpenBracket {
                    bracket: Bracket::Brace,
                    span,
                }),
                ")" => stack.pop_bracket(Bracket::Paren, span),
                "]" => stack.pop_bracket(Bracket::Square, span),
                "}" => stack.pop_bracket(Bracket::Brace, span),
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
            Some(span) => stack.push_top(TokenTree::Newline { span }),
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
        // Perform some final checks.

        // First, pop all indents from the stack.
        stack.pop_all_indents();

        if let Some((last, _)) = stack.stack.last() {
            match last {
                StackEntry::Indent { .. } => unreachable!("just popped all indents"),
                StackEntry::OpenBracket { span, .. } => reports.push(
                    Report::new(ReportKind::Error, source, span.start)
                        .with_message("this bracket was not closed")
                        .with_label(
                            Label::new(source, *span, LabelType::Error)
                                .with_message("opening bracket found here"),
                        ),
                ),
            }
        }

        if stream.next().is_some() {
            todo!()
        }
    }

    Dr::ok_with_many(stack.result, reports).deny()
}
