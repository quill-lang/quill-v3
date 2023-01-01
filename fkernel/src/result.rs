//! We create the [`Dr`] diagnostic result type by instantiating the [`ParametricDr`] type.

use std::collections::BTreeSet;

use fcommon::{MessageFormatter, ParametricDr, Path, Str};

use crate::{
    basic::{Name, WithProvenance},
    expr::HeapExpression,
};

/// A colour associated to a particular concept.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SemanticColour {
    Name,
    Scope,
    TokenTree,
}

#[cfg(feature = "console")]
impl From<SemanticColour> for console::Color {
    fn from(value: SemanticColour) -> Self {
        match value {
            SemanticColour::Name => Self::White,
            SemanticColour::Scope => Self::White,
            SemanticColour::TokenTree => Self::Cyan,
        }
    }
}

impl SemanticColour {
    #[cfg(feature = "console")]
    fn is_bright(self) -> bool {
        match self {
            SemanticColour::Name => true,
            SemanticColour::Scope => false,
            SemanticColour::TokenTree => false,
        }
    }
}

/// A rendering attribute associated to a particular concept.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SemanticAttribute {
    /// Usually represented with italicised text.
    Emphasis,
}

#[cfg(feature = "console")]
impl From<SemanticAttribute> for console::Attribute {
    fn from(value: SemanticAttribute) -> Self {
        match value {
            SemanticAttribute::Emphasis => Self::Italic,
        }
    }
}

/// Mirrors the [`console::Style`] struct, but its fields are accessible.
/// This means that we can use this [`Style`] for things that are not terminal styles, such as HTML.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Style {
    fg: Option<SemanticColour>,
    bg: Option<SemanticColour>,
    attrs: BTreeSet<SemanticAttribute>,
}

impl Style {
    fn fg(mut self, fg: SemanticColour) -> Self {
        self.fg = Some(fg);
        self
    }

    pub fn name() -> Self {
        Self::default().fg(SemanticColour::Name)
    }

    pub fn scope() -> Self {
        Self::default().fg(SemanticColour::Scope)
    }

    pub fn token_tree() -> Self {
        Self::default().fg(SemanticColour::TokenTree)
    }
}

#[cfg(feature = "console")]
impl From<&Style> for console::Style {
    fn from(value: &Style) -> Self {
        let mut result = Self::new();
        if let Some(fg) = value.fg {
            result = result.fg(fg.into());
            if fg.is_bright() {
                result = result.bright();
            }
        }
        if let Some(bg) = value.bg {
            result = result.bg(bg.into());
            if bg.is_bright() {
                result = result.on_bright();
            }
        }
        for attr in value.attrs.iter().copied() {
            result = result.attr(attr.into())
        }
        result
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Message {
    String(String),
    Str(Str),
    Expression(HeapExpression),
    Path(Path),
    Styled { style: Style, message: Box<Message> },
    Sequence(Vec<Message>),
}

impl From<&str> for Message {
    fn from(value: &str) -> Self {
        Message::String(value.to_owned())
    }
}

impl From<String> for Message {
    fn from(value: String) -> Self {
        Message::String(value)
    }
}

impl From<Str> for Message {
    fn from(value: Str) -> Self {
        Message::Str(value)
    }
}

impl<T> From<WithProvenance<T>> for Message
where
    T: Into<Message>,
{
    fn from(value: WithProvenance<T>) -> Self {
        value.contents.into()
    }
}

impl From<Name> for Message {
    fn from(value: Name) -> Self {
        Message::Styled {
            style: Style::name(),
            message: Box::new(value.0.into()),
        }
    }
}

impl From<Path> for Message {
    fn from(value: Path) -> Self {
        Self::Path(value)
    }
}

impl From<HeapExpression> for Message {
    fn from(value: HeapExpression) -> Self {
        Message::Expression(value)
    }
}

impl Message {
    pub fn new(string: impl ToString) -> Self {
        Message::String(string.to_string())
    }
}

/// Creates the syntax `message![...]` for creating a message from
/// a sequence of things convertible to message segments.
#[macro_export]
macro_rules! message {
    ($($e:expr),*) => {
        $crate::result::Message::Sequence(
            vec![$($crate::result::Message::from($e)),*]
        )
    };
}

/// Short for "diagnostic result".
/// See [`ParametricDr`].
pub type Dr<T> = ParametricDr<Message, T>;

/// A delaborator can render an expression into a message.
/// The resulting message should not contain any [`Message::Expression`].
pub trait Delaborator {
    fn delaborate(&self, expr: &HeapExpression) -> Message;
}

/// A message formatter for the console, using a given delaborator of type `T`.
#[cfg(feature = "console")]
pub struct ConsoleFormatter<'a, T> {
    pub db: &'a dyn crate::Db,
    pub delaborator: T,
}

#[cfg(feature = "console")]
impl<T> MessageFormatter for ConsoleFormatter<'_, T>
where
    T: Delaborator,
{
    type Message = Message;

    fn format(&self, message: &Self::Message) -> String {
        match &message {
            Message::String(string) => string.to_owned(),
            Message::Str(str) => str.text(self.db).to_owned(),
            Message::Expression(expr) => self.format(&self.delaborator.delaborate(expr)),
            Message::Path(path) => path
                .segments(self.db)
                .iter()
                .map(|s| {
                    console::Style::from(&Style::name())
                        .apply_to(s.text(self.db))
                        .for_stderr()
                        .to_string()
                })
                .collect::<Vec<_>>()
                .join(
                    &console::Style::from(&Style::scope())
                        .apply_to("::")
                        .for_stderr()
                        .to_string(),
                ),
            Message::Styled { style, message } => console::Style::from(style)
                .apply_to(self.format(message))
                .for_stderr()
                .to_string(),
            Message::Sequence(sequence) => sequence
                .iter()
                .map(|x| self.format(x))
                .collect::<Vec<_>>()
                .join(""),
        }
    }
}
