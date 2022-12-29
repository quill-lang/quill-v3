//! We create the [`Dr`] diagnostic result type by instantiating the [`ParametricDr`] type.

use std::collections::BTreeSet;

use fcommon::{MessageFormatter, ParametricDr};

use crate::expr::Term;

/// A colour associated to a particular concept.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SemanticColour {}

#[cfg(feature = "console")]
impl From<SemanticColour> for console::Color {
    fn from(value: SemanticColour) -> Self {
        match value {}
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
    fg_bright: bool,
    bg_bright: bool,
    attrs: BTreeSet<SemanticAttribute>,
}

#[cfg(feature = "console")]
impl From<&Style> for console::Style {
    fn from(value: &Style) -> Self {
        let mut result = Self::new();
        if let Some(fg) = value.fg {
            result = result.fg(fg.into());
        }
        if let Some(bg) = value.bg {
            result = result.bg(bg.into());
        }
        if value.fg_bright {
            result = result.bright();
        }
        if value.bg_bright {
            result = result.on_bright();
        }
        for attr in value.attrs.iter().copied() {
            result = result.attr(attr.into())
        }
        result
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MessageSegment {
    String(String),
    Term(Term),
    Styled { style: Style, message: Box<Message> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Message {
    pub segments: Vec<MessageSegment>,
}

impl Message {
    pub fn new(string: String) -> Self {
        Self {
            segments: vec![MessageSegment::String(string)],
        }
    }
}

/// Short for "diagnostic result".
/// See [`ParametricDr`].
pub type Dr<T> = ParametricDr<Message, T>;

/// Converts a [`ParametricDr`] over [`String`] to a regular [`Dr`].
pub fn parametric_dr_to_dr<T>(value: ParametricDr<String, T>) -> Dr<T> {
    value.map_messages(Message::new)
}

/// A delaborator can render a term into a message.
/// The resulting message should not contain any [`MessageSegment::Term`].
pub trait Delaborator {
    fn delaborate(&self, term: Term) -> Message;
}

/// A message formatter for the console, using a given delaborator of type `T`.
#[cfg(feature = "console")]
pub struct ConsoleFormatter<T>(pub T);

#[cfg(feature = "console")]
impl<T> MessageFormatter for ConsoleFormatter<T>
where
    T: Delaborator,
{
    type Message = Message;

    fn format(&self, message: &Self::Message) -> String {
        message
            .segments
            .iter()
            .map(|segment| match segment {
                MessageSegment::String(string) => string.to_owned(),
                MessageSegment::Term(term) => self.format(&self.0.delaborate(*term)),
                MessageSegment::Styled { style, message } => console::Style::from(style)
                    .apply_to(self.format(message))
                    .for_stderr()
                    .to_string(),
            })
            .collect::<Vec<_>>()
            .join("")
    }
}
