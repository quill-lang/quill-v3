//! A pretty-printer for parsed expressions and definitions.
//! Based off Wadler's 'A Prettier Printer'.
//!
//! - <https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf>
//! - <https://github.com/prettier/prettier-printer>

use std::{collections::VecDeque, fmt::Display};

/// A pretty-printable 'document'.
/// `DOC` in Wadler.
#[derive(Clone)]
pub enum Document {
    Empty,
    Concat(Vec<Document>),
    Indent(Box<Document>),
    Any(Vec<Document>),
    Text(String),
    Line,
}

impl Document {
    pub fn then(self, doc: Document) -> Document {
        Document::Concat(vec![self, doc])
    }

    pub fn pretty_print(&self, width: usize) -> String {
        let mut docs = VecDeque::new();
        docs.push_front((0, self));
        best(width, 0, docs).to_string()
    }
}

/// `Doc` in Wadler.
#[derive(Clone)]
enum SimpleDocument {
    Empty,
    Text {
        string: String,
        doc: Box<SimpleDocument>,
    },
    Line {
        indent: usize,
        doc: Box<SimpleDocument>,
    },
}

impl Display for SimpleDocument {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SimpleDocument::Empty => write!(f, ""),
            SimpleDocument::Text { string, doc } => write!(f, "{string}{doc}"),
            SimpleDocument::Line { indent, doc } => {
                write!(f, "\n{}{doc}", " ".repeat(*indent))
            }
        }
    }
}

/// The screen width is `width` and we are currently on column `col`.
/// The parameter `docs` is a slice of indentation-document pairs.
fn best(width: usize, col: usize, mut docs: VecDeque<(usize, &Document)>) -> SimpleDocument {
    loop {
        match docs.pop_front() {
            None => return SimpleDocument::Empty,
            Some((_, Document::Empty)) => {}
            Some((indent, Document::Concat(more_docs))) => {
                for item in more_docs.iter().rev().map(|doc| (indent, doc)) {
                    docs.push_front(item);
                }
            }
            Some((indent, Document::Any(more_docs))) => {
                return more_docs
                    .iter()
                    .map(|doc| {
                        let mut docs = docs.clone();
                        docs.push_front((indent, doc));
                        best(width, col, docs)
                    })
                    .reduce(|left, right| better(width, col, left, right))
                    .unwrap()
            }
            Some((indent, Document::Indent(doc))) => {
                docs.push_front((indent + 4, doc));
            }
            Some((_, Document::Text(text))) => {
                let new_col = col + text.len();
                return SimpleDocument::Text {
                    string: text.clone(),
                    doc: Box::new(best(width, new_col, docs)),
                };
            }
            Some((indent, Document::Line)) => {
                return SimpleDocument::Line {
                    indent,
                    doc: Box::new(best(width, indent, docs)),
                };
            }
        }
    }
}

/// Returns the 'better' of the two documents.
fn better(width: usize, col: usize, left: SimpleDocument, right: SimpleDocument) -> SimpleDocument {
    if fits(width as isize - col as isize, &left) {
        left
    } else {
        right
    }
}

/// Checks if the first line of the document fits into `width` spaces.
fn fits(width: isize, doc: &SimpleDocument) -> bool {
    if width < 0 {
        false
    } else {
        match doc {
            SimpleDocument::Empty => true,
            SimpleDocument::Text { string, doc } => fits(width - string.len() as isize, doc),
            SimpleDocument::Line { .. } => true,
        }
    }
}
