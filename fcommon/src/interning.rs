use serde::{de::Visitor, Deserialize, Serialize};
use std::{fmt::Debug, path::PathBuf};

use crate::Db;

/// A span of code in a given source file.
/// Represented by a range of UTF-8 characters.
/// See also [`SourceSpan`].
///
/// The default span is `0..0`.
#[derive(Serialize, Deserialize, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    /// The lower bound of the span (inclusive).
    pub start: usize,
    /// The upper bound of the span (exclusive).
    pub end: usize,
}

impl Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl From<std::ops::Range<usize>> for Span {
    fn from(value: std::ops::Range<usize>) -> Self {
        Self {
            start: value.start,
            end: value.end,
        }
    }
}

impl From<&std::ops::Range<usize>> for Span {
    fn from(value: &std::ops::Range<usize>) -> Self {
        Self {
            start: value.start,
            end: value.end,
        }
    }
}

impl From<Span> for std::ops::Range<usize> {
    fn from(value: Span) -> Self {
        value.start..value.end
    }
}

/// An interned string type.
/// Can be safely copied and compared cheaply.
#[salsa::interned]
pub struct Str {
    #[return_ref]
    pub text: String,
}

// Users of `LOCAL_DATABASE` must ensure that they do not retain copies of the borrow `&'static dyn Db`.
thread_local!(static LOCAL_DATABASE: std::cell::RefCell<Option<&'static dyn Db>> = Default::default());

/// When serialising and deserialising feather values, we need to look at the database to look up interned data.
/// However, the serde API doesn't provide access to the database.
/// This file provides a way to temporarily set a thread-local read-only database for use while (de)serialising.
///
/// # Safety
/// This function uses `unsafe` code. This is used to convert the lifetime of `db` to `'static`, so that it can
/// be held by a thread local variable. Thread local variables cannot be lifetime parametric.
/// We ensure safety by deinitialising the thread local variable after the function terminates.
/// Users of `LOCAL_DATABASE` must ensure that they do not retain copies of the borrow `&'static dyn Intern`.
///
/// # Panics
/// If this is used recursively, it will panic.
pub fn with_local_database<T>(db: &dyn Db, f: impl FnOnce() -> T) -> T {
    LOCAL_DATABASE.with(|local_db| {
        if local_db.borrow().is_some() {
            panic!("with_local_database called recursively");
        }
        local_db.replace(Some(unsafe {
            std::mem::transmute::<&dyn Db, &'static dyn Db>(db)
        }));
    });
    let val = f();
    LOCAL_DATABASE.with(|local_db| {
        local_db.replace(None);
    });
    val
}

impl Str {
    /// Only call inside a serde deserialisation block, i.e., inside `with_local_database`.
    pub fn deserialise(v: String) -> Str {
        LOCAL_DATABASE.with(|db| {
            Str::new(
                db.borrow()
                    .expect("must only deserialise inside with_local_database"),
                v,
            )
        })
    }
}

impl Serialize for Str {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(LOCAL_DATABASE.with(|db| {
            self.text(
                db.borrow()
                    .expect("must only serialise inside with_local_database"),
            )
        }))
    }
}

struct StrVisitor;

impl<'de> Visitor<'de> for StrVisitor {
    type Value = Str;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a string")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Str::deserialise(v.to_owned()))
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Str::deserialise(v))
    }
}

impl<'de> Deserialize<'de> for Str {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_string(StrVisitor)
    }
}

/// Generates a sequence of distinct strings with a given prefix.
pub struct StrGenerator<'a> {
    db: &'a dyn Db,
    prefix: String,
    counter: u64,
}

impl<'a> StrGenerator<'a> {
    pub fn new(db: &'a dyn Db, prefix: impl ToString) -> Self {
        Self {
            db,
            prefix: prefix.to_string(),
            counter: 0,
        }
    }

    pub fn generate(&mut self) -> Str {
        let result = Str::new(
            self.db,
            if self.counter == 0 {
                self.prefix.clone()
            } else {
                format!("{}_{}", self.prefix, self.counter)
            },
        );
        self.counter += 1;
        result
    }
}

/// A fully qualified path.
/// Can be used, for example, as a qualified name for a definition or for a source file.
/// Can be safely copied and compared cheaply.
#[salsa::interned]
pub struct Path {
    #[return_ref]
    pub segments: Vec<Str>,
}

impl Serialize for Path {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        LOCAL_DATABASE
            .with(|db| {
                self.segments(
                    db.borrow()
                        .expect("must only serialise inside with_local_database"),
                )
            })
            .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Path {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Vec::<Str>::deserialize(deserializer).map(|data| {
            LOCAL_DATABASE.with(|db| {
                Path::new(
                    db.borrow()
                        .expect("must only deserialise inside with_local_database"),
                    data,
                )
            })
        })
    }
}

impl Path {
    pub fn display(self, db: &dyn Db) -> String {
        self.segments(db)
            .iter()
            .map(|s| s.text(db))
            .cloned()
            .collect::<Vec<_>>()
            .join("::")
    }

    /// Split the last element off a path and return the resulting components.
    /// If a path was `[a, b, c]`, this function returns `([a, b], c)`.
    /// Typically this is used for extracting the name of the source file and the item inside that module from a qualified name.
    ///
    /// # Panics
    ///
    /// If this path does not have any elements, this will panic.
    pub fn split_last(&self, db: &dyn Db) -> (Path, Str) {
        let (last_element, source_file) = self.segments(db).split_last().unwrap();
        (Path::new(db, Vec::from(source_file)), *last_element)
    }

    pub fn to_path_buf(&self, db: &dyn Db) -> PathBuf {
        self.segments(db).iter().map(|s| s.text(db)).collect()
    }

    pub fn to_string(&self, db: &dyn Db) -> String {
        self.segments(db)
            .iter()
            .map(|s| s.text(db).to_owned())
            .collect::<Vec<_>>()
            .join("::")
    }
}

/// Uniquely identifies a source file.
#[salsa::interned]
pub struct Source {
    /// The relative path from the project root to this source file.
    /// File extensions are *not* appended to this path.
    pub path: Path,
    /// The type of the file.
    /// This is used to deduce the file extension.
    pub ty: SourceType,
}

/// Gadget used to (de)serialise [`Source`].
#[derive(Serialize, Deserialize)]
#[doc(hidden)]
struct SourceData {
    path: Path,
    ty: SourceType,
}

impl Serialize for Source {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        LOCAL_DATABASE.with(|db| {
            let db = db
                .borrow()
                .expect("must only serialise inside with_local_database");
            SourceData {
                path: self.path(db),
                ty: self.ty(db),
            }
            .serialize(serializer)
        })
    }
}

impl<'de> Deserialize<'de> for Source {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        LOCAL_DATABASE.with(|db| {
            let db = db
                .borrow()
                .expect("must only serialise inside with_local_database");
            SourceData::deserialize(deserializer)
                .map(|SourceData { path, ty }| Source::new(db, path, ty))
        })
    }
}

/// Used to deduce the file extension of a [`Source`].
#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SourceType {
    /// A feather source file, written as an S-expression encoded as UTF-8.
    Feather,
    /// A quill source file, encoded as UTF-8.
    Quill,
}

impl SourceType {
    pub fn extension(self) -> &'static str {
        match self {
            SourceType::Feather => "ron",
            SourceType::Quill => "quill",
        }
    }
}

/// A span of code in a particular source file.
/// See also [`Span`].
#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SourceSpan {
    pub source: Source,
    pub span: Span,
}

#[cfg(feature = "ariadne")]
impl ariadne::Span for SourceSpan {
    type SourceId = Source;

    fn source(&self) -> &Self::SourceId {
        &self.source
    }

    fn start(&self) -> usize {
        self.span.start
    }

    fn end(&self) -> usize {
        self.span.end
    }
}
