use salsa::{InternId, InternKey};
use serde::{de::Visitor, Deserialize, Serialize};
use std::{fmt::Debug, path::PathBuf};
use upcast::UpcastFrom;

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

/// Provides utilities for interning various data types.
///
/// The [`Debug`] constraint is used to give databases a simple [`Debug`] implementation
/// for use in tracing messages.
#[salsa::query_group(InternStorage)]
pub trait Intern: Debug {
    #[salsa::interned]
    fn intern_string_data(&self, data: String) -> Str;

    #[salsa::interned]
    fn intern_path_data(&self, data: PathData) -> Path;
}

impl<'a, T: Intern + 'a> UpcastFrom<T> for dyn Intern + 'a {
    fn up_from(value: &T) -> &(dyn Intern + 'a) {
        value
    }
    fn up_from_mut(value: &mut T) -> &mut (dyn Intern + 'a) {
        value
    }
}

// Users of `LOCAL_DATABASE` must ensure that they do not retain copies of the borrow `&'static dyn Intern`.
thread_local!(static LOCAL_DATABASE: std::cell::RefCell<Option<&'static dyn Intern>> = Default::default());

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
pub fn with_local_database<T>(db: &dyn Intern, f: impl FnOnce() -> T) -> T {
    LOCAL_DATABASE.with(|local_db| {
        if local_db.borrow().is_some() {
            panic!("with_local_database called recursively");
        }
        local_db.replace(Some(unsafe {
            std::mem::transmute::<&dyn Intern, &'static dyn Intern>(db)
        }));
    });
    let val = f();
    LOCAL_DATABASE.with(|local_db| {
        local_db.replace(None);
    });
    val
}

/// An interned string type.
/// Can be safely copied and compared cheaply.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Str(InternId);

impl Str {
    /// Only call inside a serde deserialisation block, i.e., inside `with_local_database`.
    pub fn deserialise(v: String) -> Str {
        LOCAL_DATABASE.with(|db| {
            db.borrow()
                .expect("must only deserialise inside with_local_database")
                .intern_string_data(v)
        })
    }
}

impl Serialize for Str {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&LOCAL_DATABASE.with(|db| {
            self.lookup(
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

impl InternKey for Str {
    fn from_intern_id(v: InternId) -> Self {
        Self(v)
    }

    fn as_intern_id(&self) -> InternId {
        self.0
    }
}

impl Str {
    pub fn lookup(self, db: &dyn Intern) -> String {
        db.lookup_intern_string_data(self)
    }
}

/// Generates a sequence of distinct strings with a given prefix.
pub struct StrGenerator<'a> {
    db: &'a dyn Intern,
    prefix: String,
    counter: u64,
}

impl<'a> StrGenerator<'a> {
    pub fn new(db: &'a dyn Intern, prefix: impl ToString) -> Self {
        Self {
            db,
            prefix: prefix.to_string(),
            counter: 0,
        }
    }

    pub fn generate(&mut self) -> Str {
        let result = self.db.intern_string_data(if self.counter == 0 {
            self.prefix.clone()
        } else {
            format!("{}_{}", self.prefix, self.counter)
        });
        self.counter += 1;
        result
    }
}

/// A fully qualified path.
/// Use [`Path`] instead, if possible.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PathData(pub Vec<Str>);

/// A fully qualified path.
/// Can be used, for example, as a qualified name for a definition or for a source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Path(InternId);

impl Serialize for Path {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        LOCAL_DATABASE
            .with(|db| {
                self.lookup(
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
        PathData::deserialize(deserializer).map(|data| {
            LOCAL_DATABASE.with(|db| {
                db.borrow()
                    .expect("must only deserialise inside with_local_database")
                    .intern_path_data(data)
            })
        })
    }
}

impl InternKey for Path {
    fn from_intern_id(v: InternId) -> Self {
        Self(v)
    }

    fn as_intern_id(&self) -> InternId {
        self.0
    }
}

impl Path {
    pub fn lookup(self, db: &dyn Intern) -> PathData {
        db.lookup_intern_path_data(self)
    }

    pub fn display(self, intern: &dyn Intern) -> String {
        intern
            .lookup_intern_path_data(self)
            .0
            .into_iter()
            .map(|s| intern.lookup_intern_string_data(s))
            .collect::<Vec<_>>()
            .join("::")
    }
}

impl PathData {
    pub fn intern(self, db: &dyn Intern) -> Path {
        db.intern_path_data(self)
    }
}

pub trait InternExt: Intern {
    fn path_data_to_path_buf(&self, data: &PathData) -> PathBuf {
        data.0
            .iter()
            .map(|x| self.lookup_intern_string_data(*x))
            .collect()
    }

    fn path_to_path_buf(&self, path: Path) -> PathBuf {
        self.path_data_to_path_buf(&self.lookup_intern_path_data(path))
    }

    fn path_to_string(&self, path: Path) -> String {
        self.path_to_path_buf(path).to_string_lossy().to_string()
    }

    /// Split the last element off a path and return the resulting components.
    /// If a path was `[a, b, c]`, this function returns `([a, b], c)`.
    /// Typically this is used for extracting the name of the source file and the item inside that module from a qualified name.
    ///
    /// # Panics
    /// If this path does not have any elements, this will panic.
    fn split_path_last(&self, path: Path) -> (Path, Str) {
        let path_data = self.lookup_intern_path_data(path);
        let (last_element, source_file) = path_data.0.split_last().unwrap();
        let source_file_name = self.intern_path_data(PathData(source_file.into()));
        (source_file_name, *last_element)
    }
}

impl<T> InternExt for T where T: Intern {}

/// Uniquely identifies a source file.
#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Source {
    /// The relative path from the project root to this source file.
    /// File extensions are *not* appended to this path.
    pub path: Path,
    /// The type of the file.
    /// This is used to deduce the file extension.
    pub ty: SourceType,
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
