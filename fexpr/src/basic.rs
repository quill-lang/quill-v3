//! Basic serialisable objects

use std::{
    fmt::{Debug, Display},
    ops::{Add, Deref, DerefMut, Sub},
};

use fcommon::{Label, LabelType, Path, Report, ReportKind, Source, SourceSpan, Span, Spanned, Str};
use serde::{de::Visitor, ser::SerializeTuple, Deserialize, Serialize};

use crate::Db;

/// The place that an object in quill code came from.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Provenance {
    /// The object originated from being written directly in a quill source file.
    Quill(SourceSpan),
    Feather(SourceSpan),
    Synthetic,
}

impl Default for Provenance {
    fn default() -> Self {
        Provenance::Synthetic
    }
}

impl Provenance {
    pub fn report<M>(&self, report_kind: ReportKind) -> Report<M> {
        Report::new(
            report_kind,
            self.source()
                .expect("cannot create a report from synthetic provenance"),
            self.span().start,
        )
    }

    pub fn label<M>(&self, ty: LabelType) -> Label<M> {
        Label::new(
            self.source()
                .expect("cannot create a label from synthetic provenance"),
            self.span(),
            ty,
        )
    }
}

/// Attaches provenance data to a type.
///
/// # Common patterns
///
/// It is common to create a newtype wrapper as follows.
/// ```
/// # use fexpr::basic::WithProvenance;
/// # use std::ops::{Deref, DerefMut};
/// # use serde::{Serialize, Deserialize};
///
/// #[derive(Serialize, Deserialize, PartialEq, Eq)]
/// pub struct TContents;
///
/// #[derive(Serialize, Deserialize, PartialEq, Eq)]
/// pub struct T(pub WithProvenance<TContents>);
///
/// impl Deref for T {
///     type Target = TContents;
///
///     fn deref(&self) -> &Self::Target {
///         &self.0.contents
///     }
/// }
///
/// impl DerefMut for T {
///     fn deref_mut(&mut self) -> &mut Self::Target {
///         &mut self.0.contents
///     }
/// }
/// ```
#[derive(Serialize, Deserialize, Copy, Clone, PartialEq, Eq, Hash)]
pub struct WithProvenance<T> {
    /// The origin of the value.
    #[serde(default, skip_serializing_if = "is_default_value")]
    pub provenance: Provenance,
    /// The actual contents of the value.
    pub contents: T,
}

fn is_default_value<P>(provenance: &P) -> bool
where
    P: Default + PartialEq,
{
    *provenance == P::default()
}

impl<T> WithProvenance<T> {
    pub fn new_synthetic(contents: T) -> Self {
        Self {
            provenance: Provenance::Synthetic,
            contents,
        }
    }

    pub fn new_with_provenance(provenance: Provenance, contents: T) -> Self {
        Self {
            provenance,
            contents,
        }
    }
}

impl<T> Debug for WithProvenance<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            write!(f, "{:?}@{:#?}", self.provenance, self.contents)
        } else {
            write!(f, "{:?}@{:?}", self.provenance, self.contents)
        }
    }
}

impl<T> Deref for WithProvenance<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.contents
    }
}

impl<T> DerefMut for WithProvenance<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.contents
    }
}

impl Provenance {
    pub fn source(&self) -> Option<Source> {
        match self {
            Provenance::Quill(source_span) => Some(source_span.source),
            Provenance::Feather(source_span) => Some(source_span.source),
            Provenance::Synthetic => None,
        }
    }
}

impl Spanned for Provenance {
    /// Returns the span, or `0..0` if it was synthetic.
    fn span(&self) -> Span {
        match self {
            Provenance::Quill(source_span) => source_span.span,
            Provenance::Feather(source_span) => source_span.span,
            Provenance::Synthetic => Span { start: 0, end: 0 },
        }
    }
}

/// A single indivisible lexical unit in an identifier, variable, or so on.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Name(pub WithProvenance<Str>);

impl Deref for Name {
    type Target = Str;

    fn deref(&self) -> &Self::Target {
        &self.0.contents
    }
}

impl DerefMut for Name {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0.contents
    }
}

impl Debug for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

// We need a custom Serialize/Deserialize impl for Name.
// Because `Str` is not a struct, `#[flatten]` doesn't work.

impl Serialize for Name {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        if self.0.provenance == Provenance::default() {
            self.deref().serialize(serializer)
        } else {
            let mut s = serializer.serialize_tuple(2)?;
            s.serialize_element(&self.0.provenance)?;
            s.serialize_element(self.deref())?;
            s.end()
        }
    }
}

#[derive(Default)]
struct NameVisitor;

impl<'de> Visitor<'de> for NameVisitor {
    type Value = Name;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a string or a 2-tuple")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Name(WithProvenance {
            provenance: Provenance::default(),
            contents: Str::deserialise(v.to_owned()),
        }))
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        let provenance = seq.next_element()?.ok_or_else(|| {
            serde::de::Error::invalid_value(serde::de::Unexpected::Other("data"), &"provenance")
        })?;
        let contents = seq.next_element()?.ok_or_else(|| {
            serde::de::Error::invalid_value(serde::de::Unexpected::Other("data"), &"contents")
        })?;
        Ok(Name(WithProvenance {
            provenance,
            contents,
        }))
    }
}

impl<'de> Deserialize<'de> for Name {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(NameVisitor::default())
    }
}

/// A qualified name that may have been written in code, rather than one simply stored internally
/// that was never written in code (see [`fcommon::Path`] for that use case).
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, Hash)]
pub struct QualifiedName(pub WithProvenance<Vec<Name>>);

impl Deref for QualifiedName {
    type Target = Vec<Name>;

    fn deref(&self) -> &Self::Target {
        &self.0.contents
    }
}

impl DerefMut for QualifiedName {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0.contents
    }
}

impl Debug for QualifiedName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl QualifiedName {
    pub fn from_path(db: &dyn Db, path: Path) -> Self {
        QualifiedName(WithProvenance {
            provenance: Provenance::default(),
            contents: path
                .segments(db)
                .iter()
                .map(|s| {
                    Name(WithProvenance {
                        provenance: Provenance::default(),
                        contents: *s,
                    })
                })
                .collect(),
        })
    }

    pub fn to_path(&self, db: &dyn Db) -> Path {
        Path::new(db, self.iter().map(|name| *name.deref()).collect())
    }

    pub fn display(&self, db: &dyn Db) -> String {
        self.to_path(db).display(db)
    }

    pub fn eq_ignoring_provenance(&self, other: &QualifiedName) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .zip(other.deref())
                .all(|(left, right)| left.deref() == right.deref())
    }

    pub fn replace_provenance(mut self, provenance: Provenance) -> Self {
        self.0.provenance = provenance;
        self
    }
}

#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeBruijnIndex(u32);

impl Display for DeBruijnIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)
    }
}

impl DeBruijnIndex {
    /// Constructs a de Bruijn index explicitly.
    /// Do not use this if possible, prefer [`Self::zero`] and [`Self::succ`].
    pub fn new(idx: u32) -> Self {
        Self(idx)
    }

    /// The lowest de Bruijn index.
    pub fn zero() -> DeBruijnIndex {
        Self(0)
    }

    /// The next (higher) de Bruijn index.
    pub fn succ(self) -> DeBruijnIndex {
        Self(self.0 + 1)
    }

    /// The previous (lower) de Bruijn index, or zero if one does not exist.
    pub fn pred(self) -> DeBruijnIndex {
        Self(self.0.saturating_sub(1))
    }
}

/// An offset for de Bruijn indices, which can be used to calculate relative indices.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeBruijnOffset(u32);

impl DeBruijnOffset {
    /// The zero offset.
    pub fn zero() -> DeBruijnOffset {
        Self(0)
    }

    /// Increase the offset by one.
    pub fn succ(self) -> DeBruijnOffset {
        Self(self.0 + 1)
    }

    pub fn new(offset: u32) -> DeBruijnOffset {
        Self(offset)
    }
}

impl Add<DeBruijnOffset> for DeBruijnIndex {
    type Output = DeBruijnIndex;

    fn add(self, rhs: DeBruijnOffset) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl Sub<DeBruijnOffset> for DeBruijnIndex {
    type Output = DeBruijnIndex;

    fn sub(self, rhs: DeBruijnOffset) -> Self::Output {
        Self(self.0.saturating_sub(rhs.0))
    }
}

impl Add for DeBruijnOffset {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl Sub for DeBruijnOffset {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0.saturating_sub(rhs.0))
    }
}
