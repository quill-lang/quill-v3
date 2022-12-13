//! Basic serialisable objects

use std::{
    fmt::{Debug, Display},
    ops::{Add, Deref, DerefMut},
};

use fcommon::{Label, LabelType, Path, Report, ReportKind, Source, SourceSpan, Span, Str};
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
    pub fn report(&self, report_kind: ReportKind) -> Report {
        Report::new(report_kind, self.source().unwrap(), self.span().start)
    }

    pub fn label(&self, ty: LabelType) -> Label {
        Label::new(self.source().unwrap(), self.span(), ty)
    }
}

/// Attaches provenance data to a type.
/// Parametric over the type `P` of provenance data used.
/// Typically, `P` is either [`Provenance`] or `()`.
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
/// pub struct T<P: Default + PartialEq>(pub WithProvenance<P, TContents>);
///
/// impl<P: Default + PartialEq> Deref for T<P> {
///     type Target = TContents;
///
///     fn deref(&self) -> &Self::Target {
///         &self.0.contents
///     }
/// }
///
/// impl<P: Default + PartialEq> DerefMut for T<P> {
///     fn deref_mut(&mut self) -> &mut Self::Target {
///         &mut self.0.contents
///     }
/// }
/// ```
#[derive(Serialize, Deserialize, Copy, Clone, PartialEq, Eq, Hash)]
pub struct WithProvenance<P, T>
where
    P: Default + PartialEq,
{
    /// The origin of the value.
    #[serde(default, skip_serializing_if = "is_default_value")]
    pub provenance: P,
    /// The actual contents of the value.
    pub contents: T,
}

fn is_default_value<P>(provenance: &P) -> bool
where
    P: Default + PartialEq,
{
    *provenance == P::default()
}

impl<T> WithProvenance<(), T> {
    pub fn new(contents: T) -> Self {
        Self {
            provenance: (),
            contents,
        }
    }
}

impl<T> WithProvenance<Provenance, T> {
    pub fn without_provenance(self) -> WithProvenance<(), T> {
        WithProvenance {
            provenance: (),
            contents: self.contents,
        }
    }

    pub fn new_with_span(source_span: SourceSpan, contents: T) -> Self {
        Self {
            provenance: Provenance::Feather(source_span),
            contents,
        }
    }

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

impl<P, T> Debug for WithProvenance<P, T>
where
    P: Debug + Default + PartialEq,
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

impl<P, T> Deref for WithProvenance<P, T>
where
    P: Default + PartialEq,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.contents
    }
}

impl<P, T> DerefMut for WithProvenance<P, T>
where
    P: Default + PartialEq,
{
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

    /// Returns the span, or `0..0` if it was synthetic.
    pub fn span(&self) -> Span {
        match self {
            Provenance::Quill(source_span) => source_span.span,
            Provenance::Feather(source_span) => source_span.span,
            Provenance::Synthetic => Span { start: 0, end: 0 },
        }
    }
}

/// A single indivisible lexical unit in an identifier, variable, or so on.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Name<P>(pub WithProvenance<P, Str>)
where
    P: Default + PartialEq;

impl<P> Deref for Name<P>
where
    P: Default + PartialEq,
{
    type Target = Str;

    fn deref(&self) -> &Self::Target {
        &self.0.contents
    }
}

impl<P> DerefMut for Name<P>
where
    P: Default + PartialEq,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0.contents
    }
}

impl<P> Debug for Name<P>
where
    P: Default + PartialEq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<P> Name<P>
where
    P: Default + PartialEq,
{
    pub fn without_provenance(&self) -> Name<()> {
        Name(WithProvenance::new(**self))
    }

    pub fn synthetic(&self) -> Name<Provenance> {
        Name(WithProvenance::new_synthetic(**self))
    }
}

// We need a custom Serialize/Deserialize impl for Name.
// Because `Str` is not a struct, `#[flatten]` doesn't work.

impl<P> Serialize for Name<P>
where
    P: Default + PartialEq + Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        if self.0.provenance == P::default() {
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
struct NameVisitor<P> {
    _phantom: std::marker::PhantomData<P>,
}

impl<'de, P> Visitor<'de> for NameVisitor<P>
where
    P: Default + Deserialize<'de> + PartialEq,
{
    type Value = Name<P>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a string or a 2-tuple")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Name(WithProvenance {
            provenance: P::default(),
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

impl<'de, P> Deserialize<'de> for Name<P>
where
    P: Default + PartialEq + Deserialize<'de>,
{
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
pub struct QualifiedName<P>(pub WithProvenance<P, Vec<Name<P>>>)
where
    P: Default + PartialEq;

impl<P> Deref for QualifiedName<P>
where
    P: Default + PartialEq,
{
    type Target = Vec<Name<P>>;

    fn deref(&self) -> &Self::Target {
        &self.0.contents
    }
}

impl<P> DerefMut for QualifiedName<P>
where
    P: Default + PartialEq,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0.contents
    }
}

impl<P> Debug for QualifiedName<P>
where
    P: Default + PartialEq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<P> QualifiedName<P>
where
    P: Default + PartialEq,
{
    pub fn to_path(&self, db: &dyn Db) -> Path {
        Path::new(db, self.iter().map(|name| *name.deref()).collect())
    }

    pub fn display(&self, db: &dyn Db) -> String {
        self.to_path(db).display(db)
    }

    pub fn eq_ignoring_provenance(&self, other: &QualifiedName<P>) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .zip(other.deref())
                .all(|(left, right)| left.deref() == right.deref())
    }
}

impl<P> QualifiedName<P>
where
    P: Default + PartialEq,
{
    pub fn without_provenance(&self) -> QualifiedName<()> {
        QualifiedName(WithProvenance {
            provenance: (),
            contents: self
                .0
                .contents
                .iter()
                .map(Name::without_provenance)
                .collect(),
        })
    }

    pub fn synthetic(&self) -> QualifiedName<Provenance> {
        QualifiedName(WithProvenance::new_synthetic(
            self.0.contents.iter().map(Name::synthetic).collect(),
        ))
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
}

impl Add<DeBruijnOffset> for DeBruijnIndex {
    type Output = DeBruijnIndex;

    fn add(self, rhs: DeBruijnOffset) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}
