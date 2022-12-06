use std::{
    fmt::Display,
    ops::{Add, Deref, DerefMut},
};

use fcommon::{Intern, Path, PathData, Source, SourceSpan, Span, Str};
use serde::{Deserialize, Serialize};

/// The place the node came from.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Provenance {
    /// The node originated from being written directly in a quill source file.
    Quill(SourceSpan),
    Feather(SourceSpan),
    Synthetic,
}

/// Attaches provenance data to a type.
///
/// # Common patterns
///
/// It is common to create a newtype wrapper as follows.
/// ```
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
    pub provenance: Provenance,
    /// The actual contents of the value.
    pub contents: T,
}

impl<T> std::fmt::Debug for WithProvenance<T>
where
    T: std::fmt::Debug,
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
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, Hash)]
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

impl std::fmt::Debug for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
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

impl std::fmt::Debug for QualifiedName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl QualifiedName {
    pub fn to_path(&self, intern: &dyn Intern) -> Path {
        intern.intern_path_data(PathData(self.iter().map(|name| *name.deref()).collect()))
    }

    pub fn display(&self, intern: &dyn Intern) -> String {
        self.to_path(intern).display(intern)
    }

    pub fn eq_ignoring_provenance(&self, other: &QualifiedName) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .zip(other.deref())
                .all(|(left, right)| left.deref() == right.deref())
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

/// A documentation string.
/// Even though this isn't a single identifier, it's still represented as a [Name].
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq)]
pub struct Documentation(pub WithProvenance<Str>);
