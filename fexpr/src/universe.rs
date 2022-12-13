// TODO: Document this module, taking care to detail each universe operation.

use crate::basic::*;
use fcommon::SourceSpan;
use serde::{Deserialize, Serialize};

/// A concrete universe level.
/// Level `0` represents `Prop`, the type of (proof-irrelevant) propositions.
/// Level `1` represents `Type`, the type of all (small) types.
pub type UniverseLevel = u32;

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct UniverseZero;

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct UniverseVariable<P>(pub Name<P>)
where
    P: Default + PartialEq;

impl<P> UniverseVariable<P>
where
    P: Default + PartialEq,
{
    pub fn without_provenance(&self) -> UniverseVariable<()> {
        UniverseVariable(self.0.without_provenance())
    }
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct UniverseSucc<P>(pub Box<Universe<P>>)
where
    P: Default + PartialEq;

impl<P> UniverseSucc<P>
where
    P: Default + PartialEq,
{
    pub fn without_provenance(&self) -> UniverseSucc<()> {
        UniverseSucc(Box::new(self.0.without_provenance()))
    }
}

/// Takes the larger universe of `left` and `right`.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct UniverseMax<P>
where
    P: Default + PartialEq,
{
    pub left: Box<Universe<P>>,
    pub right: Box<Universe<P>>,
}

impl<P> UniverseMax<P>
where
    P: Default + PartialEq,
{
    pub fn without_provenance(&self) -> UniverseMax<()> {
        UniverseMax {
            left: Box::new(self.left.without_provenance()),
            right: Box::new(self.right.without_provenance()),
        }
    }
}

/// Takes the larger universe of `left` and `right`, but if `right == 0`, then this just gives `0`.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct UniverseImpredicativeMax<P>
where
    P: Default + PartialEq,
{
    pub left: Box<Universe<P>>,
    pub right: Box<Universe<P>>,
}

impl<P> UniverseImpredicativeMax<P>
where
    P: Default + PartialEq,
{
    pub fn without_provenance(&self) -> UniverseImpredicativeMax<()> {
        UniverseImpredicativeMax {
            left: Box::new(self.left.without_provenance()),
            right: Box::new(self.right.without_provenance()),
        }
    }
}

/// An inference variable for universes.
/// May represent any universe.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Metauniverse(u32);

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub enum UniverseContents<P>
where
    P: Default + PartialEq,
{
    UniverseZero,
    UniverseVariable(UniverseVariable<P>),
    UniverseSucc(UniverseSucc<P>),
    UniverseMax(UniverseMax<P>),
    UniverseImpredicativeMax(UniverseImpredicativeMax<P>),
    Metauniverse(Metauniverse),
}

impl<P> UniverseContents<P>
where
    P: Default + PartialEq,
{
    pub fn without_provenance(&self) -> UniverseContents<()> {
        match self {
            UniverseContents::UniverseZero => UniverseContents::UniverseZero,
            UniverseContents::UniverseVariable(var) => {
                UniverseContents::UniverseVariable(var.without_provenance())
            }
            UniverseContents::UniverseSucc(succ) => {
                UniverseContents::UniverseSucc(succ.without_provenance())
            }
            UniverseContents::UniverseMax(max) => {
                UniverseContents::UniverseMax(max.without_provenance())
            }
            UniverseContents::UniverseImpredicativeMax(imax) => {
                UniverseContents::UniverseImpredicativeMax(imax.without_provenance())
            }
            UniverseContents::Metauniverse(meta) => UniverseContents::Metauniverse(*meta),
        }
    }
}

pub type Universe<P> = WithProvenance<P, UniverseContents<P>>;

#[salsa::interned]
pub struct Univ {
    pub value: Universe<()>,
}

impl Universe<Provenance> {
    pub fn new_with_span(source_span: SourceSpan, contents: UniverseContents<Provenance>) -> Self {
        Self {
            provenance: Provenance::Feather(source_span),
            contents,
        }
    }

    pub fn new_synthetic(contents: UniverseContents<Provenance>) -> Self {
        Self {
            provenance: Provenance::Synthetic,
            contents,
        }
    }

    pub fn new_with_provenance(
        provenance: Provenance,
        contents: UniverseContents<Provenance>,
    ) -> Self {
        Self {
            provenance,
            contents,
        }
    }
}

impl<P> Universe<P>
where
    P: Default + PartialEq,
{
    pub fn without_provenance(&self) -> Universe<()> {
        Universe {
            provenance: (),
            contents: self.contents.without_provenance(),
        }
    }

    /// Compares two universes for equality, ignoring provenance data.
    pub fn eq_ignoring_provenance(&self, other: &Universe<P>) -> bool {
        match (&self.contents, &other.contents) {
            (UniverseContents::UniverseZero, UniverseContents::UniverseZero) => true,
            (
                UniverseContents::UniverseVariable(arg1),
                UniverseContents::UniverseVariable(arg2),
            ) => arg1.0 == arg2.0,
            (UniverseContents::UniverseSucc(arg1), UniverseContents::UniverseSucc(arg2)) => {
                arg1.0.eq_ignoring_provenance(&arg2.0)
            }
            (UniverseContents::UniverseMax(arg1), UniverseContents::UniverseMax(arg2)) => {
                arg1.left.eq_ignoring_provenance(&arg2.left)
                    && arg1.right.eq_ignoring_provenance(&arg2.right)
            }
            (
                UniverseContents::UniverseImpredicativeMax(arg1),
                UniverseContents::UniverseImpredicativeMax(arg2),
            ) => {
                arg1.left.eq_ignoring_provenance(&arg2.left)
                    && arg1.right.eq_ignoring_provenance(&arg2.right)
            }
            (UniverseContents::Metauniverse(arg1), UniverseContents::Metauniverse(arg2)) => {
                arg1.0 == arg2.0
            }
            _ => false,
        }
    }
}

impl Universe<()> {
    /// Returns a dummy universe.
    /// Should not be used for anything.
    pub fn dummy() -> Universe<()> {
        Universe {
            provenance: (),
            contents: UniverseContents::UniverseZero,
        }
    }
}

impl<P> Universe<P>
where
    P: Default + PartialEq,
{
    /// If this universe is syntactically equal to `Sort k` for some integer `k`, return `k`.
    pub fn to_explicit_universe(&self) -> Option<UniverseLevel> {
        match &self.contents {
            UniverseContents::UniverseZero => Some(0),
            UniverseContents::UniverseSucc(inner) => inner.0.to_explicit_universe().map(|n| n + 1),
            _ => None,
        }
    }
}
