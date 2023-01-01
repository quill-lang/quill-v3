// TODO: Document this module, taking care to detail each universe operation.

use crate::basic::*;
use serde::{Deserialize, Serialize};

/// A concrete universe level.
/// Level `0` represents `Prop`, the type of (proof-irrelevant) propositions.
/// Level `1` represents `Type`, the type of all (small) types.
pub type UniverseLevel = u32;

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct UniverseZero;

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct UniverseVariable(pub Name);

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct UniverseSucc(pub Box<Universe>);

/// Takes the larger universe of `left` and `right`.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct UniverseMax {
    pub left: Box<Universe>,
    pub right: Box<Universe>,
}

/// Takes the larger universe of `left` and `right`, but if `right == 0`, then this just gives `0`.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct UniverseImpredicativeMax {
    pub left: Box<Universe>,
    pub right: Box<Universe>,
}

/// An inference variable for universes.
/// May represent any universe.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Metauniverse(u32);

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub enum UniverseContents {
    UniverseZero,
    UniverseVariable(UniverseVariable),
    UniverseSucc(UniverseSucc),
    UniverseMax(UniverseMax),
    UniverseImpredicativeMax(UniverseImpredicativeMax),
    Metauniverse(Metauniverse),
}

pub type Universe = WithProvenance<UniverseContents>;

impl Universe {
    /// Compares two universes for equality, ignoring provenance data.
    pub fn eq_ignoring_provenance(&self, other: &Universe) -> bool {
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

impl Universe {
    /// Returns a dummy universe.
    /// Should not be used for anything.
    pub fn dummy() -> Universe {
        Universe {
            provenance: Provenance::Synthetic,
            contents: UniverseContents::UniverseZero,
        }
    }
}

impl Universe {
    /// If this universe is syntactically equal to `Sort k` for some integer `k`, return `k`.
    pub fn to_explicit_universe(&self) -> Option<UniverseLevel> {
        match &self.contents {
            UniverseContents::UniverseZero => Some(0),
            UniverseContents::UniverseSucc(inner) => inner.0.to_explicit_universe().map(|n| n + 1),
            _ => None,
        }
    }
}
