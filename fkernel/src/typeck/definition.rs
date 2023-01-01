use std::fmt::Display;

use crate::{definition::Definition, expr::Sort};
use fcommon::Path;
use serde::{Deserialize, Serialize};

/// A definition that has been verified by the type checker.
/// No data inside a certified definition can be changed; this preserves the certification status.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct CertifiedDefinition {
    def: Definition,
    /// The type of the type of the definition, stored as a sort.
    sort: Sort,
    reducibility_hints: ReducibilityHints,
    /// Why this definition exists.
    origin: DefinitionOrigin,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub enum DefinitionOrigin {
    /// This definition was written directly in Feather code.
    Feather,
    /// This definition is the type declaration for an inductive type.
    TypeDeclaration { inductive: Path },
    /// This definition is an intro rule for an inductive type.
    IntroRule { inductive: Path },
}

impl CertifiedDefinition {
    pub(in crate::typeck) fn new(
        def: Definition,
        sort: Sort,
        reducibility_hints: ReducibilityHints,
        origin: DefinitionOrigin,
    ) -> Self {
        Self {
            def,
            sort,
            reducibility_hints,
            origin,
        }
    }

    pub fn def(&self) -> &Definition {
        &self.def
    }

    pub fn sort(&self) -> &Sort {
        &self.sort
    }

    pub fn reducibility_hints(&self) -> &ReducibilityHints {
        &self.reducibility_hints
    }

    pub fn origin(&self) -> &DefinitionOrigin {
        &self.origin
    }
}

/// Hints used by the definitional equality checker to choose which definitions to unfold first.
/// In particular, if we are checking if `f x y z` is equal to `g a b c`, we look at the
/// reducibility hints of `f` and `g`. If one has a heigher height than the other, we unfold
/// that one first, as it may reduce into an invocation of the other function. This essentially
/// allows us to unfold complicated expressions into easier ones, rather than having to unfold
/// all expressions into normal form, which would be very computationally intensive.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ReducibilityHints {
    Regular {
        height: DefinitionHeight,
    },
    /// Opaque definitions are never unfolded.
    /// They do not have a definition height.
    Opaque,
}

impl Display for ReducibilityHints {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReducibilityHints::Regular { height } => {
                write!(f, "regular definition with height {height}")
            }
            ReducibilityHints::Opaque => write!(f, "opaque definition"),
        }
    }
}

/// If this number is higher, the definition is 'more complex'.
/// We define the height of a [`ReducibilityHints::Regular`] definition to be one more than
/// the maximum height of any [`ReducibilityHints::Regular`] definitions it contains.
pub type DefinitionHeight = u64;
