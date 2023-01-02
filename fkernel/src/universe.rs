//! TODO: Document this module, taking care to detail each universe operation.

// Allow this lint to increase readability in complex chains of logic.
#![allow(clippy::if_same_then_else)]

use std::ops::DerefMut;

use crate::basic::*;
use crate::Db;
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

    /// If this universe is syntactically equal to `Sort k` for some integer `k`, return `k`.
    pub fn to_explicit_universe(&self) -> Option<UniverseLevel> {
        match &self.contents {
            UniverseContents::UniverseZero => Some(0),
            UniverseContents::UniverseSucc(inner) => inner.0.to_explicit_universe().map(|n| n + 1),
            _ => None,
        }
    }

    /// Factors out the outermost sequence of [`UniverseSucc`] instances.
    /// If the input is `u + k` where `k` is an integer, we remove the `+ k` from the input and return `k`.
    fn remove_offset(&mut self) -> UniverseLevel {
        if let UniverseContents::UniverseSucc(UniverseSucc(inner)) = &mut self.contents {
            let result = inner.remove_offset();
            let inner = std::mem::replace(
                inner.deref_mut(),
                Universe::new_with_provenance(self.provenance, UniverseContents::UniverseZero),
            );
            *self = inner;
            result + 1
        } else {
            0
        }
    }

    /// Reverses [`to_universe_with_offset`] by adding iterated `+ 1` operations to this universe.
    fn add_offset(&mut self, levels_to_raise: UniverseLevel) {
        let mut contents = std::mem::replace(&mut self.contents, UniverseContents::UniverseZero);
        for _ in 0..levels_to_raise {
            contents = UniverseContents::UniverseSucc(UniverseSucc(Box::new(
                Universe::new_with_provenance(self.provenance, contents),
            )));
        }
        self.contents = contents;
    }

    /// Returns true if this universe is definitely not the zero universe, `Prop`.
    /// It is possible for [`is_zero`] and [`is_nonzero`] to both be false.
    pub fn is_nonzero(&self) -> bool {
        match &self.contents {
            UniverseContents::UniverseZero => false,
            UniverseContents::UniverseVariable(_) => false,
            UniverseContents::UniverseSucc(_) => true,
            UniverseContents::UniverseMax(max) => max.left.is_nonzero() || max.right.is_nonzero(),
            // Even if the left hand side of an `imax` is nonzero, the result is still zero if the right hand side is.
            UniverseContents::UniverseImpredicativeMax(imax) => imax.right.is_nonzero(),
            UniverseContents::Metauniverse(_) => false,
        }
    }

    /// Returns true if this universe is definitely zero.
    /// It is possible for [`is_zero`] and [`is_nonzero`] to both be false.
    pub fn is_zero(&self) -> bool {
        matches!(&self.contents, UniverseContents::UniverseZero)
    }

    /// Converts a universe to an equivalent, simpler, form.
    ///
    /// TODO: There may be a normalisation issue here still.
    pub fn normalise_universe(mut self, db: &dyn Db) -> Universe {
        // First, factor out the outermost `+ k` chain.
        let levels = self.remove_offset();
        match self.contents {
            UniverseContents::UniverseZero => {}
            UniverseContents::UniverseVariable(_) => {}
            UniverseContents::UniverseSucc(_) => {
                unreachable!("should have already factored out succ chain")
            }
            UniverseContents::UniverseMax(max) => {
                self = Self::normalise_max_chain(db, max, self.provenance);
            }
            UniverseContents::UniverseImpredicativeMax(mut imax) => {
                *imax.left = imax.left.normalise_universe(db);
                *imax.right = imax.right.normalise_universe(db);
                // We now need to check if we can perform a simplification on this `imax` operation.
                self = Self::normalise_imax(db, self.provenance, imax);
            }
            UniverseContents::Metauniverse(_) => {}
        }
        self.add_offset(levels);
        self
    }

    fn normalise_imax(
        db: &dyn Db,
        provenance: Provenance,
        imax: UniverseImpredicativeMax,
    ) -> Universe {
        if imax.right.is_nonzero() {
            // This is a regular max expression.
            Self::normalise_max_chain(
                db,
                UniverseMax {
                    left: imax.left,
                    right: imax.right,
                },
                provenance,
            )
        } else if imax.left.is_zero() || imax.right.is_zero() {
            // If the left parameter is zero, the result is the right parameter.
            // If the right parameter is zero, then the result is zero, which is the right parameter.
            *imax.right
        } else if imax.left == imax.right {
            // If the two parameters are equal we can just take one of them as the result.
            *imax.left
        } else {
            // Couldn't simplify.
            Universe::new_with_provenance(
                provenance,
                UniverseContents::UniverseImpredicativeMax(imax),
            )
        }
    }

    fn normalise_max_chain(db: &dyn Db, max: UniverseMax, provenance: Provenance) -> Universe {
        // Flatten out nested invocations of `max`, normalise all parameters, and flatten again.
        let mut args = Self::collect_max_args(max)
            .into_iter()
            .flat_map(|mut arg| {
                arg = arg.normalise_universe(db);
                if let UniverseContents::UniverseMax(inner) = arg.contents {
                    Self::collect_max_args(inner)
                } else {
                    vec![arg]
                }
            })
            .collect::<Vec<_>>();
        // Now, we sort the arguments so that easily comparable arguments are grouped.
        args.sort_by_key(|arg| match &arg.contents {
            UniverseContents::UniverseZero => 0,
            UniverseContents::UniverseSucc(_) => 1,
            UniverseContents::UniverseMax(_) => 2,
            UniverseContents::UniverseImpredicativeMax(_) => 3,
            UniverseContents::UniverseVariable(_) => 4,
            UniverseContents::Metauniverse(_) => 5,
        });
        // Collect the chain of arguments together.
        // We reverse the iterator so this behaves like a right-facing fold.
        args.into_iter()
            .rev()
            .reduce(|right, left| {
                Self::normalise_max(
                    UniverseMax {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    provenance,
                )
            })
            .expect("args should be nonempty")
    }

    fn collect_max_args(max: UniverseMax) -> Vec<Universe> {
        let mut left = if let UniverseContents::UniverseMax(inner) = max.left.contents {
            Self::collect_max_args(inner)
        } else {
            vec![*max.left]
        };
        let right = if let UniverseContents::UniverseMax(inner) = max.right.contents {
            Self::collect_max_args(inner)
        } else {
            vec![*max.right]
        };
        left.extend(right);
        left
    }

    fn normalise_max(mut max: UniverseMax, provenance: Provenance) -> Universe {
        if let (Some(left), Some(right)) = (max.left.to_explicit_universe(), max.right.to_explicit_universe()) {
        // We can compare the universes directly because we know their values.
        if left >= right {
            *max.left
        } else {
            *max.right
        }
    } else if max.left.is_zero() {
        // If the left parameter is zero, the result is the right parameter.
        *max.right
    } else if max.right.is_zero() {
        // If the right parameter is zero, the result is the left parameter.
        *max.left
    } else if max.left == max.right {
        // If the two parameters are equal we can just take one of them as the result.
        *max.left
    } else if let UniverseContents::UniverseMax(left_max) = &max.left.contents
        && (left_max.left == max.right || left_max.right == max.right) {
        // The result of `max (max a b) a` or `max (max a b) b` is `max a b`.
        *max.left
    } else if let UniverseContents::UniverseMax(right_max) = &max.right.contents
        && (right_max.left == max.left || right_max.right == max.left) {
        // The result of `max a (max a b)` or `max b (max a b)` is `max a b`.
        *max.right
    } else {
        // Try to factor out `+ k` chains from the left and right arguments.
        let left_levels = max.left.remove_offset();
        let right_levels = max.right.remove_offset();
        if max.left == max.right {
            // We can now compare levels directly.
            if left_levels >= right_levels {
                max.left.add_offset(left_levels);
                *max.left
            } else {
                max.right.add_offset( right_levels);
                *max.right
            }
        } else {
            // Couldn't simplify. Revert the `+ k` chains for now.
            max.left.add_offset( left_levels);
            max.right.add_offset( right_levels);
            Universe::new_with_provenance(provenance, UniverseContents::UniverseMax(max))
        }
    }
    }
}

enum ReplaceResult {
    /// The expression should not be replaced.
    Skip,
    /// The expression should be replaced with the given value.
    ReplaceWith(Universe),
}

impl Universe {
    fn replace(&mut self, replace_fn: &impl Fn(&Universe) -> ReplaceResult) {
        match replace_fn(self) {
            ReplaceResult::Skip => match &mut self.contents {
                UniverseContents::UniverseZero => {}
                UniverseContents::UniverseVariable(_) => {}
                UniverseContents::UniverseSucc(inner) => inner.0.replace(replace_fn),
                UniverseContents::UniverseMax(max) => {
                    max.left.replace(replace_fn);
                    max.right.replace(replace_fn);
                }
                UniverseContents::UniverseImpredicativeMax(imax) => {
                    imax.left.replace(replace_fn);
                    imax.right.replace(replace_fn);
                }
                UniverseContents::Metauniverse(_) => {}
            },
            ReplaceResult::ReplaceWith(replacement) => *self = replacement,
        }
    }

    /// Replace the given universe variable with the provided replacement.
    pub fn instantiate_universe_variable(
        &mut self,
        var: &UniverseVariable,
        replacement: &Universe,
    ) {
        self.replace(&|inner| match &inner.contents {
            UniverseContents::UniverseVariable(inner_var) => {
                if inner_var == var {
                    ReplaceResult::ReplaceWith(replacement.clone())
                } else {
                    ReplaceResult::Skip
                }
            }
            _ => ReplaceResult::Skip,
        })
    }

    /// Replace the given metauniverse with the provided replacement.
    pub fn instantiate_metauniverse(&mut self, meta: &Metauniverse, replacement: &Universe) {
        self.replace(&|inner| match &inner.contents {
            UniverseContents::Metauniverse(inner_meta) => {
                if *inner_meta == *meta {
                    ReplaceResult::ReplaceWith(replacement.clone())
                } else {
                    ReplaceResult::Skip
                }
            }
            _ => ReplaceResult::Skip,
        })
    }

    /// Returns true if the left universe is at most (<=) the right universe.
    pub fn universe_at_most(db: &dyn Db, left: Universe, right: Universe) -> bool {
        let mut left = left.normalise_universe(db);
        let mut right = right.normalise_universe(db);

        if left.eq_ignoring_provenance(&right) {
        true
    } else if left.is_zero() {
        // The zero universe is never greater than any other universe.
        true
    } else if let UniverseContents::UniverseMax(max) = left.contents {
        Self::universe_at_most(db, *max.left, right.clone()) && Self::universe_at_most(db, *max.right, right)
    } else if let UniverseContents::UniverseMax(max) = &right.contents &&
        (Self::universe_at_most(db, left.clone(), *max.left.clone()) ||
        Self::universe_at_most(db, left.clone(), *max.right.clone())) {
        true
    } else if let UniverseContents::UniverseImpredicativeMax(imax) = left.contents {
        Self::universe_at_most(db, *imax.left, right.clone()) &&
        Self::universe_at_most(db, *imax.right, right)
    } else if let UniverseContents::UniverseImpredicativeMax(imax) = right.contents {
        // We only need to check the right hand side of an impredicative max in this case.
        Self::universe_at_most(db, left, *imax.right)
    } else {
        let left_offset = left.remove_offset();
        let right_offset = right.remove_offset();
        if left == right {
            left_offset <= right_offset
        } else if left.is_zero() {
            left_offset <= right_offset
        } else if left_offset == right_offset && right_offset > 0 {
            Self::universe_at_most(db, left, right)
        } else {
            false
        }
    }
    }
}
