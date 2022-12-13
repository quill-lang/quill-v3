//! This file adapts quantitative type theory to add the additional element [`Ownership::ReadOnly`].

use std::ops::Mul;

use serde::{Deserialize, Serialize};

/// Represents the extent to which we own a given resource.
/// Local variables in an environment Γ are given an [`Ownership`].
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Ownership {
    /// We know that the resource exists, but do not own it at all.
    /// This is commonly used to encode values that might be known at compile time but are erased,
    /// or values of proofs which can be erased due to proof irrelevance.
    ///
    /// In arithmetic, this functions like a zero value `0`.
    Zero,
    /// We may borrow the resource, but we cannot use it linearly.
    ///
    /// In arithmetic, this functions like an infinitesimal `epsilon`.
    ReadOnly,
    /// We own the resource (linearly).
    /// This is the only type of ownership that we cannot easily delete or clone; linear ownership represents a resource
    /// that must be managed and freed.
    ///
    /// In arithmetic, this functions like a unit value `1`.
    Owned,
    /// We own the resource, and can copy it.
    /// Resources owned in a copyable way must reside entirely on the stack, similarly to Rust's [`Copy`] trait.
    /// Whenever it is used in a linear setting, we copy the value instead of moving it.
    ///
    /// In arithmetic, this functions like an infinity denoted `infinity`.
    /// In particular, it is stronger than the [`ReadOnly`] infinitesimal, so `epsilon * infinity = infinity`.
    Copyable,
}

pub use Ownership::*;

impl Mul for Ownership {
    type Output = Ownership;

    /// Suppose we have an expression `y` that needs `a`-ownership of a value `x`.
    /// Then, to own `y` with `b`-ownership, we need `a * b`-ownership of `x`.
    /// Multiplication is commutative: `a * b = b * a`.
    ///
    /// # Definition
    ///
    /// - `0 * a = a * 0 = 0`, so if either `y` or `x` have zero ownership (i.e. are erased), the resulting value is also erased.
    /// - `infinity * a = a * infinity = infinity` when `a != 0`.
    ///     If `x` is copyable or `y` is copyable, we need to own the value `x` in a copyable way, unless it is erased.
    /// - `1 * a = a * 1 = a`.
    ///     For example, if `y` is simply owned, the ownership of `x` required to construct `y` is exactly `a`.
    /// - `epsilon * epsilon = epsilon`: this is double borrow elimination `&&a -> &a`.
    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Zero, _) | (_, Zero) => Zero,
            (Copyable, _) | (_, Copyable) => Copyable,
            (Owned, a) | (a, Owned) => a,
            (ReadOnly, ReadOnly) => ReadOnly,
        }
    }
}

impl Ownership {
    /// Suppose that we have a process `p` in which we need `a`-ownership and a process `q` in which we need `b`-ownership.
    /// The ownership required to execute the composed process "`p` then `q`" is then `a.then(b)`, denoted `a |> b` in docstrings.
    /// This operation is non-commutative.
    ///
    /// # Definition
    ///
    /// - `0 |> a = a |> 0 = a`.
    ///     If we sequence a process that requires `a`-ownership with one that does not, the composition requires `a`-ownership.
    /// - `infinity |> a = a |> infinity = infinity`.
    ///     If either part of the computation requires copyable ownership, then the composition also requires copyable ownership.
    /// - `1 |> epsilon = 1 |> 1 = infinity`.
    ///     After we have used a resource, we can't use it any more times, even for read-only accesses,
    ///     unless we copied the resource in the first place and did not use it linearly.
    /// - `epsilon |> epsilon = epsilon`: two sequential read-only accesses can be realised by a single read-only access.
    /// - `epsilon |> 1 = 1`.
    ///     If we read from a resource, we are allowed to subsequently use that resource.
    pub fn then(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Zero, a) | (a, Zero) => a,
            (Copyable, _) | (_, Copyable) => Copyable,
            (Owned, ReadOnly) | (Owned, Owned) => Copyable,
            (ReadOnly, ReadOnly) => ReadOnly,
            (ReadOnly, Owned) => Owned,
        }
    }
}

/// Is a value erased at runtime or not?
///
/// Values created by expressions are given an [`Erasure`] (not an [`Ownership`]).
/// This corresponds to the fact that in quantitative type theory, conclusion judgments may only take multiplicities in {0, 1}.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Erasure {
    /// This value is erased.
    /// Proofs of propositions, as well as types, are typically erased.
    /// Corresponds to [`Zero`].
    Erased,
    /// This value is not erased.
    /// Corresponds to [`Owned`].
    NotErased,
}

/// The possible ownership states for a bound variable, such as a function parameter.
/// More precisely, this is [`Ownership`] without [`ReadOnly`].
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParameterOwnership {
    /// See [`Zero`].
    PZero,
    /// See [`Owned`].
    POwned,
    /// See [`Copyable`].
    PCopyable,
}

/// Can this function be invoked exactly once (linearly) or many times (from behind a borrow)?
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InvocationType {
    /// The function must be executed exactly once, because such functions have no destructors and may own linear resources.
    /// Corresponds roughly to Rust's [`FnOnce`] without [`Drop`].
    Once,
    /// The function may be executed arbitrarily many times (including zero).
    /// Such functions are invoked from behind borrows.
    /// They may capture no linear resources, and hence they have destructors and a cloning function.
    /// Corresponds roughly to Rust's [`Fn`] + [`Clone`].
    Many,
}
