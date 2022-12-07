use serde::{Deserialize, Serialize};

use crate::basic::{Name, WithProvenance};

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct IntroRule<P, E>
where
    P: Default + PartialEq,
{
    /// The unique name of this introduction rule.
    pub name: Name<P>,
    /// The type represented by this introduction rule.
    /// For instance, a structure `Foo` with one field `foo: T` might have a introduction rule with type `(foo: T) -> Foo`.
    pub ty: E,
}

/// An inductive data type.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct InductiveContents<P, E>
where
    P: Default + PartialEq,
{
    /// The name of this inductive data type inside the current module.
    pub name: Name<P>,
    /// A list of strings representing names of universe parameters.
    pub universe_params: Vec<Name<P>>,
    /// The type of the inductive data type.
    /// If there are no parameters, this will be something like `Sort u`.
    /// If there are type parameters, say `(a: T)`, it will be a function from this `T` to a sort.
    pub ty: E,
    /// Given that `ty` is an n-ary (dependent) function to some [`Sort`], how many of the first parameters
    /// to this function are "global"? All introduction rules must have the same sequence of global parameters,
    /// but may have different sequences of index parameters (the name for non-global parameters).
    /// This number must be at most `n`, if `ty` is an n-ary function. This is guaranteed if this [`Inductive`]
    /// has been certified by the kernel.
    pub global_params: u32,
    /// A list of all of the introduction rules associated with this inductive data type.
    pub intro_rules: Vec<IntroRule<P, E>>,
}

pub type Inductive<P, E> = WithProvenance<P, InductiveContents<P, E>>;
