use serde::{Deserialize, Serialize};

use crate::{
    basic::{Name, WithProvenance},
    expr::{HeapExpression, NaryBinder},
};

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct Variant {
    /// The unique name of this variant.
    pub name: Name,
    /// The type of the introduction rule for this variant.
    /// Each binder represents a field, and the `result` should be the type of this inductive.
    ///
    /// The first parameters should be the global parameters to the inductive.
    /// The inductive being defined should occur strictly positively in each binder; intuitively, only in a
    /// covariant position such as `foo` or `_ -> foo` not `foo -> _`.
    pub intro_rule: NaryBinder<HeapExpression>,
}

/// An inductive data type.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct InductiveContents {
    /// The name of this inductive data type inside the current module.
    pub name: Name,
    /// A list of strings representing names of universe parameters.
    pub universe_params: Vec<Name>,
    /// The type of the inductive data type.
    /// If there are no parameters, this will be something like `Sort u`.
    /// If there are type parameters, say `(a: T)`, it will be a function from this `T` to a sort.
    pub ty: NaryBinder<HeapExpression>,
    /// Given that `ty` is an n-ary (dependent) function to some [`Sort`], how many of the first parameters
    /// to this function are "global"? All introduction rules must have the same sequence of global parameters,
    /// but may have different sequences of index parameters (the name for non-global parameters).
    /// This number must be at most `n`, if `ty` is an n-ary function. This is guaranteed if this [`Inductive`]
    /// has been certified by the kernel.
    pub global_params: u32,
    /// A list of all of the variants associated with this inductive data type.
    pub variants: Vec<Variant>,
}

pub type Inductive = WithProvenance<InductiveContents>;
