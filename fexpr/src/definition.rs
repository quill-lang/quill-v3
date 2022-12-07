use serde::{Deserialize, Serialize};

use crate::basic::{Name, WithProvenance};

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefinitionContents<P, E>
where
    P: Default + PartialEq,
{
    /// The name of this definition inside the current module.
    pub name: Name<P>,
    /// A list of strings representing names of universe parameters.
    pub universe_params: Vec<Name<P>>,
    /// The type of the definition.
    pub ty: E,
    /// The value of the definition.
    pub expr: Option<E>,
}

pub type Definition<P, E> = WithProvenance<P, DefinitionContents<P, E>>;
