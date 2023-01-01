use serde::{Deserialize, Serialize};

use crate::{
    basic::{Name, WithProvenance},
    expr::HeapExpression,
};

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct DefinitionContents {
    /// The name of this definition inside the current module.
    pub name: Name,
    /// A list of strings representing names of universe parameters.
    pub universe_params: Vec<Name>,
    /// The type of the definition.
    pub ty: HeapExpression,
    /// The value of the definition.
    pub expr: Option<HeapExpression>,
}

pub type Definition = WithProvenance<DefinitionContents>;
