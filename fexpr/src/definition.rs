use serde::{Serialize, Deserialize};

use crate::{
    basic::{Name, WithProvenance},
    expr::Expression,
};

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct DefinitionContents {
    /// The name of this definition inside the current module.
    pub name: Name,
    /// A list of strings representing names of universe parameters.
    pub universe_params: Vec<Name>,
    /// The type of the definition.
    pub ty: Expression,
    /// The value of the definition.
    pub expr: Option<Expression>,
}

pub type Definition = WithProvenance<DefinitionContents>;
