use std::fmt::Debug;
use std::ops::{Deref, DerefMut};

use fcommon::Str;
use serde::{Deserialize, Serialize};

use crate::basic::WithProvenance;
use crate::definition::Definition;
use crate::inductive::Inductive;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct ModuleContents<P, E>
where
    P: Default + PartialEq,
{
    pub items: Vec<Item<P, E>>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub enum Item<P, E>
where
    P: Default + PartialEq,
{
    Definition(Definition<P, E>),
    Inductive(Inductive<P, E>),
}

#[derive(Serialize, Deserialize, PartialEq, Eq)]
pub struct Module<P, E>(pub WithProvenance<P, ModuleContents<P, E>>)
where
    P: Default + PartialEq;

impl<P, E> Deref for Module<P, E>
where
    P: Default + PartialEq,
{
    type Target = ModuleContents<P, E>;

    fn deref(&self) -> &Self::Target {
        &self.0.contents
    }
}

impl<P, E> DerefMut for Module<P, E>
where
    P: Default + PartialEq,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0.contents
    }
}

impl<P, E> Debug for Module<P, E>
where
    P: Debug + Default + PartialEq,
    E: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "module {:?}:\n{:?}", self.0.provenance, self.deref())
    }
}

impl<P, E> Module<P, E>
where
    P: Default + PartialEq,
{
    pub fn definition(&self, name: Str) -> Option<&Definition<P, E>> {
        self.deref().items.iter().find_map(|item| {
            if let Item::Definition(def) = item {
                if *def.deref().name == name {
                    Some(def)
                } else {
                    None
                }
            } else {
                None
            }
        })
    }

    pub fn definition_mut(&mut self, name: Str) -> Option<&mut Definition<P, E>> {
        self.0.contents.items.iter_mut().find_map(|item| {
            if let Item::Definition(def) = item {
                if *def.deref().name == name {
                    Some(def)
                } else {
                    None
                }
            } else {
                None
            }
        })
    }
}
