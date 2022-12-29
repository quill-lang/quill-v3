use std::fmt::Debug;
use std::ops::{Deref, DerefMut};

use fcommon::{with_local_database, ParametricDr, Report, ReportKind, Source, Str};
use serde::{Deserialize, Serialize};

use crate::basic::{Provenance, WithProvenance};
use crate::definition::Definition;
use crate::expr::Expression;
use crate::inductive::Inductive;
use crate::Db;

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

#[tracing::instrument(level = "debug")]
#[salsa::tracked(return_ref)]
pub fn module_from_feather_source(
    db: &dyn Db,
    source: Source,
) -> ParametricDr<String, Module<Provenance, Box<Expression>>> {
    fcommon::source(db, source).bind(|file_contents| {
        with_local_database(db, || match ron::from_str(file_contents.contents(db)) {
            Ok(module) => ParametricDr::ok(module),
            Err(err) => ParametricDr::fail(
                Report::new_in_file(ReportKind::Error, source).with_message(err.to_string()),
            ),
        })
    })
}
