use std::fmt::Debug;
use std::ops::{Deref, DerefMut};

use fcommon::{with_local_database, ParametricDr, Report, ReportKind, Source, Str};
use serde::{Deserialize, Serialize};

use crate::basic::WithProvenance;
use crate::definition::Definition;
use crate::inductive::Inductive;
use crate::Db;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct ModuleContents {
    pub items: Vec<Item>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub enum Item {
    Definition(Definition),
    Inductive(Inductive),
}

#[derive(Serialize, Deserialize, PartialEq, Eq)]
pub struct Module(pub WithProvenance<ModuleContents>);

impl Deref for Module {
    type Target = ModuleContents;

    fn deref(&self) -> &Self::Target {
        &self.0.contents
    }
}

impl DerefMut for Module {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0.contents
    }
}

impl Debug for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "module {:?}:\n{:?}", self.0.provenance, self.deref())
    }
}

impl Module {
    pub fn definition(&self, name: Str) -> Option<&Definition> {
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

    pub fn definition_mut(&mut self, name: Str) -> Option<&mut Definition> {
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
pub fn module_from_feather_source(db: &dyn Db, source: Source) -> ParametricDr<String, Module> {
    fcommon::source(db, source).bind(|file_contents| {
        with_local_database(db, || match ron::from_str(file_contents.contents(db)) {
            Ok(module) => ParametricDr::ok(module),
            Err(err) => ParametricDr::fail(
                Report::new_in_file(ReportKind::Error, source).with_message(err.to_string()),
            ),
        })
    })
}
