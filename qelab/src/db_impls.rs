use fcommon::{Path, Report, ReportKind, Source, SourceType};
use fkernel::{
    definition::Definition,
    get_definition, get_inductive,
    inductive::{CertifiedInductive, Inductive},
    message,
    module::{module_from_feather_source, Item},
    result::{Dr, Message},
    typeck::{CertifiedDefinition, DefinitionOrigin},
};
use qparse::module_from_quill_source;

use crate::{definition::elaborate_definition, Db};

/// Retrieves the definition with the given name.
/// This definition will not have been type checked.
pub fn get_definition_impl(db: &dyn Db, path: Path) -> Dr<Definition> {
    let (source, name) = path.split_last(db);
    if let Some(module) =
        module_from_feather_source(db, Source::new(db, source, SourceType::Feather)).value()
    {
        let def = module.items.iter().find_map(|item| match item {
            Item::Definition(def) => {
                if *def.name == name {
                    Some(def.clone())
                } else {
                    None
                }
            }
            _ => None,
        });

        match def {
            Some(def) => Dr::ok(def),
            None => Dr::fail(
                Report::new_in_file(
                    ReportKind::Error,
                    Source::new(db, source, SourceType::Feather),
                )
                .with_message(message!["definition ", name, " could not be found"]),
            ),
        }
    } else {
        module_from_quill_source(db, Source::new(db, source, SourceType::Quill))
            .as_ref()
            .bind(|module| match module.iter().find(|def| *def.name == name) {
                Some(def) => {
                    elaborate_definition(db, Source::new(db, source, SourceType::Quill), def)
                }
                None => Dr::fail(
                    Report::new_in_file(
                        ReportKind::Error,
                        Source::new(db, source, SourceType::Quill),
                    )
                    .with_message(message![
                        "definition ",
                        name,
                        " could not be found"
                    ]),
                ),
            })
    }
}

/// Retrieves the inductive with the given name.
/// This inductive will not have been type checked.
pub fn get_inductive_impl(db: &dyn Db, path: Path) -> Dr<Inductive> {
    let (source, name) = path.split_last(db);
    module_from_feather_source(db, Source::new(db, source, SourceType::Feather))
        .as_ref()
        .map_messages(Message::new)
        .map(|module| {
            module.items.iter().find_map(|item| match item {
                Item::Inductive(ind) => {
                    if *ind.name == name {
                        Some(ind.clone())
                    } else {
                        None
                    }
                }
                _ => None,
            })
        })
        .bind(|ind| match ind {
            Some(ind) => Dr::ok(ind),
            None => Dr::fail(
                Report::new_in_file(
                    ReportKind::Error,
                    Source::new(db, source, SourceType::Feather),
                )
                .with_message(message!["inductive ", name, " could not be found"]),
            ),
        })
}

/// Type checks the definition with the given name.
/// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
///
/// # Usage
///
/// When type checking a definition, we may depend on previously certified definitions.
/// These should only be accessed using [`Db::get_certified_definition`], so that we don't double any error messages emitted.
pub fn certify_definition_impl(db: &dyn Db, path: Path) -> Dr<CertifiedDefinition> {
    get_definition(db, path).as_ref().bind(|def| {
        let origin = DefinitionOrigin::Feather;
        fkernel::typeck::certify_definition(db, path, def, origin)
    })
}

/// Type checks the inductive with the given name.
/// This function returns a [`CertifiedInductive`], an inductive that has been verified by the type checker.
///
/// # Usage
///
/// When certifying a definition or inductive, we may depend on previously certified inductives.
/// These should only be accessed using [`Db::get_certified_inductive`], so that we don't double any error messages emitted.
pub fn certify_inductive_impl(db: &dyn Db, path: Path) -> Dr<CertifiedInductive> {
    get_inductive(db, path)
        .as_ref()
        .bind(|ind| fkernel::inductive::certify_inductive(db, path, ind))
}
