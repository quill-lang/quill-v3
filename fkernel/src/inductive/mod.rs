use fcommon::{Dr, Path, Report, ReportKind, Source, SourceType};
use fexpr::{
    basic::Provenance, expr::Expression, inductive::Inductive, queries::module_from_feather_source,
};

use crate::Db;

mod check_type;
mod check_variant;

/// Retrieves the definition with the given name.
/// This definition will not have been type checked.
#[salsa::tracked(return_ref)]
pub fn get_inductive(db: &dyn Db, path: Path) -> Dr<Inductive<Provenance, Box<Expression>>> {
    let (source, name) = path.split_last(db);
    module_from_feather_source(db, Source::new(db, source, SourceType::Feather))
        .as_ref()
        .map(|module| {
            module.items.iter().find_map(|item| match item {
                fexpr::module::Item::Inductive(ind) => {
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
                .with_message(format!("inductive {} could not be found", name.text(db))),
            ),
        })
}

/// Type checks the inductive with the given name.
/// This function returns a [`CertifiedInductive`], an inductive that has been verified by the type checker.
///
/// # Usage
///
/// When certifying a definition or inductive, we may depend on previously certified inductives.
/// These should only be accessed using [`get_certified_inductive`], so that we don't double any error messages emitted.
#[salsa::tracked(return_ref)]
pub fn certify_inductive(db: &dyn Db, path: Path) -> Dr<()> {
    check_type::check_inductive_type(db, path).bind(|info| {
        Dr::sequence_unfail(
            info.inductive
                .variants
                .iter()
                .map(|variant| check_variant::check_variant(db, &info, variant)),
        )
        .deny()
        .map(|_| ())
    })
}

/// Type checks the definition with the given name, or retrieves it from the database if it was already type checked.
/// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
/// This function will discard any diagnostic messages produced by type checking the definition.
pub fn get_certified_inductive(db: &dyn Db, path: Path) -> Option<&()> {
    certify_inductive(db, path).value().as_ref()
}
