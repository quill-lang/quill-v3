use fcommon::{Dr, LabelType, Path, Report, ReportKind, Source, SourceType};
use fexpr::{
    basic::Provenance,
    definition::Definition,
    expr::{Expression, Sort},
    queries::module_from_feather_source,
};

use crate::{
    term::{first_local_or_metavariable, get_max_height},
    universe::normalise_universe,
    Db,
};

mod def;
mod defeq;
mod infer;
mod unfold;
mod whnf;

pub use def::*;
pub use defeq::*;
pub use infer::*;
pub use unfold::*;
pub use whnf::*;

/// Retrieves the definition with the given name.
/// This definition will not have been type checked.
#[salsa::tracked(return_ref)]
pub fn get_definition(db: &dyn Db, path: Path) -> Dr<Definition<Provenance, Box<Expression>>> {
    let (source, name) = path.split_last(db);
    module_from_feather_source(db, Source::new(db, source, SourceType::Feather))
        .as_ref()
        .map(|module| {
            module.items.iter().find_map(|item| match item {
                fexpr::module::Item::Definition(def) => {
                    if *def.name == name {
                        Some(def.clone())
                    } else {
                        None
                    }
                }
                _ => None,
            })
        })
        .bind(|def| match def {
            Some(def) => Dr::ok(def),
            None => Dr::fail(
                Report::new_in_file(
                    ReportKind::Error,
                    Source::new(db, source, SourceType::Feather),
                )
                .with_message(format!("definition {} could not be found", name.text(db))),
            ),
        })
}

pub fn check_no_local_or_metavariable(db: &dyn Db, e: &Expression) -> Dr<()> {
    if first_local_or_metavariable(db, e.to_term(db)).is_some() {
        Dr::fail(
            e.value.provenance.report(ReportKind::Error).with_label(
                e.value.provenance.label(LabelType::Error).with_message(
                    "could not certify definition as it contained an invalid expression",
                ),
            ),
        )
    } else {
        Dr::ok(())
    }
}

/// Type checks the definition with the given name.
/// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
///
/// # Usage
///
/// When type checking a definition, we may depend on previously certified definitions.
/// These should only be accessed using [`get_certified_definition`], so that we don't double any error messages emitted.
#[salsa::tracked(return_ref)]
pub fn certify_definition(db: &dyn Db, path: Path) -> Dr<CertifiedDefinition> {
    get_definition(db, path).as_ref().bind(|def| {
        let origin = DefinitionOrigin::Feather;

        check_no_local_or_metavariable(db, &def.contents.ty).bind(|()| {
            // Since we have no metavariables in the given expression,
            // we can initialise the metavariable generator with any value.
            // Check that the type of a definition is indeed a type.
            let sort =
                infer_type(db, def.contents.ty.to_term(db)).and_then(|sort| as_sort(db, sort));

            match sort {
                Ok(sort) => {
                    let sort = Sort(normalise_universe(db, sort.0));
                    if let Some(expr) = &def.contents.expr {
                        let expr = expr.clone();
                        check_no_local_or_metavariable(db, &expr).bind(|()| {
                            // Check that the type of the contents of the definition
                            // match the type declared in the definition.
                            let defeq = infer_type(db, expr.to_term(db)).and_then(|ty| {
                                Ok((
                                    ty,
                                    definitionally_equal(db, ty, def.contents.ty.to_term(db))?,
                                ))
                            });

                            match defeq {
                                Ok((_, true)) => Dr::ok(CertifiedDefinition::new(
                                    def.clone(),
                                    sort,
                                    ReducibilityHints::Regular {
                                        height: get_max_height(db, expr.to_term(db)) + 1,
                                    },
                                    origin,
                                )),
                                Ok((_ty, false)) => todo!(),
                                Err(e) => Dr::fail(
                                    Report::new(
                                        ReportKind::Error,
                                        Source::new(db, path.split_last(db).0, SourceType::Feather),
                                        def.provenance.span().start,
                                    )
                                    .with_message(format!(
                                        "while checking definition {}, kernel raised error: {}",
                                        def.name.text(db),
                                        e.display(db),
                                    )),
                                ),
                            }
                        })
                    } else {
                        Dr::ok(CertifiedDefinition::new(
                            def.clone(),
                            sort,
                            ReducibilityHints::Opaque,
                            origin,
                        ))
                    }
                }
                Err(_) => todo!(),
            }
        })
    })
}

/// Type checks the definition with the given name, or retrieves it from the database if it was already type checked.
/// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
/// This function will discard any diagnostic messages produced by type checking the definition.
pub fn get_certified_definition(db: &dyn Db, path: Path) -> Option<&CertifiedDefinition> {
    certify_definition(db, path).value().as_ref()
}
