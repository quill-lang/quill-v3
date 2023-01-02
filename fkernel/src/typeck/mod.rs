use crate::{
    definition::Definition,
    expr::{Expression, ExpressionCache, Sort},
    message,
    module::{module_from_feather_source, Item},
    result::{Dr, Message},
    Db,
};
use fcommon::{LabelType, Path, Report, ReportKind, Source, SourceType, Spanned};

mod defeq;
mod definition;
mod infer;
mod unfold;
mod whnf;

pub use defeq::*;
pub use definition::*;
pub use infer::*;
pub use unfold::*;
pub use whnf::*;

/// Retrieves the definition with the given name.
/// This definition will not have been type checked.
#[salsa::tracked(return_ref)]
pub fn get_definition(db: &dyn Db, path: Path) -> Dr<Definition> {
    let (source, name) = path.split_last(db);
    module_from_feather_source(db, Source::new(db, source, SourceType::Feather))
        .as_ref()
        .map_messages(Message::new)
        .map(|module| {
            module.items.iter().find_map(|item| match item {
                Item::Definition(def) => {
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
                .with_message(message!["definition ", name, " could not be found"]),
            ),
        })
}

pub(crate) fn check_no_local_or_metavariable<'cache>(
    cache: &ExpressionCache<'cache>,
    e: Expression<'cache>,
) -> Dr<()> {
    if e.first_local_or_metavariable(cache).is_some() {
        Dr::fail(e.provenance(cache).report(ReportKind::Error).with_label(
            e.provenance(cache).label(LabelType::Error).with_message(
                "could not certify definition as it contained an invalid expression".into(),
            ),
        ))
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

        ExpressionCache::with_cache(db, |cache| {
            check_no_local_or_metavariable(cache, def.contents.ty.from_heap(cache)).bind(|()| {
                // Since we have no metavariables in the given expression,
                // we can initialise the metavariable generator with any value.
                // Check that the type of a definition is indeed a type.
                let sort = def
                    .contents
                    .ty
                    .from_heap(cache)
                    .infer_type(cache)
                    .and_then(|sort| as_sort(cache, sort));

                match sort {
                    Ok(sort) => {
                        let sort = Sort(sort.0.normalise_universe(db));
                        if let Some(expr) = &def.contents.expr {
                            let expr = expr.clone();
                            check_no_local_or_metavariable(cache, expr.from_heap(cache)).bind(
                                |()| {
                                    // Check that the type of the contents of the definition
                                    // match the type declared in the definition.
                                    let defeq =
                                        expr.from_heap(cache).infer_type(cache).and_then(|ty| {
                                            Ok((
                                                ty,
                                                Expression::definitionally_equal(
                                                    cache,
                                                    ty,
                                                    def.contents.ty.from_heap(cache),
                                                )?,
                                            ))
                                        });

                                    match defeq {
                                        Ok((_, true)) => Dr::ok(CertifiedDefinition::new(
                                            def.clone(),
                                            sort,
                                            ReducibilityHints::Regular {
                                                height: expr
                                                    .from_heap(cache)
                                                    .get_max_height(cache)
                                                    + 1,
                                            },
                                            origin,
                                        )),
                                        Ok((_ty, false)) => Dr::fail(
                                            Report::new(
                                                ReportKind::Error,
                                                Source::new(
                                                    db,
                                                    path.split_last(db).0,
                                                    SourceType::Feather,
                                                ),
                                                def.provenance.span().start,
                                            )
                                            .with_message(message![
                                                "body of definition ",
                                                def.name,
                                                " had incorrect type"
                                            ]),
                                        ),
                                        Err(e) => Dr::fail(
                                            Report::new(
                                                ReportKind::Error,
                                                Source::new(
                                                    db,
                                                    path.split_last(db).0,
                                                    SourceType::Feather,
                                                ),
                                                def.provenance.span().start,
                                            )
                                            .with_message(message![
                                                "while checking definition ",
                                                def.name,
                                                ", kernel raised error: ",
                                                e
                                            ]),
                                        ),
                                    }
                                },
                            )
                        } else {
                            Dr::ok(CertifiedDefinition::new(
                                def.clone(),
                                sort,
                                ReducibilityHints::Opaque,
                                origin,
                            ))
                        }
                    }
                    Err(_) => Dr::fail(
                        Report::new(
                            ReportKind::Error,
                            Source::new(db, path.split_last(db).0, SourceType::Feather),
                            def.provenance.span().start,
                        )
                        .with_message(message![
                            "type of definition ",
                            def.name,
                            " was not a type"
                        ]),
                    ),
                }
            })
        })
    })
}

/// Type checks the definition with the given name, or retrieves it from the database if it was already type checked.
/// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
/// This function will discard any diagnostic messages produced by type checking the definition.
pub fn get_certified_definition(db: &dyn Db, path: Path) -> Option<&CertifiedDefinition> {
    certify_definition(db, path).value().as_ref()
}
