use crate::{
    definition::Definition,
    expr::{Expression, ExpressionCache, Sort},
    message,
    result::Dr,
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

pub(crate) fn check_no_local_or_metavariable<'cache>(
    cache: &ExpressionCache<'cache>,
    e: Expression<'cache>,
) -> Dr<()> {
    // TODO: Check no metauniverses.
    if let Some(e) = e.first_local_or_hole(cache) {
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
/// Instead of calling this method directly, which takes a [`Definition`] as well as its [`Path`],
/// in most instances you should call [`Db::certify_definition`] or [`Db::get_certified_definition`].
/// These functions are able to parse and certify both feather and quill definitions.
pub fn certify_definition(
    db: &dyn Db,
    path: Path,
    def: &Definition,
    origin: DefinitionOrigin,
) -> Dr<CertifiedDefinition> {
    ExpressionCache::with_cache(db, None, None, None, |cache| {
        check_no_local_or_metavariable(cache, def.contents.ty.from_heap(cache)).bind(|()| {
            // Since we have no metavariables in the given expression,
            // we can initialise the metavariable generator with any value.
            // Check that the type of a definition is indeed a type.
            let def_ty = def.ty.from_heap(cache);
            let def_expr = def.expr.as_ref().map(|expr| expr.from_heap(cache));
            let sort = def_ty
                .infer_type(cache)
                .and_then(|sort| as_sort(cache, sort));

            // TODO: Check that all universes in the definition are quantified.
            match sort {
                Ok(sort) => {
                    let sort = Sort(sort.0.normalise_universe(db));
                    if let Some(def_expr) = def_expr {
                        check_no_local_or_metavariable(cache, def_expr).bind(|()| {
                            // Check that the type of the contents of the definition
                            // match the type declared in the definition.
                            let defeq = def_expr.infer_type(cache).and_then(|ty| {
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
                                        height: def_expr.get_max_height(cache) + 1,
                                    },
                                    origin,
                                )),
                                Ok((ty, false)) => Dr::fail(
                                    Report::new(
                                        ReportKind::Error,
                                        Source::new(db, path.split_last(db).0, SourceType::Feather),
                                        def.provenance.span().start,
                                    )
                                    .with_message(message![
                                        "body of definition ",
                                        def.name,
                                        " had type ",
                                        ty.to_heap(cache),
                                        " which does not match its definition"
                                    ]),
                                ),
                                Err(e) => Dr::fail(
                                    Report::new(
                                        ReportKind::Error,
                                        Source::new(db, path.split_last(db).0, SourceType::Feather),
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
}
