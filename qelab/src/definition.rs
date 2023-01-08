use fcommon::Source;
use fkernel::{
    definition::{Definition, DefinitionContents},
    expr::ExpressionCache,
    result::Dr,
};
use qdelab::delaborate;
use qformat::pexpression_to_document;
use qparse::def::PDefinition;

use crate::{
    elaborator::{Context, Elaborator},
    Db,
};

pub fn elaborate_definition(db: &dyn Db, source: Source, def: &PDefinition) -> Dr<Definition> {
    ExpressionCache::with_cache(db, None, None, None, |cache| {
        if let Some(ty) = &def.ty {
            tracing::debug!(
                "Type:\n    {}",
                pexpression_to_document(db, ty).pretty_print(15)
            );
            tracing::debug!(
                "Body:\n    {}",
                pexpression_to_document(db, &def.body).pretty_print(15)
            );
            let mut elab = Elaborator::new(cache, source);
            let result = elab.elaborate(ty, None, &Context::default()).bind(|ty| {
                elab.constrain_type_correct(ty).bind(|_| {
                    elab.elaborate(&def.body, Some(ty), &Context::default())
                        .bind(|body| {
                            elab.constrain_type_correct(body).bind(|_| {
                                elab.solve().map(|solution| {
                                    let ty = solution.substitute(cache, ty);
                                    let body = solution.substitute(cache, body);
                                    tracing::debug!(
                                        "Elaborated type:\n    {}",
                                        pexpression_to_document(
                                            db,
                                            &delaborate(cache, ty, &Default::default(), false)
                                        )
                                        .pretty_print(15)
                                    );
                                    tracing::debug!(
                                        "Elaborated body:\n    {}",
                                        pexpression_to_document(
                                            db,
                                            &delaborate(cache, body, &Default::default(), false)
                                        )
                                        .pretty_print(15)
                                    );
                                    (ty, body)
                                })
                            })
                        })
                })
            });

            result.map(|(ty, body)| {
                // We quantify over all universe variables found either in the type or body of the definition.
                let mut universe_params = ty
                    .universe_variables(cache)
                    .iter()
                    .map(|var| var.0)
                    .collect::<Vec<_>>();
                for value in body.universe_variables(cache) {
                    if universe_params
                        .iter()
                        .all(|univ| univ.0.contents != value.0 .0.contents)
                    {
                        universe_params.push(value.0);
                    }
                }

                Definition {
                    provenance: def.name.0.provenance,
                    contents: DefinitionContents {
                        name: def.name,
                        universe_params,
                        ty: ty.to_heap(cache),
                        expr: Some(body.to_heap(cache)),
                    },
                }
            })
        } else {
            todo!()
        }
    })
}
