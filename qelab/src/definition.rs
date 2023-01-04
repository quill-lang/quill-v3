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
    ExpressionCache::with_cache(db, None, None, |cache| {
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
                elab.elaborate(&def.body, Some(ty), &Context::default())
                    .bind(|body| {
                        elab.solve().map(|solution| {
                            let ty = solution.substitute(cache, ty);
                            let body = solution.substitute(cache, body);
                            tracing::debug!(
                                "Elaborated type:\n    {}",
                                pexpression_to_document(
                                    db,
                                    &delaborate(cache, ty, &Default::default())
                                )
                                .pretty_print(15)
                            );
                            tracing::debug!(
                                "Elaborated body:\n    {}",
                                pexpression_to_document(
                                    db,
                                    &delaborate(cache, body, &Default::default())
                                )
                                .pretty_print(15)
                            );
                            (ty, body)
                        })
                    })
            });

            result.map(|(ty, body)| Definition {
                provenance: def.name.0.provenance,
                contents: DefinitionContents {
                    name: def.name,
                    universe_params: Vec::new(),
                    ty: ty.to_heap(cache),
                    expr: Some(body.to_heap(cache)),
                },
            })
        } else {
            todo!()
        }
    })
}