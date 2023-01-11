use fcommon::{Source, Spanned};
use fkernel::{
    basic::{Name, QualifiedName, WithProvenance},
    definition::{Definition, DefinitionContents},
    expr::{
        BinderAnnotation, BinderStructure, BoundVariable, Expression, ExpressionCache, ExpressionT,
        FunctionOwnership, Inst, LocalConstant,
    },
    inductive::{Inductive, InductiveContents, Variant},
    multiplicity::ParameterOwnership,
    result::Dr,
    universe::{Universe, UniverseContents, UniverseVariable},
};
use qdelab::delaborate;
use qformat::pexpression_to_document;
use qparse::{def::PDefinition, inductive::PVariant};

use crate::{
    elaborator::{Context, Elaborator},
    Db,
};

pub fn elaborate_definition(db: &dyn Db, source: Source, def: &PDefinition) -> Dr<Definition> {
    ExpressionCache::with_cache(db, None, None, None, |cache| {
        let mut elab = Elaborator::new(cache, source);
        if let Some(ty) = &def.ty {
            tracing::debug!(
                "Type:\n    {}",
                pexpression_to_document(db, ty)
                    .pretty_print(15)
                    .replace('\n', "\n    ")
            );
            tracing::debug!(
                "Body:\n    {}",
                pexpression_to_document(db, &def.body)
                    .pretty_print(15)
                    .replace('\n', "\n    ")
            );
            let result = elab.elaborate(ty, None, &Context::default()).bind(|ty| {
                elab.constrain_type_correct(ty).bind(|_| {
                    elab.elaborate(&def.body, Some(ty), &Context::default())
                        .bind(|body| {
                            elab.constrain_type_correct(body).bind(|_| {
                                tracing::debug!(
                                    "Elaborated type:\n    {}",
                                    pexpression_to_document(
                                        db,
                                        &delaborate(cache, ty, &Default::default(), false)
                                    )
                                    .pretty_print(15)
                                    .replace('\n', "\n    ")
                                );
                                tracing::debug!(
                                    "Elaborated body:\n    {}",
                                    pexpression_to_document(
                                        db,
                                        &delaborate(cache, body, &Default::default(), false)
                                    )
                                    .pretty_print(15)
                                    .replace('\n', "\n    ")
                                );
                                elab.solve().map(|solution| {
                                    let ty = solution.substitute(cache, ty);
                                    let body = solution.substitute(cache, body);
                                    tracing::debug!(
                                        "Solved type:\n    {}",
                                        pexpression_to_document(
                                            db,
                                            &delaborate(cache, ty, &Default::default(), false)
                                        )
                                        .pretty_print(15)
                                        .replace('\n', "\n    ")
                                    );
                                    tracing::debug!(
                                        "Solved body:\n    {}",
                                        pexpression_to_document(
                                            db,
                                            &delaborate(cache, body, &Default::default(), false)
                                        )
                                        .pretty_print(15)
                                        .replace('\n', "\n    ")
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

pub fn elaborate_inductive(db: &dyn Db, source: Source, def: &PDefinition) -> Dr<Inductive> {
    ExpressionCache::with_cache(db, None, None, None, |cache| {
        let mut elab = Elaborator::new(cache, source);
        let (binders, inductive) = if let Some(result) = def.as_inductive() {
            result
        } else {
            todo!()
        };

        if let Some(ty) = &def.ty {
            tracing::debug!(
                "Inductive type:\n    {}",
                pexpression_to_document(elab.db(), ty)
                    .pretty_print(15)
                    .replace('\n', "\n    ")
            );
            elab.elaborate(ty, None, &Context::default()).bind(|ty| {
                elab.constrain_type_correct(ty).bind(|_| {
                    let inductive_params = ty.pi_args(cache);
                    assert!(binders.len() <= inductive_params.len());
                    let context = binders.iter().zip(&inductive_params).fold(
                        Context::default(),
                        |acc, (binder, constant)| {
                            let mut structure = constant.structure;
                            structure.bound.name = binder.name;
                            assert!(binder.ty.is_none());
                            acc.with(cache.gen_local(structure))
                        },
                    );

                    inductive
                        .variants
                        .iter()
                        .map(|variant| elaborate_variant(&mut elab, variant, context.clone()))
                        .collect::<Dr<Vec<_>>>()
                        .bind(|elaborated_variants| {
                            let provenance = elab.provenance(inductive.span());
                            // Quantify over all universe variables found in the inductive's type.
                            // TODO: Quantify over universes in the fields.
                            let cache = elab.cache();
                            let universe_params = ty
                                .universe_variables(cache)
                                .iter()
                                .map(|var| var.0)
                                .collect::<Vec<_>>();

                            // TODO: Apply the global parameters.
                            let inductive_ty = Expression::new(
                                cache,
                                provenance,
                                ExpressionT::Inst(Inst {
                                    name: QualifiedName(WithProvenance::new(
                                        provenance,
                                        source
                                            .path(cache.db())
                                            .with(cache.db(), def.name.0.contents)
                                            .segments(cache.db())
                                            .iter()
                                            .map(|str| Name(WithProvenance::new(provenance, *str)))
                                            .collect(),
                                    )),
                                    universes: universe_params
                                        .iter()
                                        .map(|param| {
                                            Universe::new(
                                                param.0.provenance,
                                                UniverseContents::UniverseVariable(
                                                    UniverseVariable(*param),
                                                ),
                                            )
                                        })
                                        .collect(),
                                }),
                            );

                            elab.solve().map(|solution| {
                                let mut variants = Vec::new();
                                for (name, fields, variant_ty) in elaborated_variants {
                                    let variant_ty = variant_ty.unwrap_or({
                                        // TODO: Check that we have no index parameters.
                                        inductive_ty
                                    });
                                    let intro_rule_pi = variant_ty.abstract_nary_pi(
                                        cache,
                                        fields.iter().rev().copied().map(|mut field| {
                                            field.structure.bound.ty = solution
                                                .substitute(cache, field.structure.bound.ty);
                                            (field.structure.bound.name.0.provenance, field)
                                        }),
                                    );
                                    tracing::debug!(
                                        "Intro rule {}:\n    {}",
                                        name.text(cache.db()),
                                        pexpression_to_document(
                                            cache.db(),
                                            &delaborate(
                                                cache,
                                                intro_rule_pi,
                                                &Default::default(),
                                                false
                                            )
                                        )
                                        .pretty_print(15)
                                        .replace('\n', "\n    ")
                                    );
                                    let intro_rule =
                                        intro_rule_pi.pi_to_nary_binder(cache).to_heap(cache);
                                    variants.push(Variant { name, intro_rule });
                                }

                                Inductive::new(
                                    provenance,
                                    InductiveContents {
                                        name: def.name,
                                        universe_params,
                                        ty: ty.pi_to_nary_binder(cache).to_heap(cache),
                                        global_params: 0,
                                        variants,
                                    },
                                )
                            })
                        })
                })
            })
        } else {
            todo!()
        }
    })
}

/// Elaborates a variant of an inductive.
/// Returns the list of fields, given as local constants parametrising the next fields,
/// as well as the type of the variant, which may also contain the local constants of the fields.
fn elaborate_variant<'cache>(
    elab: &mut Elaborator<'_, 'cache>,
    variant: &PVariant,
    mut context: Context<'cache>,
) -> Dr<(
    Name,
    Vec<LocalConstant<Expression<'cache>>>,
    Option<Expression<'cache>>,
)> {
    let mut fields = Vec::new();
    for field in &variant.fields {
        let constant = elab
            .elaborate(&field.ty, None, &context)
            .bind(|ty| elab.constrain_type_correct(ty))
            .map(|ty| {
                elab.cache().gen_local(BinderStructure {
                    bound: BoundVariable {
                        name: field.name,
                        ty,
                        ownership: ParameterOwnership::POwned,
                    },
                    binder_annotation: BinderAnnotation::Explicit,
                    function_ownership: FunctionOwnership::Once,
                    region: Expression::static_region(elab.cache()),
                })
            });
        if let Some(constant) = constant.value() {
            context = context.with(*constant);
        }
        fields.push(constant);
    }
    Dr::sequence(fields).bind(|fields| {
        if let Some(ty) = &variant.ty {
            elab.elaborate(ty, None, &context)
                .bind(|ty| elab.constrain_type_correct(ty))
                .map(|ty| (variant.name, fields, Some(ty)))
        } else {
            Dr::ok((variant.name, fields, None))
        }
    })
}
