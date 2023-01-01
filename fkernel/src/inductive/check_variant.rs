use crate::{
    basic::{DeBruijnIndex, DeBruijnOffset, Provenance},
    expr::{Expression, ExpressionCache, ExpressionT, MetavariableGenerator},
    inductive::Variant,
    result::Dr,
    typeck::{as_sort, check_no_local_or_metavariable},
    universe::Universe,
};
use fcommon::{LabelType, ReportKind};

use super::check_type::InductiveTypeInformation;

/// Verifies that a variant for an inductive type is valid and can be added to the environment.
/// We require that
/// - all variants start with the same global parameters,
/// - the type of all arguments live in universes at most the level of the corresponding data type,
/// - occurences of the inductive data type inside the introduction rule occur strictly positively,
/// - the introduction rule is type correct.
pub(in crate::inductive) fn check_variant<'cache>(
    cache: &mut ExpressionCache<'cache>,
    info: &InductiveTypeInformation<'cache>,
    variant: &Variant,
) -> Dr<()> {
    let intro_rule_ty = Expression::nary_binder_to_pi(
        cache,
        Provenance::Synthetic,
        variant.intro_rule.from_heap(cache),
    );
    check_no_local_or_metavariable(cache, intro_rule_ty).bind(|()| {
        // Ensure that the intro rule is type correct.
        match intro_rule_ty.infer_type(cache) {
            Ok(_) => {
                // The intro rule is type correct.
                // Check that there are enough global parameters.
                if (variant.intro_rule.structures.len() as u32) < info.inductive.global_params {
                    todo!()
                } else {
                    // Check that the first parameters are the global parameters.
                    let check_global_params = Dr::sequence_unfail(
                        variant
                            .intro_rule
                            .structures
                            .iter()
                            .take(info.inductive.global_params as usize)
                            .zip(&info.inductive.ty.structures)
                            .map(|(from_intro_rule, from_ty)| {
                                let result = Expression::definitionally_equal(
                                    cache,
                                    from_intro_rule.region.from_heap(cache),
                                    from_ty.region.from_heap(cache),
                                )
                                .and_then(|regions| {
                                    Expression::definitionally_equal(
                                        cache,
                                        from_intro_rule.bound.ty.from_heap(cache),
                                        from_ty.bound.ty.from_heap(cache),
                                    )
                                    .map(|types| regions && types)
                                });
                                match result {
                                    Ok(_) => Dr::ok(()),
                                    Err(_) => todo!(),
                                }
                            }),
                    );

                    // Check that the other parameters are valid fields.
                    let mut found_recursive_parameter = false;
                    let check_fields = Dr::sequence_unfail(
                        variant
                            .intro_rule
                            .structures
                            .iter()
                            .enumerate()
                            .skip(info.inductive.global_params as usize)
                            .map(|(i, _)| {
                                check_field(cache, info, variant, i, &mut found_recursive_parameter)
                            }),
                    );

                    check_global_params.bind(|_| check_fields).deny().bind(|_| {
                        is_valid_inductive_application(
                            cache,
                            info,
                            variant.intro_rule.result.from_heap(cache),
                            variant.intro_rule.structures.len(),
                        )
                        .bind(
                            |result| {
                                if result {
                                    Dr::ok(())
                                } else {
                                    todo!()
                                }
                            },
                        )
                    })
                }
            }
            Err(err) => {
                tracing::error!(
                    "{:?} checking {}",
                    err,
                    info.inductive.name.0.text(cache.db())
                );
                Dr::fail(
                    intro_rule_ty
                        .provenance(cache)
                        .report(ReportKind::Error)
                        .with_message("this introduction rule was not type correct".into()),
                )
            }
        }
    })
}

fn check_field<'cache>(
    cache: &mut ExpressionCache<'cache>,
    info: &InductiveTypeInformation<'cache>,
    variant: &Variant,
    field_index: usize,
    found_recursive_parameter: &mut bool,
) -> Dr<()> {
    let mut expr = variant.intro_rule.structures[field_index]
        .bound
        .ty
        .from_heap(cache);
    let mut meta_gen = MetavariableGenerator::new(expr.largest_unusable_metavariable(cache));
    for param in variant.intro_rule.structures.iter().take(field_index).rev() {
        expr = expr.instantiate(
            cache,
            Expression::new(
                cache,
                Provenance::Synthetic,
                ExpressionT::LocalConstant(
                    param
                        .from_heap(cache)
                        .generate_local_with_gen(&mut meta_gen),
                ),
            ),
        );
    }
    match expr.infer_type(cache).and_then(|sort| as_sort(cache, sort)) {
        Ok(sort) => {
            // The type of the type of this field is allowed if
            // - its level is at most the level of the inductive data type being declared, or
            // - the inductive data type has sort 0.
            if !info.sort.0.is_zero()
                && !Universe::universe_at_most(cache.db(), sort.0, info.sort.0.clone())
            {
                todo!()
            } else {
                // Check that the inductive data type occurs strictly positively.
                check_positivity(cache, info, variant, field_index).bind(|()| {
                    is_recursive_argument(cache, info,expr, field_index).bind(|is_recursive| {
                        if is_recursive {
                            *found_recursive_parameter = true;
                        }
                        if *found_recursive_parameter {
                            for (index, field) in variant.intro_rule.structures.iter().enumerate().skip(field_index) {
                                // This is an invalid occurrence of a recursive argument
                                // because later fields depend on it.
                                if field.bound.ty.from_heap(cache).local_is_bound(cache, DeBruijnIndex::zero() + DeBruijnOffset::new((index - field_index) as u32)) {
                                        return Dr::fail(field.bound.ty.value.provenance.report(ReportKind::Error)
                                            .with_message("this is an invalid occurrence of a recursive argument, because a later field depends on it".into())
                                            .with_label(field.bound.ty.value.provenance.label(LabelType::Error)
                                                .with_message("this type referenced the field".into())),
                                    );
                                }
                            }
                            if variant.intro_rule.result.from_heap(cache).local_is_bound(cache, DeBruijnIndex::zero() + DeBruijnOffset::new((variant.intro_rule.structures.len() - field_index) as u32)) {
                                Dr::fail(variant.intro_rule.result.value.provenance.report(ReportKind::Error)
                                    .with_message("this is an invalid occurrence of a recursive argument, because the inductive type itself depends on it".into())
                                    .with_label(variant.intro_rule.result.value.provenance.label(LabelType::Error)
                                        .with_message("this type referenced the field".into())),
                                )
                            } else {
                                Dr::ok(())
                            }
                        } else {
                            Dr::ok(())
                        }
                    })
                })
            }
        }
        Err(_) => todo!(),
    }
}

/// Check that the inductive data type being declared occurs strictly positively in the given expression.
/// This means that the field's type must be `a -> b -> ... -> t` where the inductive cannot appear in `a`, `b` and so on,
/// and `t` may either not reference the inductive, or is exactly `(I As t)`.
fn check_positivity<'cache>(
    cache: &mut ExpressionCache<'cache>,
    info: &InductiveTypeInformation<'cache>,
    variant: &Variant,
    field_index: usize,
) -> Dr<()> {
    if variant.intro_rule.structures[field_index]
        .bound
        .ty
        .from_heap(cache)
        .find_inst(cache, &info.inst.name)
        .is_some()
    {
        // This is a recursive argument, so we need to check for positivity.
        let mut t = variant.intro_rule.structures[field_index]
            .bound
            .ty
            .from_heap(cache);
        while let ExpressionT::Pi(pi) = t.value(cache) {
            if pi
                .structure
                .bound
                .ty
                .find_inst(cache, &info.inst.name)
                .is_some()
            {
                // This is a non-positive occurence of the inductive type being declared.
                todo!()
            } else {
                t = pi.result;
            }
        }

        is_valid_inductive_application(
            cache,
            info,
            variant.intro_rule.structures[field_index]
                .bound
                .ty
                .from_heap(cache),
            field_index,
        )
        .bind(|result| {
            if result {
                // This is a valid recursive inductive application.
                Dr::ok(())
            } else {
                // This is an invalid inductive application.
                todo!()
            }
        })
    } else {
        Dr::ok(())
    }
}

/// Returns true if the expression is a term of the form `(I As t)` where `I` is the inductive being
/// defined, `As` are the global parameters, and `I` does not occur in the indices `t`.
/// `field_index` is the field index, used for a de Bruijn offset.
fn is_valid_inductive_application<'cache>(
    cache: &mut ExpressionCache<'cache>,
    info: &InductiveTypeInformation<'cache>,
    expr: Expression<'cache>,
    field_index: usize,
) -> Dr<bool> {
    let (function, arguments) = expr.destructure_as_nary_application(cache);
    match Expression::definitionally_equal(
        cache,
        function,
        Expression::new(
            cache,
            Provenance::Synthetic,
            ExpressionT::Inst(info.inst.clone()),
        ),
    ) {
        Ok(defeq) => Dr::ok({
            if !defeq || arguments.len() != info.inductive.ty.structures.len() {
                // The application was not of the form `(I ...)`, or the application was of the form `(I ...)`, but an incorrect number of parameters to the inductive were supplied.
                false
            } else {
                // Check that the global parameters are exactly the first parameters passed to the inductive.
                let globals_match = arguments
                    .iter()
                    .take(info.inductive.global_params as usize)
                    .enumerate()
                    .all(|(index, field)| match field.value(cache) {
                        ExpressionT::Local(local) => {
                            local.index + DeBruijnOffset::zero().succ()
                                == DeBruijnIndex::zero()
                                    + DeBruijnOffset::new((field_index - index) as u32)
                        }
                        _ => false,
                    });
                // Check that the inductive does not appear in the index parameters.
                let inductive_not_in_index = arguments
                    .iter()
                    .skip(info.inductive.global_params as usize)
                    .all(|arg| arg.find_inst(cache, &info.inst.name).is_none());
                globals_match && inductive_not_in_index
            }
        }),
        Err(_) => todo!(),
    }
}

/// Returns true if the expression is a recursive argument.
fn is_recursive_argument<'cache>(
    cache: &mut ExpressionCache<'cache>,
    info: &InductiveTypeInformation<'cache>,
    mut expr: Expression<'cache>,
    field_index: usize,
) -> Dr<bool> {
    expr = expr.to_weak_head_normal_form(cache);
    while let ExpressionT::Pi(pi) = expr.value(cache) {
        expr = pi.result;
    }
    is_valid_inductive_application(cache, info, expr, field_index)
}
