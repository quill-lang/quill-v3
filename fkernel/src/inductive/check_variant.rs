use fcommon::{Dr, LabelType, ReportKind};
use fexpr::{
    basic::{DeBruijnIndex, DeBruijnOffset, Provenance},
    expr::{
        largest_unusable_metavariable, Expression, ExpressionT, LocalConstant,
        MetavariableGenerator, Term,
    },
    inductive::Variant,
};

use crate::{
    term::{
        destructure_as_nary_application, find_inst, instantiate, local_is_bound,
        nary_binder_to_pi_expression,
    },
    typeck::{
        as_sort, check_no_local_or_metavariable, definitionally_equal, infer_type,
        to_weak_head_normal_form,
    },
    universe::{is_zero, universe_at_most},
    Db,
};

use super::check_type::InductiveTypeInformation;

/// Verifies that a variant for an inductive type is valid and can be added to the environment.
/// We require that
/// - all variants start with the same global parameters,
/// - the type of all arguments live in universes at most the level of the corresponding data type,
/// - occurences of the inductive data type inside the introduction rule occur strictly positively,
/// - the introduction rule is type correct.
pub(in crate::inductive) fn check_variant<'db>(
    db: &'db dyn Db,
    info: &InductiveTypeInformation<'db>,
    variant: &Variant<Provenance, Box<Expression>>,
) -> Dr<()> {
    let intro_rule_ty =
        nary_binder_to_pi_expression(Provenance::Synthetic, variant.intro_rule.clone());
    check_no_local_or_metavariable(db, &intro_rule_ty).bind(|()| {
        // Ensure that the intro rule is type correct.
        match infer_type(db, intro_rule_ty.to_term(db)) {
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
                                let result = definitionally_equal(
                                    db,
                                    from_intro_rule.region.to_term(db),
                                    from_ty.region.to_term(db),
                                )
                                .and_then(|regions| {
                                    definitionally_equal(
                                        db,
                                        from_intro_rule.bound.ty.to_term(db),
                                        from_ty.bound.ty.to_term(db),
                                    )
                                    .map(|types| {
                                        regions
                                            && types
                                            && from_intro_rule.invocation_type
                                                == from_ty.invocation_type
                                    })
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
                                check_field(db, info, variant, i, &mut found_recursive_parameter)
                            }),
                    );

                    check_global_params.bind(|_| check_fields).deny().bind(|_| {
                        is_valid_inductive_application(
                            db,
                            info,
                            variant.intro_rule.result.to_term(db),
                            variant.intro_rule.structures.len(),
                        )
                        .bind(|result| {
                            if result {
                                Dr::ok(())
                            } else {
                                Dr::fail(todo!())
                            }
                        })
                    })
                }
            }
            Err(err) => {
                tracing::error!("{:?} checking {}", err, info.inductive.name.0.text(db));
                Dr::fail(
                    intro_rule_ty
                        .value
                        .provenance
                        .report(ReportKind::Error)
                        .with_message("this introduction rule was not type correct"),
                )
            }
        }
    })
}

fn check_field<'db>(
    db: &'db dyn Db,
    info: &InductiveTypeInformation<'db>,
    variant: &Variant<Provenance, Box<Expression>>,
    field_index: usize,
    found_recursive_parameter: &mut bool,
) -> Dr<()> {
    let mut term = variant.intro_rule.structures[field_index]
        .bound
        .ty
        .to_term(db);
    let mut meta_gen = MetavariableGenerator::new(largest_unusable_metavariable(db, term));
    for param in variant.intro_rule.structures.iter().take(field_index).rev() {
        term = instantiate(
            db,
            term,
            Term::new(
                db,
                ExpressionT::LocalConstant(
                    param
                        .without_provenance(db)
                        .generate_local_with_gen(&mut meta_gen),
                ),
            ),
        );
    }
    match infer_type(db, term).and_then(|sort| as_sort(db, sort)) {
        Ok(sort) => {
            // The type of the type of this field is allowed if
            // - its level is at most the level of the inductive data type being declared, or
            // - the inductive data type has sort 0.
            if !is_zero(&info.sort.0) && !universe_at_most(db, sort.0, info.sort.0.clone()) {
                todo!()
            } else {
                // Check that the inductive data type occurs strictly positively.
                check_positivity(db, info, variant, field_index).bind(|()| {
                    is_recursive_argument(db, info,term, field_index).bind(|is_recursive| {
                        if is_recursive {
                            *found_recursive_parameter = true;
                        }
                        if *found_recursive_parameter {
                            for (index, field) in variant.intro_rule.structures.iter().enumerate().skip(field_index) {
                                // This is an invalid occurrence of a recursive argument
                                // because later fields depend on it.
                                if local_is_bound(db, field.bound.ty.to_term(db), DeBruijnIndex::zero() + DeBruijnOffset::new((index - field_index) as u32)) {
                                        return Dr::fail(field.bound.ty.value.provenance.report(ReportKind::Error)
                                            .with_message("this is an invalid occurrence of a recursive argument, because a later field depends on it")
                                            .with_label(field.bound.ty.value.provenance.label(LabelType::Error)
                                                .with_message("this type referenced the field".to_string())),
                                    );
                                }
                            }
                            if local_is_bound(db, variant.intro_rule.result.to_term(db), DeBruijnIndex::zero() + DeBruijnOffset::new((variant.intro_rule.structures.len() - field_index) as u32)) {
                                Dr::fail(variant.intro_rule.result.value.provenance.report(ReportKind::Error)
                                    .with_message("this is an invalid occurrence of a recursive argument, because the inductive type itself depends on it")
                                    .with_label(variant.intro_rule.result.value.provenance.label(LabelType::Error)
                                        .with_message("this type referenced the field".to_string())),
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
fn check_positivity<'db>(
    db: &'db dyn Db,
    info: &InductiveTypeInformation<'db>,
    variant: &Variant<Provenance, Box<Expression>>,
    field_index: usize,
) -> Dr<()> {
    if find_inst(
        db,
        variant.intro_rule.structures[field_index]
            .bound
            .ty
            .to_term(db),
        &info.inst.name,
    )
    .is_some()
    {
        // This is a recursive argument, so we need to check for positivity.
        let mut t = variant.intro_rule.structures[field_index]
            .bound
            .ty
            .to_term(db);
        while let ExpressionT::Pi(pi) = t.value(db) {
            if let Some(value) = find_inst(db, pi.structure.bound.ty, &info.inst.name) {
                // This is a non-positive occurence of the inductive type being declared.
                return Dr::fail(todo!());
            } else {
                t = pi.result;
            }
        }

        is_valid_inductive_application(
            db,
            info,
            variant.intro_rule.structures[field_index]
                .bound
                .ty
                .to_term(db),
            field_index,
        )
        .bind(|result| {
            if result {
                // This is a valid recursive inductive application.
                Dr::ok(())
            } else {
                // This is an invalid inductive application.
                Dr::fail(todo!())
            }
        })
    } else {
        Dr::ok(())
    }
}

/// Returns true if the expression is a term of the form `(I As t)` where `I` is the inductive being
/// defined, `As` are the global parameters, and `I` does not occur in the indices `t`.
/// `field_index` is the field index, used for a de Bruijn offset.
fn is_valid_inductive_application<'db>(
    db: &'db dyn Db,
    info: &InductiveTypeInformation<'db>,
    t: Term,
    field_index: usize,
) -> Dr<bool> {
    let (function, arguments) = destructure_as_nary_application(db, t);
    match definitionally_equal(
        db,
        function,
        Term::new(db, ExpressionT::Inst(info.inst.clone())),
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
                    .all(|(index, field)| match field.value(db) {
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
                    .all(|arg| find_inst(db, *arg, &info.inst.name).is_none());
                globals_match && inductive_not_in_index
            }
        }),
        Err(_) => todo!(),
    }
}

/// Returns true if the expression is a recursive argument.
fn is_recursive_argument<'db>(
    db: &'db dyn Db,
    info: &InductiveTypeInformation<'db>,
    mut t: Term,
    field_index: usize,
) -> Dr<bool> {
    t = to_weak_head_normal_form(db, t);
    while let ExpressionT::Pi(pi) = t.value(db) {
        t = pi.result;
    }
    is_valid_inductive_application(db, info, t, field_index)
}
