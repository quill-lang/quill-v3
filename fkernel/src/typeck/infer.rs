//! Infers types of terms.

use fcommon::{Path, Str};
use fexpr::{
    basic::{DeBruijnIndex, Name, Provenance, WithProvenance},
    expr::*,
    multiplicity::{InvocationType, ParameterOwnership},
    universe::*,
};

use crate::{
    inductive::get_inductive,
    term::{
        abstract_binder, create_nary_application, destructure_as_nary_application,
        has_free_variables, instantiate, instantiate_universe_parameters, nary_binder_to_lambda,
        nary_binder_to_pi_expression,
    },
};

use super::{defeq::definitionally_equal, get_definition, whnf::to_weak_head_normal_form, Db};

/// An error emitted by the kernel when performing type inference or definitional equality checking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InferenceError {
    TermNotClosed(Term),
    IncorrectUniverseArity,
    DefinitionNotFound(Path),
    LetTypeMismatch,
    ApplyTypeMismatch {
        function: Term,
        function_type: Term,
        argument: Term,
        argument_type: Term,
    },
    ExpectedSort,
    ExpectedPi,
    UnexpectedMetauniverse,
    IncorrectIntroParameters,
}

impl InferenceError {
    pub fn display(&self, db: &dyn Db) -> String {
        match self {
            InferenceError::TermNotClosed(term) => {
                format!("term\n{}\nhad free variables", term.display(db))
            }
            InferenceError::IncorrectUniverseArity => todo!(),
            InferenceError::DefinitionNotFound(path) => {
                format!("definition {} not found", path.to_string(db))
            }
            InferenceError::LetTypeMismatch => todo!(),
            InferenceError::ApplyTypeMismatch {
                function,
                function_type,
                argument,
                argument_type,
            } => format!(
                "cannot apply function\n{}\nof type\n{}\nto term\n{}\nof type\n{}",
                function.display(db),
                function_type.display(db),
                argument.display(db),
                argument_type.display(db),
            ),
            InferenceError::ExpectedSort => todo!(),
            InferenceError::ExpectedPi => todo!(),
            InferenceError::UnexpectedMetauniverse => todo!(),
            InferenceError::IncorrectIntroParameters => todo!(),
        }
    }
}

/// Short for "inference result".
/// See also [`fcommon::Dr`].
///
/// Instead of emitting textual errors, the kernel emits *inference results* which either succeed
/// or error with a particular error message.
pub type Ir<T> = Result<T, InferenceError>;

/// Infers the type of a (closed) term.
/// If we return [`Ok`], the provided term is type-correct and has the given type.
#[salsa::tracked]
pub fn infer_type(db: &dyn Db, t: Term) -> Ir<Term> {
    if has_free_variables(db, t) {
        Err(InferenceError::TermNotClosed(t))
    } else {
        infer_type_core(db, t)
    }
}

/// Infers the type of a closed term.
/// This function assumes that `t` is indeed a closed term and panics if it finds a free variable;
/// use [`infer_type`] if this is unknown.
pub(crate) fn infer_type_core(db: &dyn Db, t: Term) -> Ir<Term> {
    match t.value(db) {
        ExpressionT::Local(_) => {
            unreachable!("term should not have free variables, but a bound variable was found")
        }
        ExpressionT::Borrow(borrow) => infer_type_borrow(db, borrow),
        ExpressionT::Delta(delta) => infer_type_delta(db, delta),
        ExpressionT::Inst(inst) => infer_type_inst(db, inst),
        ExpressionT::Let(inner) => infer_type_let(db, inner),
        ExpressionT::Lambda(lambda) => infer_type_lambda(db, lambda),
        ExpressionT::Pi(pi) => infer_type_pi(db, pi),
        ExpressionT::RegionLambda(_) => todo!(),
        ExpressionT::RegionPi(_) => todo!(),
        ExpressionT::Apply(apply) => infer_type_apply(db, apply),
        ExpressionT::Intro(intro) => infer_type_intro(db, intro),
        ExpressionT::Match(match_expr) => infer_type_match(db, match_expr),
        ExpressionT::Fix(fix) => infer_type_fix(db, fix),
        ExpressionT::Sort(sort) => infer_type_sort(db, sort),
        ExpressionT::Region | ExpressionT::RegionT => Ok(Term::new(db, ExpressionT::RegionT)),
        ExpressionT::StaticRegion => Ok(Term::new(db, ExpressionT::Region)),
        ExpressionT::Lifespan(_) => todo!(),
        ExpressionT::Metavariable(var) => Ok(var.ty),
        ExpressionT::LocalConstant(local) => Ok(local.metavariable.ty),
    }
}

fn infer_type_borrow(db: &dyn Db, borrow: &Borrow<Term>) -> Ir<Term> {
    infer_type_core(db, borrow.value).map(|ty| {
        Term::new(
            db,
            ExpressionT::Delta(Delta {
                region: borrow.region,
                ty,
            }),
        )
    })
}

fn infer_type_delta(db: &dyn Db, delta: &Delta<Term>) -> Ir<Term> {
    let ty_type = infer_type_core(db, delta.ty)?;
    Ok(Term::new(db, ExpressionT::Sort(as_sort(db, ty_type)?)))
}

fn infer_type_inst(db: &dyn Db, inst: &Inst<()>) -> Ir<Term> {
    let path = inst.name.to_path(db);
    match get_definition(db, path).value() {
        Some(def) => {
            if def.contents.universe_params.len() == inst.universes.len() {
                for u in &inst.universes {
                    check_valid_universe(u)?;
                }
                if def.contents.universe_params.len() != inst.universes.len() {
                    todo!()
                }
                Ok(instantiate_universe_parameters(
                    db,
                    def.contents.ty.to_term(db),
                    &def.contents.universe_params,
                    &inst.universes,
                ))
            } else {
                Err(InferenceError::IncorrectUniverseArity)
            }
        }
        None => match get_inductive(db, path).value() {
            Some(ind) => {
                if ind.contents.universe_params.len() == inst.universes.len() {
                    for u in &inst.universes {
                        check_valid_universe(u)?;
                    }
                    if ind.contents.universe_params.len() != inst.universes.len() {
                        todo!()
                    }
                    Ok(instantiate_universe_parameters(
                        db,
                        nary_binder_to_pi_expression(
                            Provenance::Synthetic,
                            ind.contents.ty.clone(),
                        )
                        .to_term(db),
                        &ind.contents.universe_params,
                        &inst.universes,
                    ))
                } else {
                    Err(InferenceError::IncorrectUniverseArity)
                }
            }
            None => Err(InferenceError::DefinitionNotFound(path)),
        },
    }
}

fn infer_type_let(db: &dyn Db, inner: &Let<(), Term>) -> Ir<Term> {
    // The type of the value to assign must be a type.
    // That is, its type must be a sort.
    let let_type_type = infer_type_core(db, inner.bound.ty)?;
    as_sort(db, let_type_type)?;

    // Infer the type of the value to substitute.
    let let_value_type = infer_type_core(db, inner.to_assign)?;

    // The value that we assign must have type definitionally equal to the type to assign.
    if !definitionally_equal(db, let_value_type, inner.bound.ty)? {
        return Err(InferenceError::LetTypeMismatch);
    }

    // We perform a step of zeta-reduction and then infer the type of the body of the expression.
    infer_type_core(db, instantiate(db, inner.body, inner.to_assign))
}

fn infer_type_lambda(db: &dyn Db, lambda: &Binder<(), Term>) -> Ir<Term> {
    // The argument type must be a type.
    let argument_type_type = infer_type_core(db, lambda.structure.bound.ty)?;
    as_sort(db, argument_type_type)?;

    // Infer the return type of the lambda by first instantiating the parameter then inferring the resulting type.
    let new_local = lambda.structure.generate_local(db, lambda.result);
    let body = instantiate(
        db,
        lambda.result,
        Term::new(db, ExpressionT::LocalConstant(new_local)),
    );
    let return_type = infer_type_core(db, body)?;
    Ok(Term::new(
        db,
        ExpressionT::Pi(abstract_binder(db, new_local, return_type)),
    ))
}

fn infer_type_pi(db: &dyn Db, pi: &Binder<(), Term>) -> Ir<Term> {
    // The argument type must be a type.
    let parameter_type = infer_type_core(db, pi.structure.bound.ty)?;
    let domain_type = as_sort(db, parameter_type)?;

    // Infer the return type of the pi by first instantiating the parameter then inferring the resulting type.
    let body = instantiate(
        db,
        pi.result,
        Term::new(
            db,
            ExpressionT::LocalConstant(pi.structure.generate_local(db, pi.result)),
        ),
    );
    let return_type = as_sort(db, infer_type_core(db, body)?)?;
    Ok(Term::new(
        db,
        ExpressionT::Sort(Sort(Universe::new(
            UniverseContents::UniverseImpredicativeMax(UniverseImpredicativeMax {
                left: Box::new(domain_type.0),
                right: Box::new(return_type.0),
            }),
        ))),
    ))
}

fn infer_type_apply(db: &dyn Db, apply: &Apply<Term>) -> Ir<Term> {
    let function_type = infer_type_core(db, apply.function)?;
    let function_type_binder = as_pi(db, function_type)?;
    let argument_type = infer_type_core(db, apply.argument)?;

    if !definitionally_equal(db, argument_type, function_type_binder.structure.bound.ty)? {
        return Err(InferenceError::ApplyTypeMismatch {
            function: apply.function,
            function_type,
            argument: apply.argument,
            argument_type,
        });
    }

    Ok(instantiate(db, function_type_binder.result, apply.argument))
}

fn infer_type_intro(db: &dyn Db, intro: &Intro<(), Term>) -> Ir<Term> {
    match get_inductive(db, intro.inductive.to_path(db)).value() {
        Some(inductive) => {
            match inductive
                .variants
                .iter()
                .find(|variant| *variant.name == *intro.variant)
            {
                Some(variant) => {
                    if intro.parameters.len() != variant.intro_rule.structures.len() {
                        tracing::error!(
                            "{} != {}",
                            intro.parameters.len(),
                            variant.intro_rule.structures.len()
                        );
                        return Err(InferenceError::IncorrectIntroParameters);
                    }

                    // Check that all of the parameters are of the correct type.
                    for (index, param) in intro.parameters.iter().enumerate() {
                        let param_instantiated = intro
                            .parameters
                            .iter()
                            .take(index)
                            .rev()
                            .fold(*param, |t, param| instantiate(db, t, *param));

                        let expected_type = intro.parameters.iter().take(index).rev().fold(
                            instantiate_universe_parameters(
                                db,
                                variant.intro_rule.structures[index].bound.ty.to_term(db),
                                &inductive.universe_params,
                                &intro.universes,
                            ),
                            |t, param| instantiate(db, t, *param),
                        );

                        if !definitionally_equal(
                            db,
                            infer_type(db, param_instantiated)?,
                            expected_type,
                        )? {
                            todo!();
                        }
                    }

                    Ok(intro.parameters.iter().rev().fold(
                        instantiate_universe_parameters(
                            db,
                            variant.intro_rule.result.to_term(db),
                            &inductive.universe_params,
                            &intro.universes,
                        ),
                        |t, param| instantiate(db, t, *param),
                    ))
                }
                None => todo!(),
            }
        }
        None => todo!(),
    }
}

fn infer_type_match(db: &dyn Db, match_expr: &Match<(), Term>) -> Ir<Term> {
    let major_premise_type = infer_type(db, match_expr.major_premise)?;
    let (inductive_term, parameters) = destructure_as_nary_application(db, major_premise_type);
    // TODO: Check if we need to `lift_free_vars` on the global parameters below.
    match inductive_term.value(db) {
        ExpressionT::Inst(inst) => {
            match get_inductive(db, inst.name.to_path(db)).value() {
                Some(inductive) => {
                    // The major premise is indeed of an inductive type, and the inductive type exists.
                    // Check that `index_params` is correct.
                    if match_expr.index_params
                        != (inductive.ty.structures.len() as u32) - inductive.global_params
                    {
                        // The number of `index_params` stated in the match expression was wrong.
                        todo!()
                    }

                    // Check the type of the motive.
                    // This is accomplished by turning the motive into a lambda abstraction
                    // where the parameters are the inductive's index parameters and then the major premise,
                    // then checking the type of the resulting lambda.
                    let mut binders = inductive.ty.without_provenance(db);
                    binders.structures = binders
                        .structures
                        .into_iter()
                        .skip(inductive.global_params as usize)
                        .chain(std::iter::once(BinderStructure {
                            // The structure here isn't really relevant.
                            bound: BoundVariable {
                                name: Name(WithProvenance::new(Str::new(
                                    db,
                                    "_major_premise".to_owned(),
                                ))),
                                ty: create_nary_application(
                                    db,
                                    inductive_term,
                                    inductive.ty.structures.iter().enumerate().rev().map(
                                        |(index, _)| {
                                            Term::new(
                                                db,
                                                ExpressionT::Local(Local {
                                                    index: DeBruijnIndex::new(index as u32),
                                                }),
                                            )
                                        },
                                    ),
                                ),
                                ownership: ParameterOwnership::POwned,
                            },
                            binder_annotation: BinderAnnotation::Explicit,
                            invocation_type: InvocationType::Once,
                            region: Term::new(db, ExpressionT::StaticRegion),
                        }))
                        .collect();
                    binders.result = match_expr.motive;
                    let motive_lambda = parameters
                        .iter()
                        .take(inductive.global_params as usize)
                        .rev()
                        .fold(nary_binder_to_lambda(db, binders), |ty, term| {
                            instantiate(db, ty, *term)
                        });
                    infer_type(db, motive_lambda)?;
                    // The motive is type correct.

                    // Check each minor premise.
                    // First, check that there is exactly one minor premise for each variant.
                    for variant in &inductive.variants {
                        let matching_minor_premises = match_expr
                            .minor_premises
                            .iter()
                            .filter(|premise| *premise.variant == *variant.name)
                            .collect::<Vec<_>>();
                        if matching_minor_premises.len() != 1 {
                            todo!()
                        }
                    }

                    // Check that each minor premise is type correct.
                    for premise in &match_expr.minor_premises {
                        // Get the variant of the inductive that this minor premise matches.
                        let variant = if let Some(variant) = inductive
                            .variants
                            .iter()
                            .find(|variant| *premise.variant == *variant.name)
                        {
                            variant
                        } else {
                            todo!()
                        };

                        // Check that `premise.fields` is correct.
                        if premise.fields
                            != (variant.intro_rule.structures.len() as u32)
                                - inductive.global_params
                        {
                            // The number of fields stated in the match expression was wrong.
                            todo!()
                        }

                        let mut binders = variant.intro_rule.without_provenance(db);
                        binders.structures = binders
                            .structures
                            .into_iter()
                            .skip(inductive.global_params as usize)
                            .collect();
                        binders.result = premise.result;
                        let premise_lambda = parameters
                            .iter()
                            .take(inductive.global_params as usize)
                            .rev()
                            .fold(nary_binder_to_lambda(db, binders), |ty, term| {
                                instantiate(db, ty, *term)
                            });
                        let mut minor_premise_type = infer_type(db, premise_lambda)?;

                        // Check that the minor premise type matches the motive.
                        // Strip off the fields from the type of the minor premise.
                        let mut fields = Vec::new();
                        let mut meta_gen =
                            MetavariableGenerator::new(largest_unusable_metavariable(
                                db,
                                Term::new(db, ExpressionT::Match(match_expr.clone())),
                            ));
                        for _ in 0..premise.fields {
                            match minor_premise_type.value(db) {
                                ExpressionT::Pi(pi) => {
                                    let field = pi.structure.generate_local_with_gen(&mut meta_gen);
                                    minor_premise_type = instantiate(
                                        db,
                                        pi.result,
                                        Term::new(db, ExpressionT::LocalConstant(field)),
                                    );
                                    fields.push(field);
                                }
                                _ => unreachable!(),
                            }
                        }
                        // Instantiate the motive with the index parameters and the inductive.
                        let specialised_major_premise = Term::new(
                            db,
                            ExpressionT::Intro(Intro {
                                inductive: inst.name.clone(),
                                universes: inst.universes.clone(),
                                variant: variant.name.without_provenance(),
                                parameters: parameters
                                    .iter()
                                    .take(inductive.global_params as usize)
                                    .copied()
                                    .chain(fields.iter().map(|field| {
                                        Term::new(db, ExpressionT::LocalConstant(*field))
                                    }))
                                    .collect(),
                            }),
                        );
                        let (_, specialised_major_premise_args) = destructure_as_nary_application(
                            db,
                            infer_type(db, specialised_major_premise)?,
                        );
                        let specialised_motive = specialised_major_premise_args
                            .into_iter()
                            .skip(inductive.global_params as usize)
                            .rev()
                            .fold(
                                instantiate(db, match_expr.motive, specialised_major_premise),
                                |term, param| instantiate(db, term, param),
                            );
                        if !definitionally_equal(db, minor_premise_type, specialised_motive)? {
                            tracing::error!(
                                "{} != {}",
                                minor_premise_type.display(db),
                                specialised_motive.display(db)
                            );
                            todo!()
                        }
                    }

                    // The major and minor premises are correct.
                    Ok(parameters
                        .iter()
                        .skip(inductive.global_params as usize)
                        .rev()
                        .fold(
                            instantiate(db, match_expr.motive, match_expr.major_premise),
                            |term, param| instantiate(db, term, *param),
                        ))
                }
                None => todo!(),
            }
        }
        _ => todo!(),
    }
}

fn infer_type_fix(db: &dyn Db, fix: &Fix<(), Term>) -> Ir<Term> {
    todo!()
}

fn infer_type_sort(db: &dyn Db, sort: &Sort<()>) -> Ir<Term> {
    check_valid_universe(&sort.0)?;

    Ok(Term::new(
        db,
        ExpressionT::Sort(Sort(Universe::new(UniverseContents::UniverseSucc(
            UniverseSucc(Box::new(sort.0.clone())),
        )))),
    ))
}

/// Expands the given term until it is a [`Sort`].
/// If the term was not a sort, returns [`Err`].
pub fn as_sort(db: &dyn Db, t: Term) -> Ir<Sort<()>> {
    if let ExpressionT::Sort(sort) = t.value(db) {
        Ok(sort.clone())
    } else if let ExpressionT::Sort(sort) = to_weak_head_normal_form(db, t).value(db) {
        Ok(sort.clone())
    } else {
        Err(InferenceError::ExpectedSort)
    }
}

/// Expands the given term until it is a [`ExpressionT::Pi`].
/// If the term was not a function type, returns [`Err`].
fn as_pi(db: &dyn Db, t: Term) -> Ir<Binder<(), Term>> {
    if let ExpressionT::Pi(pi) = t.value(db) {
        Ok(*pi)
    } else if let ExpressionT::Pi(pi) = to_weak_head_normal_form(db, t).value(db) {
        Ok(*pi)
    } else {
        Err(InferenceError::ExpectedPi)
    }
}

/// Check that this universe contains no metauniverses.
/// TODO: Check elsewhere that all referenced universe variables were initialised in the definition.
fn check_valid_universe(u: &Universe<()>) -> Ir<()> {
    match &u.contents {
        UniverseContents::UniverseZero | UniverseContents::UniverseVariable(_) => Ok(()),
        UniverseContents::UniverseSucc(inner) => check_valid_universe(&inner.0),
        UniverseContents::UniverseMax(max) => {
            check_valid_universe(&max.left)?;
            check_valid_universe(&max.right)
        }
        UniverseContents::UniverseImpredicativeMax(imax) => {
            check_valid_universe(&imax.left)?;
            check_valid_universe(&imax.right)
        }
        UniverseContents::Metauniverse(_) => Err(InferenceError::UnexpectedMetauniverse),
    }
}
