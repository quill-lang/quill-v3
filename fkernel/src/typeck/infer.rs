//! Infers types of terms.

use std::collections::HashSet;

use crate::{
    basic::{DeBruijnIndex, Name, Provenance, WithProvenance},
    expr::*,
    get_certified_inductive, get_definition, get_inductive,
    inductive::CertifiedInductive,
    message,
    multiplicity::ParameterOwnership,
    result::Message,
    universe::*,
};
use fcommon::{Path, Str};

/// An error emitted by the kernel when performing type inference or definitional equality checking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InferenceError {
    ExpressionNotClosed(HeapExpression),
    IncorrectUniverseArity,
    DefinitionNotFound(Path),
    LetTypeMismatch,
    ApplyTypeMismatch {
        function: HeapExpression,
        function_type: HeapExpression,
        argument: HeapExpression,
        argument_type: HeapExpression,
    },
    FunctionOwnershipMismatch,
    ExpectedSort(HeapExpression),
    ExpectedPi,
    ExpectedDelta,
    UnexpectedMetauniverse,
    IncorrectIntroParameters,
    MinorPremiseCountMismatch,
}

impl From<InferenceError> for Message {
    fn from(value: InferenceError) -> Message {
        match value {
            InferenceError::ExpressionNotClosed(expr) => {
                message!["expression ", expr, " had free variables"]
            }
            InferenceError::IncorrectUniverseArity => todo!(),
            InferenceError::DefinitionNotFound(path) => {
                message!["definition ", path, " not found"]
            }
            InferenceError::LetTypeMismatch => todo!(),
            InferenceError::ApplyTypeMismatch {
                function,
                function_type,
                argument,
                argument_type,
            } => message![
                "cannot apply function ",
                function,
                " of type ",
                function_type,
                " to term ",
                argument,
                " of type ",
                argument_type
            ],
            InferenceError::FunctionOwnershipMismatch => todo!(),
            InferenceError::ExpectedSort(expr) => message!["expression ", expr, " was not a sort"],
            InferenceError::ExpectedPi => todo!(),
            InferenceError::ExpectedDelta => todo!(),
            InferenceError::UnexpectedMetauniverse => todo!(),
            InferenceError::IncorrectIntroParameters => todo!(),
            InferenceError::MinorPremiseCountMismatch => {
                "wrong number of minor premises for a given variant".into()
            }
        }
    }
}

/// Short for "inference result".
/// See also [`fcommon::Dr`].
///
/// Instead of emitting textual errors, the kernel emits *inference results* which either succeed
/// or error with a particular error message.
pub type Ir<T> = Result<T, InferenceError>;

impl<'cache> Expression<'cache> {
    /// Infers the type of a (closed) term.
    /// If we return [`Ok`], the provided term is type-correct and has the given type.
    pub fn infer_type(self, cache: &ExpressionCache<'cache>) -> Ir<Self> {
        if self.has_free_variables(cache) {
            Err(InferenceError::ExpressionNotClosed(self.to_heap(cache)))
        } else {
            infer_type_core(cache, self)
        }
    }
}

/// Infers the type of a closed term.
/// This function assumes that `e` is indeed a closed term and panics if it finds a free variable;
/// use [`Expression::infer_type`] if this is unknown.
/// The returned type will have synthetic provenance.
/// TODO: Cache the results.
pub(crate) fn infer_type_core<'cache>(
    cache: &ExpressionCache<'cache>,
    e: Expression<'cache>,
) -> Ir<Expression<'cache>> {
    match e.value(cache) {
        ExpressionT::Local(_) => {
            unreachable!("term should not have free variables, but a bound variable was found")
        }
        ExpressionT::Borrow(borrow) => infer_type_borrow(cache, borrow),
        ExpressionT::Dereference(deref) => infer_type_deref(cache, deref),
        ExpressionT::Delta(delta) => infer_type_delta(cache, delta),
        ExpressionT::Inst(inst) => infer_type_inst(cache, inst),
        ExpressionT::Let(inner) => infer_type_let(cache, inner),
        ExpressionT::Lambda(lambda) => infer_type_lambda(cache, lambda),
        ExpressionT::Pi(pi) => infer_type_pi(cache, pi),
        ExpressionT::RegionLambda(lambda) => infer_type_region_lambda(cache, lambda),
        ExpressionT::RegionPi(pi) => infer_type_region_pi(cache, pi),
        ExpressionT::Apply(apply) => infer_type_apply(cache, apply),
        ExpressionT::Intro(intro) => infer_type_intro(cache, intro),
        ExpressionT::Match(match_expr) => infer_type_match(cache, match_expr),
        ExpressionT::Fix(fix) => infer_type_fix(cache, fix),
        ExpressionT::Sort(sort) => infer_type_sort(cache, sort),
        ExpressionT::Region | ExpressionT::RegionT => Ok(Expression::new(
            cache,
            Provenance::Synthetic,
            ExpressionT::RegionT,
        )),
        ExpressionT::StaticRegion => Ok(Expression::new(
            cache,
            Provenance::Synthetic,
            ExpressionT::Region,
        )),
        ExpressionT::Lifespan(_) => todo!(),
        ExpressionT::Metavariable(var) => Ok(var.ty),
        ExpressionT::Metaregion(var) => {
            if var.ty.value(cache) == ExpressionT::Region {
                Ok(var.ty)
            } else {
                todo!()
            }
        }
        ExpressionT::LocalConstant(local) => Ok(local.metavariable.ty),
    }
}

fn infer_type_borrow<'cache>(
    cache: &ExpressionCache<'cache>,
    borrow: Borrow<Expression<'cache>>,
) -> Ir<Expression<'cache>> {
    infer_type_core(cache, borrow.value).map(|ty| {
        Expression::new(
            cache,
            Provenance::Synthetic,
            ExpressionT::Delta(Delta {
                region: borrow.region,
                ty,
            }),
        )
    })
}

fn infer_type_deref<'cache>(
    cache: &ExpressionCache<'cache>,
    deref: Dereference<Expression<'cache>>,
) -> Ir<Expression<'cache>> {
    infer_type_core(cache, deref.value)
        .and_then(|ty| as_delta(cache, ty))
        .map(|delta| delta.ty)
}

fn infer_type_delta<'cache>(
    cache: &ExpressionCache<'cache>,
    delta: Delta<Expression<'cache>>,
) -> Ir<Expression<'cache>> {
    let ty_type = infer_type_core(cache, delta.ty)?;
    Ok(Expression::new(
        cache,
        Provenance::Synthetic,
        ExpressionT::Sort(as_sort(cache, ty_type)?),
    ))
}

fn infer_type_inst<'cache>(cache: &ExpressionCache<'cache>, inst: Inst) -> Ir<Expression<'cache>> {
    let path = inst.name.to_path(cache.db());
    match get_definition(cache.db(), path).value() {
        Some(def) => {
            if def.contents.universe_params.len() == inst.universes.len() {
                for u in &inst.universes {
                    check_valid_universe(u)?;
                }
                if def.contents.universe_params.len() != inst.universes.len() {
                    todo!()
                }
                Ok(def
                    .contents
                    .ty
                    .from_heap(cache)
                    .instantiate_universe_parameters(
                        cache,
                        &def.contents.universe_params,
                        &inst.universes,
                    ))
            } else {
                Err(InferenceError::IncorrectUniverseArity)
            }
        }
        None => match get_inductive(cache.db(), path).value() {
            Some(ind) => {
                if ind.contents.universe_params.len() == inst.universes.len() {
                    for u in &inst.universes {
                        check_valid_universe(u)?;
                    }
                    if ind.contents.universe_params.len() != inst.universes.len() {
                        todo!()
                    }
                    Ok(Expression::nary_binder_to_pi(
                        cache,
                        Provenance::Synthetic,
                        ind.contents.ty.from_heap(cache),
                    )
                    .instantiate_universe_parameters(
                        cache,
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

fn infer_type_let<'cache>(
    cache: &ExpressionCache<'cache>,
    inner: Let<Expression<'cache>>,
) -> Ir<Expression<'cache>> {
    // The type of the value to assign must be a type.
    // That is, its type must be a sort.
    let let_type_type = infer_type_core(cache, inner.bound.ty)?;
    as_sort(cache, let_type_type)?;

    // Infer the type of the value to substitute.
    let let_value_type = infer_type_core(cache, inner.to_assign)?;

    // The value that we assign must have type definitionally equal to the type to assign.
    if !Expression::definitionally_equal(cache, let_value_type, inner.bound.ty)? {
        return Err(InferenceError::LetTypeMismatch);
    }

    // We perform a step of zeta-reduction and then infer the type of the body of the expression.
    infer_type_core(cache, inner.body.instantiate(cache, inner.to_assign))
}

fn infer_type_lambda<'cache>(
    cache: &ExpressionCache<'cache>,
    lambda: Binder<Expression<'cache>>,
) -> Ir<Expression<'cache>> {
    // The argument type must be a type.
    let argument_type_type = infer_type_core(cache, lambda.structure.bound.ty)?;
    as_sort(cache, argument_type_type)?;

    // Infer the return type of the lambda by first instantiating the parameter then inferring the resulting type.
    let new_local = lambda.structure.generate_local(cache, lambda.result);
    let body = lambda.result.instantiate(
        cache,
        Expression::new(
            cache,
            Provenance::Synthetic,
            ExpressionT::LocalConstant(new_local),
        ),
    );
    let return_type = infer_type_core(cache, body)?;
    Ok(Expression::new(
        cache,
        Provenance::Synthetic,
        ExpressionT::Pi(return_type.abstract_binder(cache, new_local)),
    ))
}

fn infer_type_pi<'cache>(
    cache: &ExpressionCache<'cache>,
    pi: Binder<Expression<'cache>>,
) -> Ir<Expression<'cache>> {
    // The argument type must be a type.
    let parameter_type = infer_type_core(cache, pi.structure.bound.ty)?;
    let domain_type = as_sort(cache, parameter_type)?;

    // Infer the return type of the pi by first instantiating the parameter then inferring the resulting type.
    let body = pi.result.instantiate(
        cache,
        Expression::new(
            cache,
            Provenance::Synthetic,
            ExpressionT::LocalConstant(pi.structure.generate_local(cache, pi.result)),
        ),
    );
    let return_type = as_sort(cache, infer_type_core(cache, body)?)?;
    Ok(Expression::new(
        cache,
        Provenance::Synthetic,
        ExpressionT::Sort(Sort(Universe::new_with_provenance(
            Provenance::Synthetic,
            UniverseContents::UniverseImpredicativeMax(UniverseImpredicativeMax {
                left: Box::new(domain_type.0),
                right: Box::new(return_type.0),
            }),
        ))),
    ))
}

fn infer_type_region_lambda<'cache>(
    cache: &ExpressionCache<'cache>,
    lambda: RegionBinder<Expression<'cache>>,
) -> Ir<Expression<'cache>> {
    let new_local = lambda.generate_local(cache, lambda.body);
    let body = lambda.body.instantiate(
        cache,
        Expression::new(
            cache,
            Provenance::Synthetic,
            ExpressionT::LocalConstant(new_local),
        ),
    );
    let return_type = infer_type_core(cache, body)?;
    Ok(Expression::new(
        cache,
        Provenance::Synthetic,
        ExpressionT::RegionPi(return_type.abstract_region_binder(cache, new_local)),
    ))
}

fn infer_type_region_pi<'cache>(
    cache: &ExpressionCache<'cache>,
    pi: RegionBinder<Expression<'cache>>,
) -> Ir<Expression<'cache>> {
    // TODO: Check that the region variable occurs simply in the term.
    let new_local = pi.generate_local(cache, pi.body);
    let body = pi.body.instantiate(
        cache,
        Expression::new(
            cache,
            Provenance::Synthetic,
            ExpressionT::LocalConstant(new_local),
        ),
    );
    let return_type = infer_type_core(cache, body)?;
    // Assuming that the region variable occurs simply in the body of the abstraction,
    // we can replace it with the static region.
    Ok(return_type.replace_local(
        cache,
        &new_local,
        Expression::new(cache, Provenance::Synthetic, ExpressionT::StaticRegion),
    ))
}

fn infer_type_apply<'cache>(
    cache: &ExpressionCache<'cache>,
    apply: Apply<Expression<'cache>>,
) -> Ir<Expression<'cache>> {
    let function_type = infer_type_core(cache, apply.function)?;
    match as_delta(cache, function_type) {
        Ok(function_type_delta) => match as_pi(cache, function_type_delta.ty) {
            Ok(function_type_binder) => {
                if function_type_binder.structure.function_ownership != FunctionOwnership::Many {
                    return Err(InferenceError::FunctionOwnershipMismatch);
                }

                let argument_type = infer_type_core(cache, apply.argument)?;

                if !Expression::definitionally_equal(
                    cache,
                    argument_type,
                    function_type_binder.structure.bound.ty,
                )? {
                    return Err(InferenceError::ApplyTypeMismatch {
                        function: apply.function.to_heap(cache),
                        function_type: function_type.to_heap(cache),
                        argument: apply.argument.to_heap(cache),
                        argument_type: argument_type.to_heap(cache),
                    });
                }

                Ok(function_type_binder
                    .result
                    .instantiate(cache, apply.argument))
            }
            Err(_) => Err(InferenceError::ApplyTypeMismatch {
                function: apply.function.to_heap(cache),
                function_type: function_type.to_heap(cache),
                argument: apply.argument.to_heap(cache),
                argument_type: infer_type_core(cache, apply.argument)?.to_heap(cache),
            }),
        },
        Err(_) => match as_pi(cache, function_type) {
            Ok(function_type_binder) => {
                if function_type_binder.structure.function_ownership != FunctionOwnership::Once {
                    return Err(InferenceError::FunctionOwnershipMismatch);
                }

                let argument_type = infer_type_core(cache, apply.argument)?;

                if !Expression::definitionally_equal(
                    cache,
                    argument_type,
                    function_type_binder.structure.bound.ty,
                )? {
                    return Err(InferenceError::ApplyTypeMismatch {
                        function: apply.function.to_heap(cache),
                        function_type: function_type.to_heap(cache),
                        argument: apply.argument.to_heap(cache),
                        argument_type: argument_type.to_heap(cache),
                    });
                }

                Ok(function_type_binder
                    .result
                    .instantiate(cache, apply.argument))
            }
            Err(_) => {
                let function_type_binder = as_region_pi(cache, function_type)?;
                let argument_type = infer_type_core(cache, apply.argument)?;

                if !Expression::definitionally_equal(
                    cache,
                    argument_type,
                    Expression::new(cache, Provenance::Synthetic, ExpressionT::Region),
                )? {
                    return Err(InferenceError::ApplyTypeMismatch {
                        function: apply.function.to_heap(cache),
                        function_type: function_type.to_heap(cache),
                        argument: apply.argument.to_heap(cache),
                        argument_type: argument_type.to_heap(cache),
                    });
                }

                Ok(function_type_binder.body.instantiate(cache, apply.argument))
            }
        },
    }
}

fn infer_type_intro<'cache>(
    cache: &ExpressionCache<'cache>,
    intro: Intro<Expression<'cache>>,
) -> Ir<Expression<'cache>> {
    match get_inductive(cache.db(), intro.inductive.to_path(cache.db())).value() {
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
                            .fold(*param, |e, param| e.instantiate(cache, *param));

                        let expected_type = intro.parameters.iter().take(index).rev().fold(
                            variant.intro_rule.structures[index]
                                .bound
                                .ty
                                .from_heap(cache)
                                .instantiate_universe_parameters(
                                    cache,
                                    &inductive.universe_params,
                                    &intro.universes,
                                ),
                            |e, param| e.instantiate(cache, *param),
                        );

                        if !Expression::definitionally_equal(
                            cache,
                            param_instantiated.infer_type(cache)?,
                            expected_type,
                        )? {
                            todo!()
                        }
                    }

                    Ok(intro.parameters.iter().rev().fold(
                        variant
                            .intro_rule
                            .result
                            .from_heap(cache)
                            .instantiate_universe_parameters(
                                cache,
                                &inductive.universe_params,
                                &intro.universes,
                            ),
                        |e, param| e.instantiate(cache, *param),
                    ))
                }
                None => todo!(),
            }
        }
        None => todo!(),
    }
}

/// If `borrowed` is `Some(t)`, then `t` is the region for which the major premise is borrowed.
fn process_match<'cache>(
    match_expr: &Match<Expression<'cache>>,
    inductive: &CertifiedInductive,
    cache: &ExpressionCache<'cache>,
    inductive_term: Expression<'cache>,
    parameters: Vec<Expression<'cache>>,
    inst: &Inst,
    borrowed: Option<Expression<'cache>>,
) -> Ir<Expression<'cache>> {
    // TODO: Check if we need to `lift_free_vars` on the global parameters below.

    // The major premise is indeed of an inductive type, and the inductive type exists.
    // Check that `index_params` is correct.
    if match_expr.index_params
        != (inductive.inductive.ty.structures.len() as u32) - inductive.inductive.global_params
    {
        // The number of `index_params` stated in the match expression was wrong.
        todo!()
    }

    // Check the type of the motive.
    // This is accomplished by turning the motive into a lambda abstraction
    // where the parameters are the inductive's index parameters and then the major premise,
    // then checking the type of the resulting lambda.
    let structures = inductive
        .inductive
        .ty
        .structures
        .iter()
        .map(|expr| expr.from_heap(cache))
        .skip(inductive.inductive.global_params as usize)
        .chain(std::iter::once(BinderStructure {
            // The structure here isn't really relevant.
            bound: BoundVariable {
                name: Name(WithProvenance::new_with_provenance(
                    Provenance::Synthetic,
                    Str::new(cache.db(), "_major_premise".to_owned()),
                )),
                ty: {
                    let ty = inductive_term.create_nary_application(
                        cache,
                        inductive
                            .inductive
                            .ty
                            .structures
                            .iter()
                            .enumerate()
                            .rev()
                            .map(|(index, _)| {
                                (
                                    Provenance::Synthetic,
                                    Expression::new(
                                        cache,
                                        Provenance::Synthetic,
                                        ExpressionT::Local(Local {
                                            index: DeBruijnIndex::new(index as u32),
                                        }),
                                    ),
                                )
                            }),
                    );
                    if let Some(region) = borrowed {
                        Expression::new(
                            cache,
                            Provenance::Synthetic,
                            ExpressionT::Delta(Delta { region, ty }),
                        )
                    } else {
                        ty
                    }
                },
                ownership: ParameterOwnership::POwned,
            },
            function_ownership: FunctionOwnership::Once,
            binder_annotation: BinderAnnotation::Explicit,
            region: Expression::new(cache, Provenance::Synthetic, ExpressionT::StaticRegion),
        }))
        .collect();
    let binders = NaryBinder {
        structures,
        result: match_expr.motive,
    };
    let motive_lambda = parameters
        .iter()
        .take(inductive.inductive.global_params as usize)
        .rev()
        .fold(
            Expression::nary_binder_to_lambda(cache, Provenance::Synthetic, binders),
            |ty, expr| ty.instantiate(cache, *expr),
        );
    motive_lambda.infer_type(cache)?;
    // The motive is type correct.

    // Check each minor premise.
    // First, check that there is exactly one minor premise for each variant.
    for variant in &inductive.inductive.variants {
        let matching_minor_premises = match_expr
            .minor_premises
            .iter()
            .filter(|premise| *premise.variant == *variant.name)
            .collect::<Vec<_>>();
        if matching_minor_premises.len() != 1 {
            return Err(InferenceError::MinorPremiseCountMismatch);
        }
    }
    // Check that each minor premise is type correct.
    for premise in &match_expr.minor_premises {
        // Get the variant of the inductive that this minor premise matches.
        let variant = if let Some(variant) = inductive
            .inductive
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
            != (variant.intro_rule.structures.len() as u32) - inductive.inductive.global_params
        {
            // The number of fields stated in the match expression was wrong.
            todo!()
        }

        let mut structures = variant
            .intro_rule
            .structures
            .iter()
            .skip(inductive.inductive.global_params as usize)
            .map(|expr| expr.from_heap(cache))
            .collect::<Vec<_>>();
        if let Some(region) = borrowed {
            // We turn each bound field into its borrowed version.
            for i in 0..structures.len() {
                structures[i].bound.ty = Expression::new(
                    cache,
                    Provenance::Synthetic,
                    ExpressionT::Delta(Delta {
                        region,
                        ty: structures[i].bound.ty,
                    }),
                );
                // Update later binders to dereference this field instead of using it directly.
                for (j, structure) in structures.iter_mut().enumerate().skip(i + 1) {
                    structure.bound.ty =
                        structure
                            .bound
                            .ty
                            .replace_in_expression(cache, &|e, offset| {
                                if let ExpressionT::Local(local) = e.value(cache) {
                                    if local.index
                                        == DeBruijnIndex::new((j - i - 1) as u32) + offset
                                    {
                                        // This is the variable that we just modified the type of.
                                        ReplaceResult::ReplaceWith(Expression::new(
                                            cache,
                                            Provenance::Synthetic,
                                            ExpressionT::Dereference(Dereference { value: e }),
                                        ))
                                    } else {
                                        ReplaceResult::Skip
                                    }
                                } else {
                                    ReplaceResult::Skip
                                }
                            });
                }
            }
        }
        let binders = NaryBinder {
            structures,
            result: premise.result,
        };
        let premise_lambda = parameters
            .iter()
            .take(inductive.inductive.global_params as usize)
            .rev()
            .fold(
                Expression::nary_binder_to_lambda(cache, Provenance::Synthetic, binders),
                |ty, expr| ty.instantiate(cache, *expr),
            );
        let mut minor_premise_type = premise_lambda.infer_type(cache)?;

        // Check that the minor premise type matches the motive.
        // Strip off the fields from the type of the minor premise.
        let mut fields = Vec::new();
        let mut meta_gen = MetavariableGenerator::new(
            Expression::new(
                cache,
                Provenance::Synthetic,
                ExpressionT::Match(match_expr.clone()),
            )
            .largest_unusable_metavariable(cache),
        );
        for _ in 0..premise.fields {
            match minor_premise_type.value(cache) {
                ExpressionT::Pi(pi) => {
                    let field = pi.structure.generate_local_with_gen(&mut meta_gen);
                    minor_premise_type = pi.result.instantiate(
                        cache,
                        Expression::new(
                            cache,
                            Provenance::Synthetic,
                            ExpressionT::LocalConstant(field),
                        ),
                    );
                    fields.push(field);
                }
                _ => unreachable!(),
            }
        }
        // Instantiate the motive with the index parameters and the inductive.
        let specialised_major_premise = Expression::new(
            cache,
            Provenance::Synthetic,
            ExpressionT::Intro(Intro {
                inductive: inst.name.clone(),
                universes: inst.universes.clone(),
                variant: variant.name,
                parameters: parameters
                    .iter()
                    .take(inductive.inductive.global_params as usize)
                    .copied()
                    .chain(fields.iter().map(|field| {
                        if borrowed.is_some() {
                            Expression::new(
                                cache,
                                Provenance::Synthetic,
                                ExpressionT::Dereference(Dereference {
                                    value: Expression::new(
                                        cache,
                                        Provenance::Synthetic,
                                        ExpressionT::LocalConstant(*field),
                                    ),
                                }),
                            )
                        } else {
                            Expression::new(
                                cache,
                                Provenance::Synthetic,
                                ExpressionT::LocalConstant(*field),
                            )
                        }
                    }))
                    .collect(),
            }),
        );
        let (_, specialised_major_premise_args) = specialised_major_premise
            .infer_type(cache)?
            .destructure_as_nary_application(cache);
        let specialised_motive = specialised_major_premise_args
            .into_iter()
            .skip(inductive.inductive.global_params as usize)
            .rev()
            .fold(
                match_expr
                    .motive
                    .instantiate(cache, specialised_major_premise),
                |expr, param| expr.instantiate(cache, param),
            );
        if !Expression::definitionally_equal(cache, minor_premise_type, specialised_motive)? {
            todo!()
        }
    }

    // The major and minor premises are correct.
    let result = parameters
        .iter()
        .skip(inductive.inductive.global_params as usize)
        .rev()
        .fold(
            match_expr
                .motive
                .instantiate(cache, match_expr.major_premise),
            |expr, param| expr.instantiate(cache, *param),
        );

    // Check if we're eliminating into a permitted universe.
    if inductive.eliminate_only_into_prop {
        let sort = as_sort(cache, result.infer_type(cache)?)?;
        if !sort.0.is_zero() {
            todo!()
        }
    }

    // All checks have passed, so the match expression is type correct.
    Ok(result)
}

fn infer_type_match<'cache>(
    cache: &ExpressionCache<'cache>,
    match_expr: Match<Expression<'cache>>,
) -> Ir<Expression<'cache>> {
    let major_premise_type = match_expr.major_premise.infer_type(cache)?;
    match major_premise_type.value(cache) {
        ExpressionT::Delta(delta) => {
            let (inductive_term, parameters) = delta.ty.destructure_as_nary_application(cache);
            match inductive_term.value(cache) {
                ExpressionT::Inst(inst) => {
                    match get_certified_inductive(cache.db(), inst.name.to_path(cache.db())) {
                        Some(inductive) => process_match(
                            &match_expr,
                            inductive,
                            cache,
                            inductive_term,
                            parameters,
                            &inst,
                            Some(delta.region),
                        ),
                        None => todo!(),
                    }
                }
                _ => todo!(),
            }
        }
        _ => {
            let (inductive_term, parameters) =
                major_premise_type.destructure_as_nary_application(cache);
            match inductive_term.value(cache) {
                ExpressionT::Inst(inst) => {
                    match get_certified_inductive(cache.db(), inst.name.to_path(cache.db())) {
                        Some(inductive) => process_match(
                            &match_expr,
                            inductive,
                            cache,
                            inductive_term,
                            parameters,
                            &inst,
                            None,
                        ),
                        None => todo!(),
                    }
                }
                _ => todo!(),
            }
        }
    }
}

/// Ensures that arguments of `fixpoint` are structurally smaller than `local`.
/// `structurally_smaller` is a set of metavariables that we know are structurally smaller than `local`.
/// TODO: Fixed point expressions for borrowed inductive types.
fn check_decreasing<'cache>(
    cache: &ExpressionCache<'cache>,
    meta_gen: &mut MetavariableGenerator<Expression<'cache>>,
    expr: Expression<'cache>,
    local: LocalConstant<Expression<'cache>>,
    fixpoint: LocalConstant<Expression<'cache>>,
    structurally_smaller: &HashSet<u32>,
) -> Ir<()> {
    match expr.value(cache) {
        ExpressionT::Apply(apply) => {
            if apply.function
                == Expression::new(
                    cache,
                    Provenance::Synthetic,
                    ExpressionT::LocalConstant(fixpoint),
                )
            {
                // The fixpoint function is being invoked.
                // Its argument must be a local constant that is structurally smaller than `local`.
                match apply.argument.value(cache) {
                    ExpressionT::Metavariable(metavariable) => {
                        if structurally_smaller.contains(&metavariable.index) {
                            Ok(())
                        } else {
                            todo!()
                        }
                    }
                    _ => {
                        // The argument to the fixpoint function was not a metavariable.
                        todo!()
                    }
                }
            } else {
                Ok(())
            }
        }
        ExpressionT::Match(match_expr) => {
            match match_expr.major_premise.value(cache) {
                ExpressionT::LocalConstant(constant) => {
                    if local.metavariable.index == constant.metavariable.index {
                        // We're performing pattern matching on the local constant we need to check.
                        check_decreasing(
                            cache,
                            meta_gen,
                            match_expr.motive,
                            local,
                            fixpoint,
                            structurally_smaller,
                        )?;
                        let dummy_term =
                            Expression::new(cache, Provenance::Synthetic, ExpressionT::RegionT);
                        for premise in &match_expr.minor_premises {
                            let mut smaller = structurally_smaller.clone();
                            let mut premise_result = premise.result;
                            for _ in 0..premise.fields {
                                let metavariable = meta_gen.gen(dummy_term);
                                premise_result = premise_result.instantiate(
                                    cache,
                                    Expression::new(
                                        cache,
                                        Provenance::Synthetic,
                                        ExpressionT::Metavariable(metavariable),
                                    ),
                                );
                                smaller.insert(metavariable.index);
                            }
                            check_decreasing(
                                cache,
                                meta_gen,
                                premise_result,
                                local,
                                fixpoint,
                                &smaller,
                            )?;
                        }
                        Ok(())
                    } else {
                        Ok(())
                    }
                }
                _ => Ok(()),
            }
        }
        ExpressionT::LocalConstant(constant) => {
            if fixpoint.metavariable.index == constant.metavariable.index {
                // The fixpoint function cannot occur in a position other than function application.
                // Since we already handled function application earlier, this is an error.
                todo!()
            } else {
                Ok(())
            }
        }
        _ => {
            for expr in expr.subexpressions(cache) {
                check_decreasing(cache, meta_gen, expr, local, fixpoint, structurally_smaller)?;
            }
            Ok(())
        }
    }
}

/// If `borrowed` is `Some(t)`, then `t` is the region for which the major premise is borrowed.
fn process_fix<'cache>(
    cache: &ExpressionCache<'cache>,
    argument_type: Expression<'cache>,
    fix: Fix<Expression<'cache>>,
    borrowed: Option<Expression<'cache>>,
) -> Result<Expression<'cache>, InferenceError> {
    let inductive_term = argument_type.leftmost_function(cache);
    match inductive_term.value(cache) {
        ExpressionT::Inst(inst) => {
            if get_inductive(cache.db(), inst.name.to_path(cache.db()))
                .value()
                .is_some()
            {
                // The argument is indeed of an inductive type, and the inductive type exists.
                // Check that the body of the fixed point expression is of the correct type.
                let mut meta_gen = MetavariableGenerator::new(
                    Expression::new(cache, Provenance::Synthetic, ExpressionT::Fix(fix))
                        .largest_unusable_metavariable(cache),
                );

                let argument_type_or_delta = if let Some(region) = borrowed {
                    Expression::new(
                        cache,
                        Provenance::Synthetic,
                        ExpressionT::Delta(Delta {
                            region,
                            ty: argument_type,
                        }),
                    )
                } else {
                    argument_type
                };

                let argument_structure = BinderStructure {
                    // The structure here isn't really relevant.
                    bound: BoundVariable {
                        name: Name(WithProvenance::new_synthetic(Str::new(
                            cache.db(),
                            "_parameter".to_owned(),
                        ))),
                        ty: argument_type_or_delta,
                        ownership: ParameterOwnership::POwned,
                    },
                    binder_annotation: BinderAnnotation::Explicit,
                    function_ownership: FunctionOwnership::Once,
                    region: Expression::new(
                        cache,
                        Provenance::Synthetic,
                        ExpressionT::StaticRegion,
                    ),
                };
                let argument_local = LocalConstant {
                    metavariable: meta_gen.gen(argument_type_or_delta),
                    structure: argument_structure,
                };
                let argument_local_term = Expression::new(
                    cache,
                    Provenance::Synthetic,
                    ExpressionT::LocalConstant(argument_local),
                );
                let fixpoint_body_pi = Expression::new(
                    cache,
                    Provenance::Synthetic,
                    ExpressionT::Pi(Binder {
                        structure: argument_structure,
                        result: fix.fixpoint.ty,
                    }),
                );
                let fixpoint_local = LocalConstant {
                    metavariable: meta_gen.gen(fixpoint_body_pi),
                    structure: BinderStructure {
                        // The structure here isn't really relevant.
                        bound: BoundVariable {
                            name: Name(WithProvenance::new_synthetic(Str::new(
                                cache.db(),
                                "_fixpoint".to_owned(),
                            ))),
                            ty: fixpoint_body_pi,
                            ownership: ParameterOwnership::POwned,
                        },
                        binder_annotation: BinderAnnotation::Explicit,
                        function_ownership: FunctionOwnership::Once,
                        region: Expression::new(
                            cache,
                            Provenance::Synthetic,
                            ExpressionT::StaticRegion,
                        ),
                    },
                };

                let body_instantiated = fix
                    .body
                    .instantiate(cache, argument_local_term)
                    .instantiate(
                        cache,
                        Expression::new(
                            cache,
                            Provenance::Synthetic,
                            ExpressionT::LocalConstant(fixpoint_local),
                        ),
                    );

                let expected_fixpoint_body_type =
                    fix.fixpoint.ty.instantiate(cache, argument_local_term);

                if !Expression::definitionally_equal(
                    cache,
                    expected_fixpoint_body_type,
                    body_instantiated.infer_type(cache)?,
                )? {
                    todo!()
                }

                // The fixed point construction was correctly typed.
                // Check that the fixed point construction is only invoked using structurally smaller parameters.
                check_decreasing(
                    cache,
                    &mut meta_gen,
                    body_instantiated,
                    argument_local,
                    fixpoint_local,
                    &HashSet::new(),
                )?;

                // The fixed point construction is sound and type correct.
                Ok(fix.fixpoint.ty.instantiate(cache, fix.argument))
            } else {
                todo!()
            }
        }
        _ => todo!(),
    }
}

fn infer_type_fix<'cache>(
    cache: &ExpressionCache<'cache>,
    fix: Fix<Expression<'cache>>,
) -> Ir<Expression<'cache>> {
    let argument_type = fix.argument.infer_type(cache)?;
    match argument_type.value(cache) {
        ExpressionT::Delta(delta) => process_fix(cache, delta.ty, fix, Some(delta.region)),
        _ => process_fix(cache, argument_type, fix, None),
    }
}

fn infer_type_sort<'cache>(cache: &ExpressionCache<'cache>, sort: Sort) -> Ir<Expression<'cache>> {
    check_valid_universe(&sort.0)?;

    Ok(Expression::new(
        cache,
        Provenance::Synthetic,
        ExpressionT::Sort(Sort(Universe::new_synthetic(
            UniverseContents::UniverseSucc(UniverseSucc(Box::new(sort.0))),
        ))),
    ))
}

/// Expands the given term until it is a [`Sort`].
/// If the term was not a sort, returns [`Err`].
pub fn as_sort<'cache>(cache: &ExpressionCache<'cache>, expr: Expression<'cache>) -> Ir<Sort> {
    if let ExpressionT::Sort(sort) = expr.value(cache) {
        Ok(sort)
    } else if let ExpressionT::Sort(sort) = expr.to_weak_head_normal_form(cache).value(cache) {
        Ok(sort)
    } else {
        Err(InferenceError::ExpectedSort(expr.to_heap(cache)))
    }
}

/// Expands the given term until it is a [`ExpressionT::Pi`].
/// If the term was not a function type, returns [`Err`].
fn as_pi<'cache>(
    cache: &ExpressionCache<'cache>,
    expr: Expression<'cache>,
) -> Ir<Binder<Expression<'cache>>> {
    if let ExpressionT::Pi(pi) = expr.value(cache) {
        Ok(pi)
    } else if let ExpressionT::Pi(pi) = expr.to_weak_head_normal_form(cache).value(cache) {
        Ok(pi)
    } else {
        Err(InferenceError::ExpectedPi)
    }
}

/// Expands the given term until it is a [`ExpressionT::RegionPi`].
/// If the term was not a function type, returns [`Err`].
/// The error this returns is [`InferenceError::ExpectedPi`] because
/// this function is called when we expect either a region pi or a normal pi.
fn as_region_pi<'cache>(
    cache: &ExpressionCache<'cache>,
    expr: Expression<'cache>,
) -> Ir<RegionBinder<Expression<'cache>>> {
    if let ExpressionT::RegionPi(pi) = expr.value(cache) {
        Ok(pi)
    } else if let ExpressionT::RegionPi(pi) = expr.to_weak_head_normal_form(cache).value(cache) {
        Ok(pi)
    } else {
        Err(InferenceError::ExpectedPi)
    }
}

/// Expands the given term until it is a [`ExpressionT::Delta`].
/// If the term was not a function type, returns [`Err`].
fn as_delta<'cache>(
    cache: &ExpressionCache<'cache>,
    expr: Expression<'cache>,
) -> Ir<Delta<Expression<'cache>>> {
    if let ExpressionT::Delta(delta) = expr.value(cache) {
        Ok(delta)
    } else if let ExpressionT::Delta(delta) = expr.to_weak_head_normal_form(cache).value(cache) {
        Ok(delta)
    } else {
        Err(InferenceError::ExpectedDelta)
    }
}

/// Check that this universe contains no metauniverses.
/// TODO: Check elsewhere that all referenced universe variables were initialised in the definition.
fn check_valid_universe(u: &Universe) -> Ir<()> {
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
