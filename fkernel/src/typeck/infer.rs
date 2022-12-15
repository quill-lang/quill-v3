//! Infers types of terms.

use fcommon::Path;
use fexpr::{basic::Provenance, expr::*, universe::*};

use crate::{
    inductive::get_inductive,
    term::{
        abstract_binder, has_free_variables, instantiate, instantiate_universe_parameters,
        nary_binder_to_pi_expression,
    },
};

use super::{defeq::definitionally_equal, get_definition, whnf::to_weak_head_normal_form, Db};

/// An error emitted by the kernel when performing type inference or definitional equality checking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InferenceError {
    TermNotClosed,
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
            InferenceError::TermNotClosed => todo!(),
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
        Err(InferenceError::TermNotClosed)
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
    let new_local = lambda.generate_local(db, lambda.result);
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
            ExpressionT::LocalConstant(pi.generate_local(db, pi.result)),
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
    todo!()
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
