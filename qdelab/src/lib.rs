#![feature(trait_upcasting)]

use std::collections::VecDeque;

use fcommon::{Span, Str};
use fkernel::{
    basic::{DeBruijnIndex, Name, QualifiedName, WithProvenance},
    expr::{Expression, ExpressionCache, ExpressionT},
    message,
    result::Message,
    typeck::InferenceError,
    universe::{Universe, UniverseContents},
};
use qformat::pexpression_to_document;
use qparse::expr::{PExpression, PFunctionBinder, PLambdaBinder, PUniverse};

pub fn delaborate<'cache>(
    cache: &ExpressionCache<'cache>,
    expr: Expression<'cache>,
    locals: &VecDeque<Str>,
    print_metavariable_indices: bool,
) -> PExpression {
    match expr.value(cache) {
        ExpressionT::Local(local) => PExpression::Variable {
            name: QualifiedName(WithProvenance::new_synthetic(vec![Name(
                WithProvenance::new_synthetic(
                    locals
                        .get(local.index.value() as usize)
                        .copied()
                        .unwrap_or_else(|| {
                            Str::new(
                                cache.db(),
                                format!("#{}", local.index.value() as usize - locals.len()),
                            )
                        }),
                ),
            )])),
            universe_ascription: None,
        },
        ExpressionT::Borrow(_) => todo!(),
        ExpressionT::Dereference(_) => todo!(),
        ExpressionT::Delta(_) => todo!(),
        ExpressionT::Inst(inst) => PExpression::Variable {
            name: inst.name,
            universe_ascription: if inst.universes.is_empty() {
                None
            } else {
                Some((
                    Span::default(),
                    inst.universes.iter().map(delaborate_universe).collect(),
                    Span::default(),
                ))
            },
        },
        ExpressionT::Let(_) => todo!(),
        ExpressionT::Lambda(_) => {
            let mut structures = Vec::new();
            let mut result = expr;
            while let ExpressionT::Lambda(lambda) = result.value(cache) {
                structures.push(lambda.structure);
                result = lambda.result;
            }
            let mut locals = locals.clone();
            let mut binders = Vec::new();
            for structure in structures {
                binders.push(PLambdaBinder {
                    name: structure.bound.name,
                    annotation: structure.binder_annotation,
                    brackets: None,
                    ownership: Some((structure.bound.ownership, Span::default())),
                    ty: Some(delaborate(
                        cache,
                        structure.bound.ty,
                        &locals,
                        print_metavariable_indices,
                    )),
                });
                locals.push_front(*structure.bound.name);
            }
            PExpression::Lambda {
                fn_token: Span::default(),
                binders,
                result: Box::new(delaborate(
                    cache,
                    result,
                    &locals,
                    print_metavariable_indices,
                )),
            }
        }
        ExpressionT::Pi(pi) => {
            let name_needed = pi.result.local_is_bound(cache, DeBruijnIndex::zero());
            let mut new_locals = locals.clone();
            new_locals.push_front(*pi.structure.bound.name);
            PExpression::FunctionType {
                binder: PFunctionBinder {
                    name: if name_needed {
                        Some(pi.structure.bound.name)
                    } else {
                        None
                    },
                    annotation: pi.structure.binder_annotation,
                    brackets: None,
                    ownership: Some((pi.structure.bound.ownership, Span::default())),
                    ty: Box::new(delaborate(
                        cache,
                        pi.structure.bound.ty,
                        locals,
                        print_metavariable_indices,
                    )),
                },
                arrow_token: Span::default(),
                result: Box::new(delaborate(
                    cache,
                    pi.result,
                    &new_locals,
                    print_metavariable_indices,
                )),
            }
        }
        ExpressionT::RegionLambda(_) => todo!(),
        ExpressionT::RegionPi(_) => todo!(),
        ExpressionT::Apply(apply) => PExpression::Apply {
            function: Box::new(delaborate(
                cache,
                apply.function,
                locals,
                print_metavariable_indices,
            )),
            argument: Box::new(delaborate(
                cache,
                apply.argument,
                locals,
                print_metavariable_indices,
            )),
        },
        ExpressionT::Intro(_) => todo!(),
        ExpressionT::Match(_) => todo!(),
        ExpressionT::Fix(_) => todo!(),
        ExpressionT::Sort(sort) => PExpression::Sort {
            span: Span::default(),
            universe: delaborate_universe(&sort.0),
        },
        ExpressionT::Region => PExpression::Region(Span::default()),
        ExpressionT::RegionT => PExpression::RegionT(Span::default()),
        ExpressionT::StaticRegion => todo!(),
        ExpressionT::Lifespan(_) => todo!(),
        ExpressionT::Hole(hole) => PExpression::Metavariable {
            span: Span::default(),
            id: hole.id,
            args: hole
                .args
                .iter()
                .map(|expr| delaborate(cache, *expr, locals, print_metavariable_indices))
                .collect(),
        },
        ExpressionT::RegionHole(_major_premise) => todo!(),
        ExpressionT::LocalConstant(local) => PExpression::Variable {
            name: QualifiedName(WithProvenance::new_synthetic(vec![
                if print_metavariable_indices {
                    Name(WithProvenance::new(
                        local.structure.bound.name.0.provenance,
                        Str::new(
                            cache.db(),
                            format!(
                                "{}/{}",
                                local.structure.bound.name.text(cache.db()),
                                local.id.0,
                            ),
                        ),
                    ))
                } else {
                    local.structure.bound.name
                },
            ])),
            universe_ascription: None,
        },
    }
}

pub fn delaborate_universe(universe: &Universe) -> PUniverse {
    match &universe.contents {
        UniverseContents::UniverseZero => todo!(),
        UniverseContents::UniverseVariable(name) => PUniverse::Variable(name.0),
        UniverseContents::UniverseSucc(succ) => PUniverse::Succ {
            value: Box::new(delaborate_universe(&succ.0)),
            succ_token: Span::default(),
        },
        UniverseContents::UniverseMax(_) => todo!(),
        UniverseContents::UniverseImpredicativeMax(imax) => PUniverse::ImpredicativeMax {
            imax_token: Span::default(),
            left: Box::new(delaborate_universe(&imax.left)),
            right: Box::new(delaborate_universe(&imax.right)),
        },
        UniverseContents::Metauniverse(meta) => PUniverse::Metauniverse {
            span: Span::default(),
            index: meta.0,
        },
    }
}

fn pretty_print<'cache>(cache: &ExpressionCache<'cache>, expr: Expression<'cache>) -> Message {
    Message::String(
        pexpression_to_document(
            cache.db(),
            &delaborate(cache, expr, &Default::default(), true),
        )
        .pretty_print(100),
    )
}

pub fn print_inference_error(db: &dyn fkernel::Db, err: InferenceError) -> Message {
    ExpressionCache::with_cache(db, None, None, None, |cache| match err {
        InferenceError::ExpressionNotClosed(_) => todo!(),
        InferenceError::IncorrectUniverseArity => todo!(),
        InferenceError::DefinitionNotFound(_) => todo!(),
        InferenceError::LetTypeMismatch => todo!(),
        InferenceError::ApplyTypeMismatch {
            function, argument, ..
        } => {
            message![
                "could not apply function ",
                pretty_print(cache, function.from_heap(cache)),
                " to argument ",
                pretty_print(cache, argument.from_heap(cache))
            ]
        }
        InferenceError::FunctionOwnershipMismatch => todo!(),
        InferenceError::ExpectedSort(_) => todo!(),
        InferenceError::ExpectedPi => todo!(),
        InferenceError::ExpectedDelta => todo!(),
        InferenceError::UnexpectedMetauniverse => todo!(),
        InferenceError::IncorrectIntroParameters => todo!(),
        InferenceError::MinorPremiseCountMismatch => todo!(),
    })
}
