#![feature(trait_upcasting)]

use std::collections::VecDeque;

use fcommon::{Span, Str};
use fkernel::{
    basic::{Name, QualifiedName, WithProvenance},
    expr::{Expression, ExpressionCache, ExpressionT},
    universe::{Universe, UniverseContents},
};
use qparse::expr::{PExpression, PFunctionBinder, PLambdaBinder, PUniverse};

pub fn delaborate<'cache>(
    cache: &ExpressionCache<'cache>,
    expr: Expression<'cache>,
    locals: &VecDeque<Str>,
) -> PExpression {
    match expr.value(cache) {
        ExpressionT::Local(local) => PExpression::Variable {
            name: QualifiedName(WithProvenance::new_synthetic(vec![Name(
                WithProvenance::new_synthetic(locals[local.index.value() as usize]),
            )])),
            universe_ascription: None,
        },
        ExpressionT::Borrow(_) => todo!(),
        ExpressionT::Dereference(_) => todo!(),
        ExpressionT::Delta(_) => todo!(),
        ExpressionT::Inst(_) => todo!(),
        ExpressionT::Let(_) => todo!(),
        ExpressionT::Lambda(lambda) => {
            let mut structures = vec![lambda.structure];
            let mut result = lambda.result;
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
                    ty: Some(delaborate(cache, structure.bound.ty, &locals)),
                });
                locals.push_front(*structure.bound.name);
            }
            PExpression::Lambda {
                fn_token: Span::default(),
                binders,
                result: Box::new(delaborate(cache, result, &locals)),
            }
        }
        ExpressionT::Pi(pi) => {
            let mut new_locals = locals.clone();
            new_locals.push_front(*pi.structure.bound.name);
            PExpression::FunctionType {
                binder: PFunctionBinder {
                    name: Some(pi.structure.bound.name),
                    annotation: pi.structure.binder_annotation,
                    brackets: None,
                    ownership: Some((pi.structure.bound.ownership, Span::default())),
                    ty: Box::new(delaborate(cache, pi.structure.bound.ty, locals)),
                },
                arrow_token: Span::default(),
                result: Box::new(delaborate(cache, pi.result, &new_locals)),
            }
        }
        ExpressionT::RegionLambda(_) => todo!(),
        ExpressionT::RegionPi(_) => todo!(),
        ExpressionT::Apply(_) => todo!(),
        ExpressionT::Intro(_) => todo!(),
        ExpressionT::Match(_) => todo!(),
        ExpressionT::Fix(_) => todo!(),
        ExpressionT::Sort(sort) => PExpression::Sort {
            span: Span::default(),
            universe: delaborate_universe(sort.0),
        },
        ExpressionT::Region => todo!(),
        ExpressionT::RegionT => todo!(),
        ExpressionT::StaticRegion => todo!(),
        ExpressionT::Lifespan(_) => todo!(),
        ExpressionT::Metavariable(_) => todo!(),
        ExpressionT::LocalConstant(_) => todo!(),
    }
}

pub fn delaborate_universe(universe: Universe) -> PUniverse {
    match universe.contents {
        UniverseContents::UniverseZero => todo!(),
        UniverseContents::UniverseVariable(name) => PUniverse::Variable(name.0),
        UniverseContents::UniverseSucc(_) => todo!(),
        UniverseContents::UniverseMax(_) => todo!(),
        UniverseContents::UniverseImpredicativeMax(_) => todo!(),
        UniverseContents::Metauniverse(_) => todo!(),
    }
}
