//! Utilities for traversing the term tree for things like find-and-replace operations.

use std::{cell::RefCell, cmp::Ordering};

use fexpr::{
    basic::{DeBruijnIndex, DeBruijnOffset, Name, QualifiedName},
    expr::*,
    universe::{Universe, UniverseVariable},
};

use crate::{
    typeck::{definition_height, DefinitionHeight},
    universe::instantiate_universe,
    Db,
};

enum ReplaceResult {
    /// The term should not be replaced.
    Skip,
    /// The term should be replaced with the given value.
    ReplaceWith(Term),
}

/// Traverses the term tree and finds terms matching the provided replacement function.
/// If any matched, the replacement function generates the value to replace the found value with.
/// The provided [`DeBruijnOffset`] gives the amount of binders the [`Expr`] argument is currently under.
#[must_use]
fn replace_in_term(
    db: &dyn Db,
    t: Term,
    replace_fn: impl Clone + Fn(Term, DeBruijnOffset) -> ReplaceResult,
) -> Term {
    replace_in_term_offset(db, t, replace_fn, DeBruijnOffset::zero())
}

/// Like [`replace_in_term`] but keeps track of sub-term de Bruijn index offsets.
#[rustfmt::skip]
#[must_use]
fn replace_in_term_offset(
    db: &dyn Db,
    t: Term,
    replace_fn: impl Clone + Fn(Term, DeBruijnOffset) -> ReplaceResult,
    offset: DeBruijnOffset,
) -> Term {
    // Invoke the replacement function.
    match replace_fn(t, offset) {
        ReplaceResult::Skip => {
            // Traverse the sub-terms of `e`.
            match t.value(db) {
                ExpressionT::Local(_) | ExpressionT::Borrow(_) | ExpressionT::LocalRegion(_) | ExpressionT::Inst(_) => t,
                ExpressionT::Let(t) => Term::new(
                    db,
                    ExpressionT::Let(Let {
                        bound: BoundVariable {
                            ty: replace_in_term_offset(db, t.bound.ty, replace_fn.clone(), offset),
                            ..t.bound
                        },
                        to_assign: replace_in_term_offset(db, t.to_assign, replace_fn.clone(), offset),
                        body: replace_in_term_offset(db, t.body, replace_fn, offset.succ()),
                    }),
                ),
                ExpressionT::Lambda(t) => Term::new(
                    db,
                    ExpressionT::Lambda(Binder {
                        structure: BinderStructure {
                            bound: BoundVariable {
                                ty: replace_in_term_offset(db, t.structure.bound.ty, replace_fn.clone(), offset),
                                ..t.structure.bound
                            },
                            region: replace_in_term_offset(db, t.structure.region, replace_fn.clone(), offset),
                            ..t.structure
                        },
                        result: replace_in_term_offset(db, t.result, replace_fn, offset),
                    }),
                ),
                ExpressionT::Pi(t) => Term::new(
                    db,
                    ExpressionT::Pi(Binder {
                        structure: BinderStructure {
                            bound: BoundVariable {
                                ty: replace_in_term_offset(db, t.structure.bound.ty, replace_fn.clone(), offset),
                                ..t.structure.bound
                            },
                            region: replace_in_term_offset(db, t.structure.region, replace_fn.clone(), offset),
                            ..t.structure
                        },
                        result: replace_in_term_offset(db, t.result, replace_fn, offset),
                    }),
                ),
                ExpressionT::RegionLambda(t) => Term::new(
                    db,
                    ExpressionT::RegionLambda(RegionBinder {
                        region_name: t.region_name,
                        body: replace_in_term_offset(db, t.body, replace_fn, offset),
                    }),
                ),
                ExpressionT::RegionPi(t) => Term::new(
                    db,
                    ExpressionT::RegionPi(RegionBinder {
                        region_name: t.region_name,
                        body: replace_in_term_offset(db, t.body, replace_fn, offset.succ()),
                    }),
                ),
                ExpressionT::Delta(t) => Term::new(
                    db,
                    ExpressionT::Delta(Delta {
                        region: replace_in_term_offset(db, t.region, replace_fn.clone(), offset),
                        ty: replace_in_term_offset(db, t.ty, replace_fn, offset),
                    }),
                ),
                ExpressionT::Apply(t) => Term::new(
                    db,
                    ExpressionT::Apply(Apply {
                        function: replace_in_term_offset(db, t.function, replace_fn.clone(), offset),
                        argument: replace_in_term_offset(db, t.argument, replace_fn, offset),
                    }),
                ),
                ExpressionT::Lifespan(t) => Term::new(
                    db,
                    ExpressionT::Lifespan(Lifespan {
                        ty: replace_in_term_offset(db, t.ty, replace_fn, offset),
                    })
                ),
                ExpressionT::Sort(_)
                | ExpressionT::Region
                | ExpressionT::StaticRegion
                | ExpressionT::Metavariable(_)
                | ExpressionT::LocalConstant(_) => t,
            }
        }
        ReplaceResult::ReplaceWith(t_replaced) => {
            // We replace `t` with the given value.
            // We don't try to traverse the sub-terms of this returned value.
            t_replaced
        }
    }
}

/// Traverses the term tree and finds terms matching the provided predicate.
/// If any return `true`, the first such term is returned.
/// The tree is traversed depth first.
fn find_in_term(
    db: &dyn Db,
    t: Term,
    predicate: impl Clone + Fn(Term, DeBruijnOffset) -> bool,
) -> Option<Term> {
    find_in_term_offset(db, t, predicate, DeBruijnOffset::zero())
}

/// Like [`find_in_term`] but keeps track of sub-term de Bruijn index offsets.
fn find_in_term_offset(
    db: &dyn Db,
    t: Term,
    predicate: impl Clone + Fn(Term, DeBruijnOffset) -> bool,
    offset: DeBruijnOffset,
) -> Option<Term> {
    if predicate(t, offset) {
        Some(t)
    } else {
        match t.value(db) {
            ExpressionT::Local(_)
            | ExpressionT::Borrow(_)
            | ExpressionT::LocalRegion(_)
            | ExpressionT::Inst(_) => None,
            ExpressionT::Let(t) => find_in_term_offset(db, t.to_assign, predicate.clone(), offset)
                .or_else(|| find_in_term_offset(db, t.bound.ty, predicate.clone(), offset))
                .or_else(|| find_in_term_offset(db, t.body, predicate, offset.succ())),
            ExpressionT::Lambda(t) | ExpressionT::Pi(t) => {
                find_in_term_offset(db, t.structure.region, predicate.clone(), offset)
                    .or_else(|| {
                        find_in_term_offset(db, t.structure.bound.ty, predicate.clone(), offset)
                    })
                    .or_else(|| find_in_term_offset(db, t.result, predicate, offset.succ()))
            }
            ExpressionT::RegionLambda(t) | ExpressionT::RegionPi(t) => {
                find_in_term_offset(db, t.body, predicate, offset.succ())
            }
            ExpressionT::Delta(t) => find_in_term_offset(db, t.region, predicate.clone(), offset)
                .or_else(|| find_in_term_offset(db, t.ty, predicate.clone(), offset)),
            ExpressionT::Apply(t) => find_in_term_offset(db, t.function, predicate.clone(), offset)
                .or_else(|| find_in_term_offset(db, t.argument, predicate.clone(), offset)),
            ExpressionT::Lifespan(t) => find_in_term_offset(db, t.ty, predicate, offset),
            ExpressionT::Sort(_)
            | ExpressionT::Region
            | ExpressionT::StaticRegion
            | ExpressionT::Metavariable(_)
            | ExpressionT::LocalConstant(_) => None,
        }
    }
}

/// Returns the first local constant or metavariable in the given term.
#[must_use]
#[salsa::tracked]
pub fn first_local_or_metavariable(db: &dyn Db, t: Term) -> Option<Term> {
    find_in_term(db, t, |inner, _offset| {
        matches!(
            inner.value(db),
            ExpressionT::LocalConstant(_) | ExpressionT::Metavariable(_)
        )
    })
}

/// Traverses the term tree and finds terms matching the provided predicate.
/// If any return `true`, the first such term is returned.
/// The tree is traversed depth first.
fn for_each_term(db: &dyn Db, t: Term, func: impl FnMut(Term, DeBruijnOffset)) {
    let cell = RefCell::new(func);
    find_in_term(db, t, |inner, offset| {
        cell.borrow_mut()(inner, offset);
        false
    });
}

/// Gets the maximum height of reducible definitions contained inside this term.
#[must_use]
#[salsa::tracked]
pub fn get_max_height(db: &dyn Db, t: Term) -> DefinitionHeight {
    let mut height = 0;
    for_each_term(db, t, |inner, _offset| {
        if let ExpressionT::Inst(inst) = inner.value(db) {
            if let Some(inner_height) = definition_height(db, inst) {
                height = std::cmp::max(height, inner_height);
            }
        }
    });
    height
}

/// Finds the first instance of the given constant in the term.
#[must_use]
pub fn find_constant<'db>(
    db: &'db dyn Db,
    t: Term,
    name: &QualifiedName<()>,
) -> Option<&'db Inst<()>> {
    find_in_term(db, t, |inner, _offset| {
        if let ExpressionT::Inst(inst) = inner.value(db) {
            inst.name == *name
        } else {
            false
        }
    })
    .map(|term| {
        if let ExpressionT::Inst(inst) = term.value(db) {
            inst
        } else {
            unreachable!()
        }
    })
}

/// Instantiate the first bound variable with the given substitution.
/// This will subtract one from all higher de Bruijn indices.
#[must_use]
#[salsa::tracked]
pub fn instantiate(db: &dyn Db, t: Term, substitution: Term) -> Term {
    replace_in_term(db, t, |t, offset| {
        match t.value(db) {
            ExpressionT::Local(Local { index }) => {
                match index.cmp(&(DeBruijnIndex::zero() + offset)) {
                    Ordering::Less => {
                        // The variable is bound and has index lower than the offset, so we don't change it.
                        ReplaceResult::Skip
                    }
                    Ordering::Equal => {
                        // The variable is the smallest free de Bruijn index.
                        // It is exactly the one we need to substitute.
                        ReplaceResult::ReplaceWith(lift_free_vars(db, substitution, offset))
                    }
                    Ordering::Greater => {
                        // This de Bruijn index must be decremented, since we just
                        // instantiated a variable below it.
                        ReplaceResult::ReplaceWith(Term::new(
                            db,
                            ExpressionT::Local(Local {
                                index: index.pred(),
                            }),
                        ))
                    }
                }
            }
            _ => ReplaceResult::Skip,
        }
    })
}

/// Replace the given list of universe parameters with the given arguments.
/// The lists must be the same length.
#[must_use]
pub fn instantiate_universe_parameters(
    db: &dyn Db,
    t: Term,
    universe_params: &[Name<()>],
    universe_arguments: &[Universe<()>],
) -> Term {
    replace_in_term(db, t, |t, _offset| match t.value(db) {
        ExpressionT::Inst(inst) => {
            let mut inst = inst.clone();
            for univ in &mut inst.universes {
                for (param, replacement) in universe_params.iter().zip(universe_arguments) {
                    instantiate_universe(univ, &UniverseVariable(*param), replacement);
                }
            }
            ReplaceResult::ReplaceWith(Term::new(db, ExpressionT::Inst(inst)))
        }
        ExpressionT::Sort(sort) => {
            let mut sort = sort.clone();
            for (param, replacement) in universe_params.iter().zip(universe_arguments) {
                instantiate_universe(&mut sort.0, &UniverseVariable(*param), replacement);
            }
            ReplaceResult::ReplaceWith(Term::new(db, ExpressionT::Sort(sort)))
        }
        _ => ReplaceResult::Skip,
    })
}

/// Increase the de Bruijn indices of free variables by a certain offset.
#[must_use]
pub fn lift_free_vars(db: &dyn Db, t: Term, shift: DeBruijnOffset) -> Term {
    replace_in_term(db, t, |t, offset| {
        match t.value(db) {
            ExpressionT::Local(Local { index }) => {
                if *index >= DeBruijnIndex::zero() + offset {
                    // The variable is free.
                    ReplaceResult::ReplaceWith(Term::new(
                        db,
                        ExpressionT::Local(Local {
                            index: *index + shift,
                        }),
                    ))
                } else {
                    ReplaceResult::Skip
                }
            }
            _ => ReplaceResult::Skip,
        }
    })
}

/// Create a lambda or pi binder where the parameter is the given local constant.
#[must_use]
pub fn abstract_binder(
    db: &dyn Db,
    local: LocalConstant<(), Term>,
    return_type: Term,
) -> Binder<(), Term> {
    let return_type = replace_in_term(db, return_type, |t, offset| match t.value(db) {
        ExpressionT::LocalConstant(inner_local) => {
            if *inner_local == local {
                ReplaceResult::ReplaceWith(Term::new(
                    db,
                    ExpressionT::Local(Local {
                        index: DeBruijnIndex::zero() + offset,
                    }),
                ))
            } else {
                ReplaceResult::Skip
            }
        }
        _ => ReplaceResult::Skip,
    });

    Binder {
        structure: local.structure,
        result: return_type,
    }
}

/// Replace the given local constant with this term.
#[must_use]
pub fn replace_local(
    db: &dyn Db,
    t: Term,
    local: &LocalConstant<(), Term>,
    replacement: Term,
) -> Term {
    replace_in_term(db, t, |t, offset| {
        if let ExpressionT::LocalConstant(inner) = t.value(db)
            && inner.metavariable.index == local.metavariable.index {
            // We should replace this local variable.
            ReplaceResult::ReplaceWith(lift_free_vars(db, replacement, offset))
        } else {
            ReplaceResult::Skip
        }
    })
}

#[must_use]
pub fn replace_universe_variable(
    db: &dyn Db,
    t: Term,
    var: &UniverseVariable<()>,
    replacement: &Universe<()>,
) -> Term {
    replace_in_term(db, t, |t, _offset| match t.value(db) {
        ExpressionT::Inst(inst) => {
            let mut inst = inst.clone();
            for u in &mut inst.universes {
                instantiate_universe(u, var, replacement);
            }
            ReplaceResult::ReplaceWith(Term::new(db, ExpressionT::Inst(inst)))
        }
        ExpressionT::Sort(sort) => {
            let mut sort = sort.clone();
            instantiate_universe(&mut sort.0, var, replacement);
            ReplaceResult::ReplaceWith(Term::new(db, ExpressionT::Sort(sort)))
        }
        ExpressionT::Metavariable(mut meta) => {
            meta.ty = replace_universe_variable(db, meta.ty, var, replacement);
            ReplaceResult::ReplaceWith(Term::new(db, ExpressionT::Metavariable(meta)))
        }
        ExpressionT::LocalConstant(mut local) => {
            local.metavariable.ty =
                replace_universe_variable(db, local.metavariable.ty, var, replacement);
            ReplaceResult::ReplaceWith(Term::new(db, ExpressionT::LocalConstant(local)))
        }
        _ => ReplaceResult::Skip,
    })
}
