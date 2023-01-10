//! Utilities for traversing the expression tree for things like find-and-replace operations.

use std::{cell::RefCell, cmp::Ordering};

use fcommon::Str;

use crate::{
    basic::{DeBruijnIndex, DeBruijnOffset, Name, QualifiedName, WithProvenance},
    expr::*,
    multiplicity::ParameterOwnership,
    typeck::DefinitionHeight,
    universe::{Universe, UniverseVariable},
};

pub enum ReplaceResult<'cache> {
    /// The expression should not be replaced.
    Skip,
    /// The expression should be replaced with the given value.e.
    ReplaceWith(Expression<'cache>),
}

impl<'cache> Expression<'cache> {
    pub fn subexpressions(self, cache: &ExpressionCache<'cache>) -> Vec<Self> {
        match self.value(cache) {
            ExpressionT::Local(_) => Vec::new(),
            ExpressionT::Borrow(e) => vec![e.region, e.value],
            ExpressionT::Dereference(e) => vec![e.value],
            ExpressionT::Delta(e) => vec![e.region, e.ty],
            ExpressionT::Inst(_) => Vec::new(),
            ExpressionT::Let(e) => vec![e.bound.ty, e.to_assign, e.body],
            ExpressionT::Lambda(e) | ExpressionT::Pi(e) => {
                vec![e.structure.bound.ty, e.structure.region, e.result]
            }
            ExpressionT::RegionLambda(e) | ExpressionT::RegionPi(e) => vec![e.body],
            ExpressionT::Apply(e) => vec![e.function, e.argument],
            ExpressionT::Intro(e) => e.parameters,
            ExpressionT::Match(e) => std::iter::once(e.major_premise)
                .chain(std::iter::once(e.motive))
                .chain(e.minor_premises.iter().map(|premise| premise.result))
                .collect(),
            ExpressionT::Fix(e) => vec![e.argument, e.fixpoint.ty, e.body],
            ExpressionT::Sort(_)
            | ExpressionT::Region
            | ExpressionT::RegionT
            | ExpressionT::StaticRegion
            | ExpressionT::Lifespan(_) => Vec::new(),
            ExpressionT::Hole(mut e) | ExpressionT::RegionHole(mut e) => {
                e.args.push(e.ty);
                e.args
            }
            ExpressionT::LocalConstant(e) => vec![e.structure.bound.ty],
        }
    }

    /// Traverses the expression tree and finds expressions matching the provided replacement function.
    /// If any matched, the replacement function generates the value to replace the found value with.
    /// The provided [`DeBruijnOffset`] gives the amount of binders the [`Expr`] argument is currently under.
    #[must_use]
    pub fn replace_in_expression(
        self,
        cache: &ExpressionCache<'cache>,
        replace_fn: &impl Fn(Self, DeBruijnOffset) -> ReplaceResult<'cache>,
    ) -> Self {
        self.replace_in_expression_offset(cache, replace_fn, DeBruijnOffset::zero())
    }

    /// Like [`replace_in_expression`] but keeps track of sub-expression de Bruijn index offsets.
    #[must_use]
    fn replace_in_expression_offset(
        self,
        cache: &ExpressionCache<'cache>,
        replace_fn: &impl Fn(Self, DeBruijnOffset) -> ReplaceResult<'cache>,
        offset: DeBruijnOffset,
    ) -> Self {
        // Invoke the replacement function.
        match replace_fn(self, offset) {
            ReplaceResult::Skip => {
                // Traverse the sub-expressions of `self`.
                match self.value(cache) {
                    ExpressionT::Local(_) | ExpressionT::Inst(_) => self,
                    ExpressionT::Borrow(e) => Self::new(
                        cache,
                        self.provenance(cache),
                        ExpressionT::Borrow(Borrow {
                            region: e
                                .region
                                .replace_in_expression_offset(cache, replace_fn, offset),
                            value: e
                                .value
                                .replace_in_expression_offset(cache, replace_fn, offset),
                        }),
                    ),
                    ExpressionT::Dereference(e) => Self::new(
                        cache,
                        self.provenance(cache),
                        ExpressionT::Dereference(Dereference {
                            value: e
                                .value
                                .replace_in_expression_offset(cache, replace_fn, offset),
                        }),
                    ),
                    ExpressionT::Delta(e) => Self::new(
                        cache,
                        self.provenance(cache),
                        ExpressionT::Delta(Delta {
                            region: e
                                .region
                                .replace_in_expression_offset(cache, replace_fn, offset),
                            ty: e.ty.replace_in_expression_offset(cache, replace_fn, offset),
                        }),
                    ),
                    ExpressionT::Let(e) => Self::new(
                        cache,
                        self.provenance(cache),
                        ExpressionT::Let(Let {
                            bound: BoundVariable {
                                ty: e
                                    .bound
                                    .ty
                                    .replace_in_expression_offset(cache, replace_fn, offset),
                                ..e.bound
                            },
                            to_assign: e
                                .to_assign
                                .replace_in_expression_offset(cache, replace_fn, offset),
                            body: e.body.replace_in_expression_offset(
                                cache,
                                replace_fn,
                                offset.succ(),
                            ),
                        }),
                    ),
                    ExpressionT::Lambda(e) => {
                        Self::new(
                            cache,
                            self.provenance(cache),
                            ExpressionT::Lambda(Binder {
                                structure: BinderStructure {
                                    bound: BoundVariable {
                                        ty: e.structure.bound.ty.replace_in_expression_offset(
                                            cache, replace_fn, offset,
                                        ),
                                        ..e.structure.bound
                                    },
                                    region: e
                                        .structure
                                        .region
                                        .replace_in_expression_offset(cache, replace_fn, offset),
                                    ..e.structure
                                },
                                result: e.result.replace_in_expression_offset(
                                    cache,
                                    replace_fn,
                                    offset.succ(),
                                ),
                            }),
                        )
                    }
                    ExpressionT::Pi(e) => {
                        Self::new(
                            cache,
                            self.provenance(cache),
                            ExpressionT::Pi(Binder {
                                structure: BinderStructure {
                                    bound: BoundVariable {
                                        ty: e.structure.bound.ty.replace_in_expression_offset(
                                            cache, replace_fn, offset,
                                        ),
                                        ..e.structure.bound
                                    },
                                    region: e
                                        .structure
                                        .region
                                        .replace_in_expression_offset(cache, replace_fn, offset),
                                    ..e.structure
                                },
                                result: e.result.replace_in_expression_offset(
                                    cache,
                                    replace_fn,
                                    offset.succ(),
                                ),
                            }),
                        )
                    }
                    ExpressionT::RegionLambda(e) => Self::new(
                        cache,
                        self.provenance(cache),
                        ExpressionT::RegionLambda(RegionBinder {
                            region_name: e.region_name,
                            body: e.body.replace_in_expression_offset(
                                cache,
                                replace_fn,
                                offset.succ(),
                            ),
                        }),
                    ),
                    ExpressionT::RegionPi(e) => Self::new(
                        cache,
                        self.provenance(cache),
                        ExpressionT::RegionPi(RegionBinder {
                            region_name: e.region_name,
                            body: e.body.replace_in_expression_offset(
                                cache,
                                replace_fn,
                                offset.succ(),
                            ),
                        }),
                    ),
                    ExpressionT::Apply(e) => Self::new(
                        cache,
                        self.provenance(cache),
                        ExpressionT::Apply(Apply {
                            function: e
                                .function
                                .replace_in_expression_offset(cache, replace_fn, offset),
                            argument: e
                                .argument
                                .replace_in_expression_offset(cache, replace_fn, offset),
                        }),
                    ),
                    ExpressionT::Intro(e) => Self::new(
                        cache,
                        self.provenance(cache),
                        ExpressionT::Intro(Intro {
                            inductive: e.inductive.clone(),
                            universes: e.universes.clone(),
                            variant: e.variant,
                            parameters: e
                                .parameters
                                .iter()
                                .map(|e| e.replace_in_expression_offset(cache, replace_fn, offset))
                                .collect(),
                        }),
                    ),
                    ExpressionT::Match(e) => Self::new(
                        cache,
                        self.provenance(cache),
                        ExpressionT::Match(Match {
                            major_premise: e
                                .major_premise
                                .replace_in_expression_offset(cache, replace_fn, offset),
                            index_params: e.index_params,
                            motive: e.motive.replace_in_expression_offset(
                                cache,
                                replace_fn,
                                offset.succ() + DeBruijnOffset::new(e.index_params),
                            ),
                            minor_premises: e
                                .minor_premises
                                .iter()
                                .map(|premise| MinorPremise {
                                    variant: premise.variant,
                                    fields: premise.fields,
                                    result: premise.result.replace_in_expression_offset(
                                        cache,
                                        replace_fn,
                                        offset + DeBruijnOffset::new(premise.fields),
                                    ),
                                })
                                .collect(),
                        }),
                    ),
                    ExpressionT::Fix(e) => Self::new(
                        cache,
                        self.provenance(cache),
                        ExpressionT::Fix(Fix {
                            argument: e
                                .argument
                                .replace_in_expression_offset(cache, replace_fn, offset),
                            argument_name: e.argument_name,
                            fixpoint: BoundVariable {
                                ty: e.fixpoint.ty.replace_in_expression_offset(
                                    cache,
                                    replace_fn,
                                    offset.succ(),
                                ),
                                ..e.fixpoint
                            },
                            body: e.body.replace_in_expression_offset(
                                cache,
                                replace_fn,
                                offset.succ().succ(),
                            ),
                        }),
                    ),
                    ExpressionT::Lifespan(e) => Self::new(
                        cache,
                        self.provenance(cache),
                        ExpressionT::Lifespan(Lifespan {
                            ty: e.ty.replace_in_expression_offset(cache, replace_fn, offset),
                        }),
                    ),
                    ExpressionT::Sort(_)
                    | ExpressionT::Region
                    | ExpressionT::RegionT
                    | ExpressionT::StaticRegion => self,
                    ExpressionT::Hole(e) => Self::new(
                        cache,
                        self.provenance(cache),
                        ExpressionT::Hole(Hole {
                            id: e.id,
                            args: e
                                .args
                                .iter()
                                .map(|e| e.replace_in_expression_offset(cache, replace_fn, offset))
                                .collect(),
                            ty: e.ty.replace_in_expression_offset(
                                cache,
                                replace_fn,
                                offset + DeBruijnOffset::new(e.args.len() as u32),
                            ),
                        }),
                    ),
                    ExpressionT::RegionHole(e) => Self::new(
                        cache,
                        self.provenance(cache),
                        ExpressionT::RegionHole(Hole {
                            id: e.id,
                            args: e
                                .args
                                .iter()
                                .map(|e| e.replace_in_expression_offset(cache, replace_fn, offset))
                                .collect(),
                            ty: e.ty.replace_in_expression_offset(
                                cache,
                                replace_fn,
                                offset + DeBruijnOffset::new(e.args.len() as u32),
                            ),
                        }),
                    ),
                    ExpressionT::LocalConstant(e) => {
                        Self::new(
                            cache,
                            self.provenance(cache),
                            ExpressionT::LocalConstant(LocalConstant {
                                id: e.id,
                                structure: BinderStructure {
                                    bound: BoundVariable {
                                        ty: e.structure.bound.ty.replace_in_expression_offset(
                                            cache, replace_fn, offset,
                                        ),
                                        ..e.structure.bound
                                    },
                                    ..e.structure
                                },
                            }),
                        )
                    }
                }
            }
            ReplaceResult::ReplaceWith(replaced) => {
                // We replace `self` with the given value.
                // We don't try to traverse the sub-expressions of this returned value.
                replaced
            }
        }
    }

    /// Traverses the expression tree and finds expressions matching the provided predicate.
    /// If any return `true`, the first such expression is returned.
    /// The tree is traversed depth first.
    fn find_in_expression(
        self,
        cache: &ExpressionCache<'cache>,
        predicate: &impl Fn(Self, DeBruijnOffset) -> bool,
    ) -> Option<Self> {
        self.find_in_expression_offset(cache, predicate, DeBruijnOffset::zero())
    }

    /// Like [`find_in_expression`] but keeps track of sub-expression de Bruijn index offsets.
    fn find_in_expression_offset(
        self,
        cache: &ExpressionCache<'cache>,
        predicate: &impl Fn(Self, DeBruijnOffset) -> bool,
        offset: DeBruijnOffset,
    ) -> Option<Self> {
        if predicate(self, offset) {
            Some(self)
        } else {
            match self.value(cache) {
                ExpressionT::Local(_) | ExpressionT::Inst(_) => None,
                ExpressionT::Borrow(e) => e
                    .region
                    .find_in_expression_offset(cache, predicate, offset)
                    .or_else(|| e.value.find_in_expression_offset(cache, predicate, offset)),
                ExpressionT::Dereference(e) => {
                    e.value.find_in_expression_offset(cache, predicate, offset)
                }
                ExpressionT::Delta(e) => e
                    .region
                    .find_in_expression_offset(cache, predicate, offset)
                    .or_else(|| e.ty.find_in_expression_offset(cache, predicate, offset)),
                ExpressionT::Let(e) => e
                    .to_assign
                    .find_in_expression_offset(cache, predicate, offset)
                    .or_else(|| {
                        e.bound
                            .ty
                            .find_in_expression_offset(cache, predicate, offset)
                    })
                    .or_else(|| {
                        e.body
                            .find_in_expression_offset(cache, predicate, offset.succ())
                    }),
                ExpressionT::Lambda(e) | ExpressionT::Pi(e) => e
                    .structure
                    .region
                    .find_in_expression_offset(cache, predicate, offset)
                    .or_else(|| {
                        e.structure
                            .bound
                            .ty
                            .find_in_expression_offset(cache, predicate, offset)
                    })
                    .or_else(|| {
                        e.result
                            .find_in_expression_offset(cache, predicate, offset.succ())
                    }),
                ExpressionT::RegionLambda(e) | ExpressionT::RegionPi(e) => e
                    .body
                    .find_in_expression_offset(cache, predicate, offset.succ()),
                ExpressionT::Apply(e) => e
                    .function
                    .find_in_expression_offset(cache, predicate, offset)
                    .or_else(|| {
                        e.argument
                            .find_in_expression_offset(cache, predicate, offset)
                    }),
                ExpressionT::Intro(e) => e
                    .parameters
                    .iter()
                    .find_map(|e| e.find_in_expression_offset(cache, predicate, offset)),
                ExpressionT::Match(e) => e
                    .major_premise
                    .find_in_expression_offset(cache, predicate, offset)
                    .or_else(|| {
                        e.motive.find_in_expression_offset(
                            cache,
                            predicate,
                            offset.succ() + DeBruijnOffset::new(e.index_params),
                        )
                    })
                    .or_else(|| {
                        e.minor_premises.iter().find_map(|premise| {
                            premise.result.find_in_expression_offset(
                                cache,
                                predicate,
                                offset + DeBruijnOffset::new(premise.fields),
                            )
                        })
                    }),
                ExpressionT::Fix(e) => e
                    .argument
                    .find_in_expression_offset(cache, predicate, offset.succ())
                    .or_else(|| {
                        e.fixpoint.ty.find_in_expression_offset(
                            cache,
                            predicate,
                            offset.succ().succ(),
                        )
                    })
                    .or_else(|| e.body.find_in_expression_offset(cache, predicate, offset)),
                ExpressionT::Lifespan(e) => {
                    e.ty.find_in_expression_offset(cache, predicate, offset)
                }
                ExpressionT::Sort(_)
                | ExpressionT::Region
                | ExpressionT::RegionT
                | ExpressionT::StaticRegion
                | ExpressionT::LocalConstant(_) => None,
                ExpressionT::Hole(e) | ExpressionT::RegionHole(e) => e
                    .args
                    .iter()
                    .map(|e| e.find_in_expression_offset(cache, predicate, offset))
                    .next()
                    .unwrap_or_default()
                    .or_else(|| {
                        e.ty.find_in_expression_offset(
                            cache,
                            predicate,
                            offset + DeBruijnOffset::new(e.args.len() as u32),
                        )
                    }),
            }
        }
    }

    /// Returns the first local constant, hole, or region hole in the given expression.
    #[must_use]
    pub fn first_local_or_hole(self, cache: &ExpressionCache<'cache>) -> Option<Self> {
        self.find_in_expression(cache, &|inner, _offset| {
            matches!(
                inner.value(cache),
                ExpressionT::LocalConstant(_) | ExpressionT::Hole(_)
            )
        })
    }

    /// Returns true if the given hole or region hole appears in `self`.
    #[must_use]
    pub fn hole_occurs(self, cache: &ExpressionCache<'cache>, hole: HoleId) -> bool {
        self.find_in_expression(cache, &|inner, _offset| {
            if let ExpressionT::Hole(var) | ExpressionT::RegionHole(var) = inner.value(cache) {
                hole == var.id
            } else {
                false
            }
        })
        .is_some()
    }

    /// Returns true if the local variable given by `local` appears in `self`.
    #[must_use]
    pub fn local_is_bound(self, cache: &ExpressionCache<'cache>, local: DeBruijnIndex) -> bool {
        self.find_in_expression(cache, &|inner, offset| {
            if let ExpressionT::Local(bound) = inner.value(cache) {
                bound.index == local + offset
            } else {
                false
            }
        })
        .is_some()
    }

    /// Traverses the expression tree and calls the given function on each expression.
    /// The tree is traversed depth first.
    pub fn for_each_expression(
        self,
        cache: &ExpressionCache<'cache>,
        func: impl FnMut(Self, DeBruijnOffset),
    ) {
        let cell = RefCell::new(func);
        self.find_in_expression(cache, &|inner, offset| {
            cell.borrow_mut()(inner, offset);
            false
        });
    }

    /// Gets the maximum height of reducible definitions contained inside this expression.
    #[must_use]
    pub fn get_max_height(self, cache: &ExpressionCache<'cache>) -> DefinitionHeight {
        let mut height = 0;
        self.for_each_expression(cache, |inner, _offset| {
            if let ExpressionT::Inst(inst) = inner.value(cache) {
                if let Some(inner_height) = inst.definition_height(cache.db()) {
                    height = std::cmp::max(height, inner_height);
                }
            }
        });
        height
    }

    /// Finds the first instance of the given [`Inst`] in the expression.
    #[must_use]
    pub fn find_inst(self, cache: &ExpressionCache<'cache>, name: &QualifiedName) -> Option<Inst> {
        self.find_in_expression(cache, &|inner, _offset| {
            if let ExpressionT::Inst(inst) = inner.value(cache) {
                inst.name == *name
            } else {
                false
            }
        })
        .map(|expression| {
            if let ExpressionT::Inst(inst) = expression.value(cache) {
                inst
            } else {
                unreachable!()
            }
        })
    }

    /// Instantiate the first bound variable with the given substitution.
    /// This will subtract one from all higher de Bruijn indices.
    /// TODO: Cache the results.
    /// TODO: n-ary instantiation operation.
    #[must_use]
    pub fn instantiate(self, cache: &ExpressionCache<'cache>, substitution: Self) -> Self {
        self.replace_in_expression(cache, &|e, offset| {
            match e.value(cache) {
                ExpressionT::Local(Local { index }) => {
                    match index.cmp(&(DeBruijnIndex::zero() + offset)) {
                        Ordering::Less => {
                            // The variable is bound and has index lower than the offset, so we don't change it.
                            ReplaceResult::Skip
                        }
                        Ordering::Equal => {
                            // The variable is the smallest free de Bruijn index.
                            // It is exactly the one we need to substitute.
                            ReplaceResult::ReplaceWith(substitution.lift_free_vars(
                                cache,
                                DeBruijnOffset::zero(),
                                offset,
                            ))
                        }
                        Ordering::Greater => {
                            // This de Bruijn index must be decremented, since we just
                            // instantiated a variable below it.
                            ReplaceResult::ReplaceWith(Self::new(
                                cache,
                                e.provenance(cache),
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

    /// Gets the set of universe variables used in this expression, in the order they were used.
    pub fn universe_variables(self, cache: &ExpressionCache<'cache>) -> Vec<UniverseVariable> {
        let mut result = Vec::<UniverseVariable>::new();
        self.for_each_expression(cache, |expr, _offset| match expr.value(cache) {
            ExpressionT::Inst(inst) => {
                for univ in inst.universes {
                    for value in univ.universe_variables() {
                        if result
                            .iter()
                            .all(|univ| univ.0 .0.contents != value.0 .0.contents)
                        {
                            result.push(value);
                        }
                    }
                }
            }
            ExpressionT::Sort(sort) => {
                for value in sort.0.universe_variables() {
                    if result
                        .iter()
                        .all(|univ| univ.0 .0.contents != value.0 .0.contents)
                    {
                        result.push(value);
                    }
                }
            }
            _ => {}
        });
        result
    }

    /// Replace the given list of universe parameters with the given arguments.
    /// The lists must be the same length.
    #[must_use]
    pub fn instantiate_universe_parameters(
        self,
        cache: &ExpressionCache<'cache>,
        universe_params: &[Name],
        universe_arguments: &[Universe],
    ) -> Self {
        self.replace_in_expression(cache, &|e, _offset| match e.value(cache) {
            ExpressionT::Inst(inst) => {
                let mut inst = inst;
                for univ in &mut inst.universes {
                    for (param, replacement) in universe_params.iter().zip(universe_arguments) {
                        univ.instantiate_universe_variable(&UniverseVariable(*param), replacement);
                    }
                }
                ReplaceResult::ReplaceWith(Self::new(
                    cache,
                    e.provenance(cache),
                    ExpressionT::Inst(inst),
                ))
            }
            ExpressionT::Sort(sort) => {
                let mut sort = sort;
                for (param, replacement) in universe_params.iter().zip(universe_arguments) {
                    sort.0
                        .instantiate_universe_variable(&UniverseVariable(*param), replacement);
                }
                ReplaceResult::ReplaceWith(Self::new(
                    cache,
                    e.provenance(cache),
                    ExpressionT::Sort(sort),
                ))
            }
            _ => ReplaceResult::Skip,
        })
    }

    /// Increase the de Bruijn indices of free variables by a certain offset.
    /// Before the check, we increase the index of each expression by `bias`.
    #[must_use]
    pub fn lift_free_vars(
        self,
        cache: &ExpressionCache<'cache>,
        bias: DeBruijnOffset,
        shift: DeBruijnOffset,
    ) -> Self {
        self.replace_in_expression(cache, &|e, offset| {
            match e.value(cache) {
                ExpressionT::Local(Local { index }) => {
                    if index >= DeBruijnIndex::zero() + offset + bias {
                        // The variable is free.
                        ReplaceResult::ReplaceWith(Self::new(
                            cache,
                            e.provenance(cache),
                            ExpressionT::Local(Local {
                                index: index + shift,
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
    /// Invoke this with a closed expression.
    #[must_use]
    pub fn abstract_binder(
        self,
        cache: &ExpressionCache<'cache>,
        local: LocalConstant<Self>,
    ) -> Binder<Self> {
        let return_type = self.replace_in_expression(cache, &|e, offset| match e.value(cache) {
            ExpressionT::LocalConstant(inner_local) => {
                if inner_local == local {
                    ReplaceResult::ReplaceWith(Self::new(
                        cache,
                        e.provenance(cache),
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

    /// Create a region binder where the parameter is the given local constant.
    /// Invoke this with a closed expression.
    #[must_use]
    pub fn abstract_region_binder(
        self,
        cache: &ExpressionCache<'cache>,
        local: LocalConstant<Self>,
    ) -> RegionBinder<Self> {
        let return_type = self.replace_in_expression(cache, &|e, offset| match e.value(cache) {
            ExpressionT::LocalConstant(inner_local) => {
                if inner_local == local {
                    ReplaceResult::ReplaceWith(Self::new(
                        cache,
                        e.provenance(cache),
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

        RegionBinder {
            region_name: local.structure.bound.name,
            body: return_type,
        }
    }

    /// Replaces every instance of the given hole inside this expression with a replacement.
    #[must_use]
    pub fn fill_hole(self, cache: &ExpressionCache<'cache>, id: HoleId, replacement: Self) -> Self {
        self.replace_in_expression(cache, &|e, _offset| match e.value(cache) {
            ExpressionT::Hole(hole) | ExpressionT::RegionHole(hole) => {
                if hole.id == id {
                    // Each of the hole's arguments should be a de Bruijn index.
                    // We first replace each with a new local constant, perform the substitution, and then replace the locals with the correct indices.
                    let locals = hole
                        .args
                        .iter()
                        .map(|arg| {
                            (
                                *arg,
                                // Create a dummy local constant.
                                // This won't be used for anything, and the expression won't even be type checked.
                                cache.gen_local(BinderStructure {
                                    bound: BoundVariable {
                                        name: Name(WithProvenance::new_synthetic(Str::new(
                                            cache.db(),
                                            "".to_owned(),
                                        ))),
                                        ty: Expression::region(cache),
                                        ownership: ParameterOwnership::PZero,
                                    },
                                    binder_annotation: BinderAnnotation::Explicit,
                                    function_ownership: FunctionOwnership::Once,
                                    region: Expression::region(cache),
                                }),
                            )
                        })
                        .collect::<Vec<_>>();

                    let replacement_with_locals =
                        locals
                            .iter()
                            .rev()
                            .fold(replacement, |acc, (_,  constant)| {
                                acc.instantiate(
                                    cache,
                                    Expression::new(
                                        cache,
                                        e.provenance(cache),
                                        ExpressionT::LocalConstant(*constant),
                                    ),
                                )
                            });

                    ReplaceResult::ReplaceWith(replacement_with_locals.replace_in_expression(
                        cache,
                        &|expr, offset| {
                            if let ExpressionT::LocalConstant(constant) = expr.value(cache) {
                                for (replacement, found_constant) in &locals {
                                    if constant.id == found_constant.id {
                                        return ReplaceResult::ReplaceWith(replacement.lift_free_vars(cache, DeBruijnOffset::zero(), offset));
                                    }
                                }
                                ReplaceResult::Skip
                            } else {
                                ReplaceResult::Skip
                            }
                        },
                    ))
                } else {
                    ReplaceResult::Skip
                }
            }
            _ => ReplaceResult::Skip,
        })
    }

    /// Replace the given local constant with this expression.
    #[must_use]
    pub fn replace_local(
        self,
        cache: &ExpressionCache<'cache>,
        local: &LocalConstant<Self>,
        replacement: Self,
    ) -> Self {
        self.replace_in_expression(cache, &|e, offset| {
            if let ExpressionT::LocalConstant(inner) = e.value(cache)
            && inner.id == local.id {
            // We should replace this local variable.
            ReplaceResult::ReplaceWith(replacement.lift_free_vars(cache, DeBruijnOffset::zero(), offset))
        } else {
            ReplaceResult::Skip
        }
        })
    }

    #[must_use]
    pub fn replace_universe_variable(
        self,
        cache: &ExpressionCache<'cache>,
        var: &UniverseVariable,
        replacement: &Universe,
    ) -> Self {
        self.replace_in_expression(cache, &|e, _offset| match e.value(cache) {
            ExpressionT::Inst(inst) => {
                let mut inst = inst;
                for u in &mut inst.universes {
                    u.instantiate_universe_variable(var, replacement);
                }
                ReplaceResult::ReplaceWith(Self::new(
                    cache,
                    e.provenance(cache),
                    ExpressionT::Inst(inst),
                ))
            }
            ExpressionT::Sort(sort) => {
                let mut sort = sort;
                sort.0.instantiate_universe_variable(var, replacement);
                ReplaceResult::ReplaceWith(Self::new(
                    cache,
                    e.provenance(cache),
                    ExpressionT::Sort(sort),
                ))
            }
            _ => ReplaceResult::Skip,
        })
    }
}
