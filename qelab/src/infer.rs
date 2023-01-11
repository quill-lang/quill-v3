//! Infers types of terms that may contain metavariables.
//! When compared to [`Expression::infer_type`], inference results from this module
//! also return a set of constraints on the metavariables.

use fkernel::{
    basic::Provenance,
    expr::*,
    get_definition,
    result::Dr,
    typeck::*,
    universe::{Universe, UniverseContents, UniverseImpredicativeMax, UniverseSucc},
};

use crate::{
    constraint::{Justification, UnificationConstraint},
    elaborator::Elaborator,
};

pub struct ConstrainedExpression<'cache> {
    pub expr: Expression<'cache>,
    pub constraints: Vec<UnificationConstraint<'cache>>,
}

impl<'cache> ConstrainedExpression<'cache> {
    pub fn new(ty: Expression<'cache>) -> Self {
        Self {
            expr: ty,
            constraints: Vec::new(),
        }
    }

    pub fn with_constraints(
        mut self,
        constraints: impl IntoIterator<Item = UnificationConstraint<'cache>>,
    ) -> Self {
        self.constraints.extend(constraints);
        self
    }
}

impl<'a, 'cache> Elaborator<'a, 'cache> {
    /// Infers the type of `expr`, an expression which may contain metavariables.
    /// We also return a set of constraints that must be satisfied for `expr` to be type correct.
    /// If no constraints could be added to make `expr` type correct, this function returns a failed [`Dr`].
    ///
    /// We try to copy the provenance from the input expression where possible.
    ///
    /// This function tries to be a bit more "clever" than the usual [`Expression::infer_type`],
    /// which doesn't know how to handle uncertainty.
    pub fn infer_type_with_constraints(
        &self,
        expr: Expression<'cache>,
    ) -> Dr<ConstrainedExpression<'cache>> {
        if expr.has_free_variables(self.cache()) {
            todo!()
        } else {
            self.infer_type_with_constraints_core(expr)
        }
    }

    /// Assumes that `expr` has no free variables.
    fn infer_type_with_constraints_core(
        &self,
        expr: Expression<'cache>,
    ) -> Dr<ConstrainedExpression<'cache>> {
        match expr.value(self.cache()) {
            ExpressionT::Local(_) => todo!(),
            ExpressionT::Borrow(borrow) => {
                self.infer_type_borrow(expr.provenance(self.cache()), borrow)
            }
            ExpressionT::Dereference(deref) => self.infer_type_deref(deref),
            ExpressionT::Delta(delta) => self.infer_type_delta(delta),
            ExpressionT::Inst(inst) => self.infer_type_inst(inst),
            ExpressionT::Let(let_expr) => self.infer_type_let(let_expr),
            ExpressionT::Lambda(lambda) => self.infer_type_lambda(lambda),
            ExpressionT::Pi(pi) => self.infer_type_pi(pi),
            ExpressionT::RegionLambda(_) => todo!(),
            ExpressionT::RegionPi(_) => todo!(),
            ExpressionT::Apply(apply) => self.infer_type_apply(apply),
            ExpressionT::Intro(_) => todo!(),
            ExpressionT::Match(_) => todo!(),
            ExpressionT::Fix(_) => todo!(),
            ExpressionT::Sort(sort) => self.infer_type_sort(sort),
            ExpressionT::Region | ExpressionT::RegionT => {
                Dr::ok(ConstrainedExpression::new(Expression::new(
                    self.cache(),
                    expr.provenance(self.cache()),
                    ExpressionT::RegionT,
                )))
            }
            ExpressionT::StaticRegion => Dr::ok(ConstrainedExpression::new(Expression::new(
                self.cache(),
                expr.provenance(self.cache()),
                ExpressionT::Region,
            ))),
            ExpressionT::Lifespan(_) => todo!(),
            ExpressionT::Hole(hole) => Dr::ok(ConstrainedExpression::new(hole.ty)),
            ExpressionT::RegionHole(hole) => {
                if hole.ty.value(self.cache()) == ExpressionT::Region {
                    Dr::ok(ConstrainedExpression::new(hole.ty))
                } else {
                    todo!()
                }
            }
            ExpressionT::LocalConstant(local) => {
                Dr::ok(ConstrainedExpression::new(local.structure.bound.ty))
            }
        }
    }

    fn infer_type_borrow(
        &self,
        provenance: Provenance,
        borrow: Borrow<Expression<'cache>>,
    ) -> Dr<ConstrainedExpression<'cache>> {
        self.infer_type_with_constraints_core(borrow.value)
            .bind(|mut value| {
                self.infer_type_with_constraints_core(borrow.region)
                    .map(|region_ty| {
                        value.constraints.extend(region_ty.constraints);
                        value.constraints.push(UnificationConstraint {
                            expected: Expression::region(self.cache()),
                            actual: region_ty.expr,
                            justification: Justification::Borrow,
                        });
                        ConstrainedExpression {
                            expr: Expression::new(
                                self.cache(),
                                provenance,
                                ExpressionT::Delta(Delta {
                                    region: borrow.region,
                                    ty: value.expr,
                                }),
                            ),
                            constraints: value.constraints,
                        }
                    })
            })
    }

    fn infer_type_deref(
        &self,
        deref: Dereference<Expression<'cache>>,
    ) -> Dr<ConstrainedExpression<'cache>> {
        self.infer_type_with_constraints_core(deref.value)
            .bind(|value| {
                if let ExpressionT::Delta(delta) = value.expr.value(self.cache()) {
                    Dr::ok(ConstrainedExpression {
                        expr: delta.ty,
                        constraints: value.constraints,
                    })
                } else {
                    todo!()
                }
            })
    }

    fn infer_type_delta(
        &self,
        delta: Delta<Expression<'cache>>,
    ) -> Dr<ConstrainedExpression<'cache>> {
        self.infer_type_with_constraints_core(delta.ty)
            .bind(|delta_ty| {
                as_sort(self.cache(), delta_ty.expr)
                    .expect("parameter to delta type should be a type");
                Dr::ok(delta_ty)
            })
    }

    fn infer_type_inst(&self, inst: Inst) -> Dr<ConstrainedExpression<'cache>> {
        let path = inst.name.to_path(self.db());
        match get_definition(self.db(), path).value() {
            Some(def) => {
                // `Inst` expressions should already have the correct number of universe parameters.
                Dr::ok(ConstrainedExpression::new(
                    def.contents
                        .ty
                        .from_heap(self.cache())
                        .instantiate_universe_parameters(
                            self.cache(),
                            &def.contents.universe_params,
                            &inst.universes,
                        ),
                ))
            }
            None => todo!(),
        }
    }

    fn infer_type_let(
        &self,
        let_expr: Let<Expression<'cache>>,
    ) -> Dr<ConstrainedExpression<'cache>> {
        self.infer_type_with_constraints_core(let_expr.bound.ty)
            .bind(|let_type_type| {
                as_sort(self.cache(), let_type_type.expr).expect("deal with this later");
                // Infer the type of the value to substitute.
                self.infer_type_with_constraints_core(let_expr.to_assign)
                    .bind(|to_assign_ty| {
                        // The value that we assign must have type definitionally equal to the type to assign.
                        self.infer_type_with_constraints_core(
                            let_expr.body.instantiate(self.cache(), let_expr.to_assign),
                        )
                        .map(|body_ty| ConstrainedExpression {
                            expr: body_ty.expr,
                            constraints: let_type_type
                                .constraints
                                .into_iter()
                                .chain(to_assign_ty.constraints)
                                .chain(body_ty.constraints)
                                .collect(),
                        })
                    })
            })
    }

    fn infer_type_lambda(
        &self,
        lambda: Binder<Expression<'cache>>,
    ) -> Dr<ConstrainedExpression<'cache>> {
        self.infer_type_with_constraints_core(lambda.structure.bound.ty)
            .bind(|mut argument_type_type| {
                // Infer the return type of the lambda by first instantiating the parameter then inferring the resulting type.
                let new_local = self.cache().gen_local(lambda.structure);
                let body = lambda.result.instantiate(
                    self.cache(),
                    Expression::new(
                        self.cache(),
                        Provenance::Synthetic,
                        ExpressionT::LocalConstant(new_local),
                    ),
                );
                self.infer_type_with_constraints_core(body)
                    .map(|return_type| {
                        let expr = Expression::new(
                            self.cache(),
                            Provenance::Synthetic,
                            ExpressionT::Pi(
                                return_type.expr.abstract_binder(self.cache(), new_local),
                            ),
                        );
                        argument_type_type
                            .constraints
                            .extend(return_type.constraints);
                        ConstrainedExpression {
                            expr,
                            constraints: argument_type_type.constraints,
                        }
                    })
            })
    }

    fn infer_type_pi(&self, pi: Binder<Expression<'cache>>) -> Dr<ConstrainedExpression<'cache>> {
        // The argument type must be a type.
        self.infer_type_with_constraints_core(pi.structure.bound.ty)
            .bind(|mut parameter_type| {
                let domain_type =
                    as_sort(self.cache(), parameter_type.expr).expect("deal with this later");
                // Infer the return type of the pi by first instantiating the parameter then inferring the resulting type.
                let body = pi.result.instantiate(
                    self.cache(),
                    Expression::new(
                        self.cache(),
                        Provenance::Synthetic,
                        ExpressionT::LocalConstant(self.cache().gen_local(pi.structure)),
                    ),
                );
                self.infer_type_with_constraints_core(body)
                    .map(|return_type| {
                        let return_type_sort =
                            as_sort(self.cache(), return_type.expr).expect("deal with this later");
                        let expr = Expression::new(
                            self.cache(),
                            Provenance::Synthetic,
                            ExpressionT::Sort(Sort(Universe::new(
                                Provenance::Synthetic,
                                UniverseContents::UniverseImpredicativeMax(
                                    UniverseImpredicativeMax {
                                        left: Box::new(domain_type.0),
                                        right: Box::new(return_type_sort.0),
                                    },
                                ),
                            ))),
                        );
                        parameter_type.constraints.extend(return_type.constraints);
                        ConstrainedExpression {
                            expr,
                            constraints: parameter_type.constraints,
                        }
                    })
            })
    }

    fn infer_type_apply(
        &self,
        apply: Apply<Expression<'cache>>,
    ) -> Dr<ConstrainedExpression<'cache>> {
        self.infer_type_with_constraints_core(apply.function)
            .bind(|function_type| {
                // If the function type was a delta type, we are trying to call the function from behind a borrow.
                // Otherwise, we assume we are trying to call it normally.
                match as_delta(self.cache(), function_type.expr) {
                    Ok(_) => {
                        // This was a function called from behind a borrow.
                        todo!()
                    }
                    Err(_) => {
                        // Assume that we are trying to call the function normally.
                        self.ensure_pi(function_type.expr)
                            .bind(|(pi, constraints)| {
                                self.infer_type_with_constraints_core(apply.argument).map(
                                    |argument_type| ConstrainedExpression {
                                        expr: pi.result.instantiate(self.cache(), apply.argument),
                                        constraints: function_type
                                            .constraints
                                            .into_iter()
                                            .chain(constraints)
                                            .chain(argument_type.constraints)
                                            .chain(std::iter::once(UnificationConstraint {
                                                expected: pi.structure.bound.ty,
                                                actual: argument_type.expr,
                                                justification: Justification::Apply { apply },
                                            }))
                                            .collect(),
                                    },
                                )
                            })
                    }
                }
            })
    }

    fn infer_type_sort(&self, sort: Sort) -> Dr<ConstrainedExpression<'cache>> {
        // The type of any sort, valid or not, is just the sort one universe higher.
        Dr::ok(ConstrainedExpression::new(Expression::new(
            self.cache(),
            Provenance::Synthetic,
            ExpressionT::Sort(Sort(Universe::new(
                sort.0.provenance,
                UniverseContents::UniverseSucc(UniverseSucc(Box::new(sort.0))),
            ))),
        )))
    }

    /// Ensures that `expr` is a [`ExpressionT::Pi`].
    /// If it was not exactly such an expression, we create a new pi type and
    /// add the constraint that `expr` unifies with it.
    fn ensure_pi(
        &self,
        expr: Expression<'cache>,
    ) -> Dr<(
        Binder<Expression<'cache>>,
        Vec<UnificationConstraint<'cache>>,
    )> {
        match as_pi(self.cache(), expr) {
            Ok(pi) => Dr::ok((pi, Vec::new())),
            Err(_) => todo!(),
        }
    }
}
