use fcommon::{Span, Spanned, Str};
use fkernel::{
    basic::{Name, QualifiedName, WithProvenance},
    expr::*,
    get_certified_definition,
    multiplicity::ParameterOwnership,
    result::Dr,
    universe::{Universe, UniverseContents, UniverseSucc, UniverseVariable},
};
use qparse::expr::*;

use crate::{
    constraint::Justification,
    elaborator::{Context, Elaborator},
};

impl<'a, 'cache> Elaborator<'a, 'cache> {
    /// Produces constraints that will be solved later.
    /// Returns a closed expression representing the parsed expression.
    ///
    /// When constraints are solved, substituting the solved constraints into the return value of this function
    /// produces the fully elaborated expression.
    ///
    /// TODO: Should we put the expected type in weak head normal form here?
    ///
    /// TODO: We currently duplicate some constraints due to calling `infer_type` too often.
    pub fn preprocess(
        &mut self,
        e: &PExpression,
        expected_type: Option<Expression<'cache>>,
        ctx: &Context<'cache>,
    ) -> Dr<Expression<'cache>> {
        #[cfg(feature = "elaborator_diagnostics")]
        if let Some(expected_type) = expected_type {
            tracing::trace!(
                "inferring {} with expected type {}",
                qformat::pexpression_to_document(self.db(), e).pretty_print(100),
                self.pretty_print(expected_type),
            );
        } else {
            tracing::trace!(
                "inferring {}",
                qformat::pexpression_to_document(self.db(), e).pretty_print(100),
            );
        }
        match e {
            PExpression::Variable {
                name,
                universe_ascription,
            } => self.preprocess_variable(expected_type, ctx, name, universe_ascription),
            PExpression::Borrow { borrow, value } => {
                self.preprocess_borrow(expected_type, ctx, *borrow, value)
            }
            PExpression::Dereference { deref, value } => {
                self.preprocess_deref(expected_type, ctx, *deref, value)
            }
            PExpression::Apply { function, argument } => {
                self.preprocess_apply(expected_type, ctx, function, argument)
            }
            PExpression::Intro { .. } => todo!(),
            PExpression::Match { .. } => todo!(),
            PExpression::Fix { .. } => todo!(),
            PExpression::Let {
                let_token,
                binders,
                body,
            } => self.preprocess_let(expected_type, ctx, *let_token, binders, body),
            PExpression::Lambda {
                fn_token,
                binders,
                result,
            } => self.preprocess_lambda(expected_type, ctx, *fn_token, binders, result),
            PExpression::FunctionType {
                binder,
                arrow_token,
                result,
            } => self.preprocess_function_type(expected_type, ctx, binder, *arrow_token, result),
            PExpression::Sort { span, universe } => {
                self.preprocess_sort(expected_type, *span, universe)
            }
            PExpression::Type { span, universe } => {
                self.preprocess_type(expected_type, *span, universe)
            }
            PExpression::Prop(_) => todo!(),
            PExpression::StaticRegion(_) => todo!(),
            PExpression::Region(_) => todo!(),
            PExpression::RegionT(_) => todo!(),
            PExpression::Inductive(_) => todo!(),
            PExpression::Metavariable { .. } => todo!(),
        }
    }

    fn preprocess_variable(
        &mut self,
        expected_type: Option<Expression<'cache>>,
        ctx: &Context<'cache>,
        name: &QualifiedName,
        universe_ascription: &Option<(Span, Vec<PUniverse>, Span)>,
    ) -> Dr<Expression<'cache>> {
        if name.len() == 1 {
            // This is a name with one segment.
            // Therefore, it could be a local variable.
            // Try to find the variable in the local context.
            if let Some(local) = ctx.get(*name[0]) {
                // The associated local variable exists.
                assert!(universe_ascription.is_none());
                return self
                    .infer_type(
                        Expression::new(
                            self.cache(),
                            name.0.provenance,
                            ExpressionT::LocalConstant(*local),
                        ),
                        ctx,
                        false,
                    )
                    .map(|result| {
                        if let Some(expected_type) = expected_type {
                            self.add_unification_constraint(
                                expected_type,
                                result.ty,
                                Justification::Variable,
                            );
                        }
                        result.expr
                    });
            }
        }

        // Search for a definition with this name.
        // For now, just search in the source file.
        // This implementation is very bad for cycle detection, but it works for now.
        let def_path = self
            .source()
            .path(self.db())
            .append(self.db(), name.iter().map(|name| **name));
        let def = get_certified_definition(self.db(), def_path);

        match def {
            Some(def) => {
                // We will instantiate this definition.
                assert!(universe_ascription.is_none(), "deal with this later");
                let expr = Expression::new(
                    self.cache(),
                    name.0.provenance,
                    ExpressionT::Inst(Inst {
                        name: QualifiedName(WithProvenance::new(
                            name.0.provenance,
                            self.source()
                                .path(self.db())
                                .segments(self.db())
                                .iter()
                                .map(|s| Name(WithProvenance::new(name.0.provenance, *s)))
                                .chain(name.iter().copied())
                                .collect(),
                        )),
                        universes: def
                            .def()
                            .universe_params
                            .iter()
                            .map(|_| self.universe_hole(name.0.provenance))
                            .collect(),
                    }),
                );
                self.infer_type(expr, ctx, false).map(|expr| expr.expr)
            }
            None => todo!(),
        }
    }

    fn preprocess_borrow(
        &mut self,
        expected_type: Option<Expression<'cache>>,
        ctx: &Context<'cache>,
        _borrow: Span,
        value: &PExpression,
    ) -> Dr<Expression<'cache>> {
        // Check that `expected_type` was a delta type.
        let delta_type = if let Some(expected_type) = expected_type {
            if let ExpressionT::Delta(delta) = expected_type.value(self.cache()) {
                Some(delta)
            } else {
                todo!()
            }
        } else {
            None
        };

        self.preprocess(value, delta_type.map(|delta| delta.ty), ctx)
            .bind(|value| {
                self.infer_type(value, ctx, false).map(|value| {
                    if let Some(delta) = delta_type {
                        Expression::new(
                            self.cache(),
                            value.ty.provenance(self.cache()),
                            ExpressionT::Borrow(Borrow {
                                region: delta.region,
                                value: value.expr,
                            }),
                        )
                    } else {
                        todo!()
                    }
                })
            })
    }

    fn preprocess_deref(
        &mut self,
        expected_type: Option<Expression<'cache>>,
        ctx: &Context<'cache>,
        deref: Span,
        value: &PExpression,
    ) -> Dr<Expression<'cache>> {
        let inner_expected_type = expected_type.map(|expected_type| {
            Expression::new(
                self.cache(),
                expected_type.provenance(self.cache()),
                ExpressionT::Delta(Delta {
                    region: self.hole(
                        ctx,
                        expected_type.provenance(self.cache()),
                        Some(Expression::region(self.cache())),
                    ),
                    ty: expected_type,
                }),
            )
        });

        self.preprocess(value, inner_expected_type, ctx)
            .bind(|result| {
                self.infer_type(result, ctx, false).map(|result| {
                    Expression::new(
                        self.cache(),
                        self.provenance(Span {
                            start: deref.start,
                            end: result.expr.span(self.cache()).end,
                        }),
                        ExpressionT::Dereference(Dereference { value: result.expr }),
                    )
                })
            })
    }

    fn preprocess_apply(
        &mut self,
        expected_type: Option<Expression<'cache>>,
        ctx: &Context<'cache>,
        function: &PExpression,
        argument: &PExpression,
    ) -> Dr<Expression<'cache>> {
        let span = Span {
            start: function.span().start,
            end: argument.span().end,
        };
        self.preprocess(function, None, ctx).bind(|function| {
            self.infer_type(function, ctx, true).bind(|function| {
                // The `function.ty` should be a function type.
                match function.ty.value(self.cache()) {
                    ExpressionT::Pi(pi) => {
                        // This invariant should be upheld by `infer_type`.
                        assert_eq!(pi.structure.binder_annotation, BinderAnnotation::Explicit);
                        self.preprocess(argument, Some(pi.structure.bound.ty), ctx)
                            .bind(|argument| {
                                self.infer_type(
                                    Expression::new(
                                        self.cache(),
                                        self.provenance(span),
                                        ExpressionT::Apply(Apply {
                                            function: function.expr,
                                            argument,
                                        }),
                                    ),
                                    ctx,
                                    false,
                                )
                                .map(|result| {
                                    if let Some(expected_type) = expected_type {
                                        // tracing::trace!(
                                        //     "inferred type of {} was {}",
                                        //     self.pretty_print(result.expr),
                                        //     self.pretty_print(result.ty)
                                        // );
                                        self.add_unification_constraint(
                                            expected_type,
                                            result.ty,
                                            Justification::ApplyPreprocess,
                                        );
                                    }
                                    result.expr
                                })
                            })
                    }
                    ExpressionT::RegionPi(_) => todo!(),
                    ExpressionT::Hole(_) => todo!(),
                    ExpressionT::RegionHole(_) => todo!(),
                    _ => todo!(),
                }
            })
        })
    }

    fn preprocess_let(
        &mut self,
        let_expected_type: Option<Expression<'cache>>,
        ctx: &Context<'cache>,
        let_token: Span,
        binders: &[PLetBinder],
        body: &PExpression,
    ) -> Dr<Expression<'cache>> {
        if let Some(binder) = binders.first() {
            let expected_type = if let Some(expected_type) = &binder.ty {
                self.preprocess(expected_type, None, ctx)
                    .bind(|ty| self.infer_type(ty, ctx, false))
                    .map(Some)
            } else {
                Dr::ok(None)
            };
            expected_type
                .bind(|expected_type| {
                    self.preprocess(
                        &binder.to_assign,
                        expected_type.map(|typed| typed.expr),
                        ctx,
                    )
                })
                .bind(|result| self.infer_type(result, ctx, false))
                .bind(|result| {
                    let local = self.cache().gen_local(BinderStructure {
                        bound: BoundVariable {
                            name: binder.name,
                            ty: result.ty,
                            ownership: ParameterOwnership::POwned,
                        },
                        binder_annotation: BinderAnnotation::Explicit,
                        function_ownership: FunctionOwnership::Once,
                        region: Expression::static_region(self.cache()),
                    });
                    let ctx = ctx.clone().with(local);

                    self.preprocess_let(let_expected_type, &ctx, let_token, &binders[1..], body)
                        .map(|body| {
                            Expression::new(
                                self.cache(),
                                self.provenance(let_token),
                                ExpressionT::Let(body.abstract_let(
                                    self.cache(),
                                    local,
                                    BoundVariable {
                                        name: binder.name,
                                        ty: result.ty,
                                        ownership: ParameterOwnership::POwned,
                                    },
                                    result.expr,
                                )),
                            )
                        })
                })
        } else {
            self.preprocess(body, let_expected_type, ctx)
        }
    }

    fn preprocess_lambda(
        &mut self,
        expected_type: Option<Expression<'cache>>,
        ctx: &Context<'cache>,
        fn_token: Span,
        binders: &[PLambdaBinder],
        result: &PExpression,
    ) -> Dr<Expression<'cache>> {
        if let Some(binder) = binders.first() {
            // If the expected type is a `Pi`, we can use some information.
            let expected_pi = expected_type.and_then(|expected_type| {
                if let ExpressionT::Pi(pi) = expected_type.value(self.cache()) {
                    Some(pi)
                } else {
                    None
                }
            });

            // If the type of this binder was explicitly given, process it.
            let binder_ty = match (
                &binder.ty,
                expected_pi.as_ref().map(|pi| pi.structure.bound.ty),
            ) {
                (None, None) => {
                    // The type of the bound variable is a hole.
                    Dr::ok(self.hole(ctx, binder.name.0.provenance, None))
                }
                (None, Some(expected_ty)) => {
                    // The type of the bound variable is known.
                    Dr::ok(expected_ty)
                }
                (Some(binder_ty), None) => {
                    // The type of the bound variable was given.
                    self.preprocess(binder_ty, None, ctx)
                }
                (Some(binder_ty), Some(expected_ty)) => {
                    // The type of the bound variable was given, and we already have an expression for it.
                    match expected_ty.infer_type(self.cache()) {
                        Ok(expected_ty_ty) => {
                            self.preprocess(binder_ty, Some(expected_ty_ty), ctx)
                                .map(|binder_ty| {
                                    // We need to add the constraint that `binder_ty = expected_ty`.
                                    self.add_unification_constraint(
                                        expected_ty,
                                        binder_ty,
                                        Justification::PreprocessLambda {
                                            binder: binder.name.0.provenance.span(),
                                        },
                                    );
                                    binder_ty
                                })
                        }
                        Err(_) => {
                            // The expression that we found for the type of the binder was not type correct.
                            todo!()
                        }
                    }
                }
            };

            binder_ty.bind(|binder_ty| {
                let bound_ownership = if let Some((ownership, _)) = binder.ownership {
                    ownership
                } else {
                    // TODO: Make a more intelligent choice based on `binder_ty`.
                    ParameterOwnership::POwned
                };

                // TODO: Get this from `qparse`.
                let function_ownership = FunctionOwnership::Once;

                if let Some(expected_pi) = &expected_pi {
                    assert_eq!(bound_ownership, expected_pi.structure.bound.ownership);
                    assert_eq!(function_ownership, expected_pi.structure.function_ownership);
                }

                // Create the binder structure.
                let structure = BinderStructure {
                    bound: BoundVariable {
                        name: binder.name,
                        ty: binder_ty,
                        ownership: bound_ownership,
                    },
                    binder_annotation: binder.annotation,
                    function_ownership,
                    region: expected_pi
                        .as_ref()
                        .map(|pi| pi.structure.region)
                        .unwrap_or_else(|| {
                            self.hole(
                                ctx,
                                self.provenance(fn_token),
                                Some(Expression::region(self.cache())),
                            )
                        }),
                };

                // Process the rest of the arguments.
                let local = self.cache().gen_local(structure);
                self.preprocess_lambda(
                    if let Some(expected_pi) = &expected_pi {
                        Some(expected_pi.result.instantiate(
                            self.cache(),
                            Expression::new(
                                self.cache(),
                                local.structure.bound.name.0.provenance,
                                ExpressionT::LocalConstant(local),
                            ),
                        ))
                    } else {
                        todo!()
                    },
                    &ctx.clone().with(local),
                    fn_token,
                    &binders[1..],
                    result,
                )
                .map(|body| {
                    Expression::new(
                        self.cache(),
                        binder.name.0.provenance,
                        ExpressionT::Lambda(body.abstract_binder(self.cache(), local)),
                    )
                })
            })
        } else {
            self.preprocess(result, expected_type, ctx)
        }
    }

    fn preprocess_function_type(
        &mut self,
        expected_type: Option<Expression<'cache>>,
        ctx: &Context<'cache>,
        binder: &PFunctionBinder,
        arrow_token: Span,
        result: &PExpression,
    ) -> Dr<Expression<'cache>> {
        assert!(expected_type.is_none(), "deal with this later");
        self.preprocess(&binder.ty, None, ctx).bind(|binder_ty| {
            // Add the new bound variable to the context.
            let bound_ownership = if let Some((ownership, _)) = binder.ownership {
                ownership
            } else {
                // TODO: Make a more intelligent choice based on `binder_ty`.
                ParameterOwnership::POwned
            };

            // TODO: Get this from `qparse`.
            let function_ownership = FunctionOwnership::Once;

            // Create the binder structure.
            let structure = BinderStructure {
                bound: BoundVariable {
                    name: binder.name.unwrap_or_else(|| {
                        Name(WithProvenance::new(
                            self.provenance(binder.ty.span()),
                            Str::new(self.db(), "_".to_owned()),
                        ))
                    }),
                    ty: binder_ty,
                    ownership: bound_ownership,
                },
                binder_annotation: binder.annotation,
                function_ownership,
                region: self.hole(
                    ctx,
                    self.provenance(arrow_token),
                    Some(Expression::region(self.cache())),
                ),
            };

            if binder.name.is_some() {
                let local = self.cache().gen_local(structure);
                self.preprocess(result, None, &ctx.clone().with(local))
                    .map(|result| {
                        Expression::new(
                            self.cache(),
                            self.provenance(arrow_token),
                            ExpressionT::Pi(result.abstract_binder(self.cache(), local)),
                        )
                    })
            } else {
                // We didn't bind a new variable, so we don't need to change the context.
                self.preprocess(result, None, ctx).map(|result| {
                    Expression::new(
                        self.cache(),
                        self.provenance(arrow_token),
                        ExpressionT::Pi(Binder { structure, result }),
                    )
                })
            }
        })
    }

    fn preprocess_sort(
        &mut self,
        expected_type: Option<Expression<'cache>>,
        span: Span,
        universe: &PUniverse,
    ) -> Dr<Expression<'cache>> {
        assert!(expected_type.is_none(), "deal with this later");
        Dr::ok(Expression::new(
            self.cache(),
            self.provenance(span),
            ExpressionT::Sort(Sort(self.preprocess_universe(universe))),
        ))
    }

    fn preprocess_type(
        &mut self,
        expected_type: Option<Expression<'cache>>,
        span: Span,
        universe: &Option<(Span, PUniverse, Span)>,
    ) -> Dr<Expression<'cache>> {
        assert!(expected_type.is_none(), "deal with this later");
        Dr::ok(Expression::new(
            self.cache(),
            self.provenance(span),
            ExpressionT::Sort(Sort(if let Some((_, universe, _)) = universe {
                let universe = self.preprocess_universe(universe);
                Universe::new(
                    universe.provenance,
                    UniverseContents::UniverseSucc(UniverseSucc(Box::new(universe))),
                )
            } else {
                Universe::new(
                    self.provenance(span),
                    UniverseContents::UniverseSucc(UniverseSucc(Box::new(Universe::new(
                        self.provenance(span),
                        UniverseContents::UniverseZero,
                    )))),
                )
            })),
        ))
    }

    fn preprocess_universe(&mut self, universe: &PUniverse) -> Universe {
        match universe {
            PUniverse::Variable(variable) => Universe::new(
                self.provenance(variable.0.provenance.span()),
                UniverseContents::UniverseVariable(UniverseVariable(*variable)),
            ),
            PUniverse::Succ { .. } => todo!(),
            PUniverse::ImpredicativeMax { .. } => todo!(),
            PUniverse::Metauniverse { .. } => todo!(),
        }
    }
}
