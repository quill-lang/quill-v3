use fcommon::{Span, Spanned, Str};
use fkernel::{
    basic::{Name, QualifiedName, WithProvenance},
    expr::*,
    multiplicity::ParameterOwnership,
    result::Dr,
    universe::{Universe, UniverseContents, UniverseVariable},
};
use qparse::expr::*;

use crate::elaborator::{Context, Elaborator};

impl<'a, 'cache> Elaborator<'a, 'cache> {
    /// Produces constraints that will be solved later.
    /// Returns a closed expression representing the parsed expression.
    ///
    /// When constraints are solved, substituting the solved constraints into the return value of this function
    /// produces the fully elaborated expression.
    pub fn preprocess(
        &mut self,
        e: &PExpression,
        expected_type: Option<Expression<'cache>>,
        ctx: &Context<'cache>,
    ) -> Dr<Expression<'cache>> {
        match e {
            PExpression::Variable {
                name,
                universe_ascription,
            } => self.preprocess_variable(expected_type, ctx, name, universe_ascription),
            PExpression::Borrow { .. } => todo!(),
            PExpression::Dereference { .. } => todo!(),
            PExpression::Apply { .. } => todo!(),
            PExpression::Intro { .. } => todo!(),
            PExpression::Match { .. } => todo!(),
            PExpression::Fix { .. } => todo!(),
            PExpression::Let { .. } => todo!(),
            PExpression::Lambda { .. } => todo!(),
            PExpression::FunctionType {
                binder,
                arrow_token,
                result,
            } => self.preprocess_function_type(expected_type, ctx, binder, *arrow_token, result),
            PExpression::Sort { span, universe } => {
                self.preprocess_sort(expected_type, *span, universe)
            }
            PExpression::Type { .. } => todo!(),
            PExpression::Prop(_) => todo!(),
            PExpression::StaticRegion(_) => todo!(),
            PExpression::Region(_) => todo!(),
            PExpression::RegionT(_) => todo!(),
            PExpression::Inductive(_) => todo!(),
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
                assert!(expected_type.is_none(), "deal with this later");
                assert!(universe_ascription.is_none());
                return Dr::ok(Expression::new(
                    self.cache(),
                    name.0.provenance,
                    ExpressionT::LocalConstant(*local),
                ));
            }
        }
        todo!()
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
                        Name(WithProvenance::new_with_provenance(
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
                let local = structure.generate_local_with_gen(self.meta_gen());
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

    fn preprocess_universe(&mut self, universe: &PUniverse) -> Universe {
        match universe {
            PUniverse::Variable(variable) => Universe::new_with_provenance(
                self.provenance(variable.0.provenance.span()),
                UniverseContents::UniverseVariable(UniverseVariable(*variable)),
            ),
        }
    }
}
