use std::collections::BTreeMap;

use fcommon::{Source, SourceSpan, Span, Str};
use fkernel::{
    basic::{Name, Provenance, QualifiedName, WithProvenance},
    expr::*,
    result::Dr,
    universe::{Universe, UniverseContents, UniverseVariable},
};
use qdelab::delaborate;
use qformat::pexpression_to_document;
use qparse::expr::PExpression;

use crate::constraint::{Justification, UnificationConstraint};

/// The elaborator converts parsed quill expressions into feather expressions.
/// An elaborator keeps track of metavariable assignments and performs unification tasks.
///
/// When all necessary expressions have been passed through the elaborator, it can be *finalised*,
/// making a final decision on what terms metavariables should map to, ensuring that all metavariables
/// actually have an assignment, and that the result is type-correct.
pub struct Elaborator<'a, 'cache> {
    cache: &'a ExpressionCache<'cache>,
    source: Source,
    current_definition_name: Name,
    /// If we're currently elaborating a definition, `get_definition` or `get_inductive` won't be able to
    /// actually get the definition in question since it'll cause a cycle.
    ///
    /// To fix this, we keep track of the current definition, and its elaborated type and universe parameters.
    /// Of course, elaborating the type of the definition can only be done with an existing elaborator,
    /// so this field is [`None`] while we do that.
    /// Consequently, the *type* of a definition can't depend on the definition itself, but that is a
    /// completely reasonable restriction - that's also verified in the kernel.
    pub(crate) current_definition_type: Option<(Expression<'cache>, Vec<Name>)>,
    /// TODO: This probably shouldn't be a [`Vec`].
    /// The API is designed so that changing this type should be easy.
    pub(crate) unification_constraints: Vec<UnificationConstraint<'cache>>,
}

#[derive(Default, Clone)]
pub struct Context<'cache> {
    /// A map from local variable names to the local constants representing these local variables.
    local_variables: BTreeMap<Str, LocalConstant<Expression<'cache>>>,
}

impl<'cache> Context<'cache> {
    pub fn with(mut self, local: LocalConstant<Expression<'cache>>) -> Self {
        self.local_variables
            .insert(*local.structure.bound.name, local);
        self
    }

    pub fn get(&self, name: Str) -> Option<&LocalConstant<Expression<'cache>>> {
        self.local_variables.get(&name)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TypedExpression<'cache> {
    pub expr: Expression<'cache>,
    pub ty: Expression<'cache>,
}

impl<'a, 'cache> Elaborator<'a, 'cache> {
    /// Creates a new elaborator.
    pub fn new(cache: &'a ExpressionCache<'cache>, source: Source, definition: Name) -> Self {
        Self {
            cache,
            source,
            current_definition_name: definition,
            current_definition_type: None,
            unification_constraints: Vec::new(),
        }
    }

    /// Tries to elaborate the parsed expression.
    /// This process can create and unify metavariables stored in this elaborator.
    pub fn elaborate(
        &mut self,
        e: &PExpression,
        expected_type: Option<Expression<'cache>>,
        context: &Context<'cache>,
    ) -> Dr<Expression<'cache>> {
        self.preprocess(e, expected_type, context)
    }

    pub fn cache(&self) -> &'a ExpressionCache<'cache> {
        self.cache
    }

    pub fn source(&self) -> Source {
        self.source
    }

    pub fn db(&self) -> &'a dyn fkernel::Db {
        self.cache.db()
    }

    pub fn provenance(&self, span: Span) -> Provenance {
        Provenance::Quill(SourceSpan {
            source: self.source,
            span,
        })
    }

    pub fn current_definition_name(&self) -> Name {
        self.current_definition_name
    }

    /// Creates a new hole: a metavariable with a given type, in a given context.
    /// If the expected type is unknown, it is created as another hole.
    /// If the expected type is (syntactically) `Region`, we will create a metaregion hole instead of a metavariable hole.
    ///
    /// Creating a hole of type `C` inside a context `x: A, y: B` creates the expression `?m[x, y]`.
    pub fn hole(
        &mut self,
        ctx: &Context<'cache>,
        provenance: Provenance,
        ty: Option<Expression<'cache>>,
    ) -> Expression<'cache> {
        let ty = ty.unwrap_or_else(|| {
            let ty_ty = Some(Expression::new(
                self.cache(),
                provenance,
                ExpressionT::Sort(Sort(WithProvenance::new(
                    provenance,
                    UniverseContents::Metauniverse(self.cache().gen_metauniverse()),
                ))),
            ));
            self.hole(ctx, provenance, ty_ty)
        });

        let hole = self.cache.gen_hole(
            ctx.local_variables
                .values()
                .map(|constant| {
                    Expression::new(
                        self.cache,
                        provenance,
                        ExpressionT::LocalConstant(*constant),
                    )
                })
                .collect(),
            ty,
        );
        Expression::new(
            self.cache(),
            provenance,
            if ty.value(self.cache()) == ExpressionT::Region {
                ExpressionT::RegionHole(hole)
            } else {
                ExpressionT::Hole(hole)
            },
        )
    }

    /// Create a new metauniverse.
    pub fn universe_hole(&mut self, provenance: Provenance) -> Universe {
        Universe::new(
            provenance,
            UniverseContents::Metauniverse(self.cache().gen_metauniverse()),
        )
    }

    /// Add the constraints that this expression is type correct.
    /// Returns the type that it was deduced to have.
    pub fn constrain_type_correct(&mut self, expr: Expression<'cache>) -> Dr<Expression<'cache>> {
        self.infer_type_with_constraints(expr).map(|ty| {
            #[cfg(feature = "elaborator_diagnostics")]
            for constraint in &ty.constraints {
                assert!(
                    constraint.expected.closed(self.cache())
                        && constraint.actual.closed(self.cache()),
                    "{} =?= {} because {}",
                    self.pretty_print(constraint.expected),
                    self.pretty_print(constraint.actual),
                    constraint.justification.display(self),
                );
                tracing::trace!(
                    "inference: unifying {} =?= {} because {}",
                    self.pretty_print(constraint.expected),
                    self.pretty_print(constraint.actual),
                    constraint.justification.display(self),
                );
            }
            self.unification_constraints.extend(ty.constraints);
            ty.expr
        })
    }

    /// Infers the type of this expression, storing any constraints that were generated.
    /// Use this instead of the method from `fkernel` while we are in the elaborator.
    ///
    /// If the expression was found to have a function type where the argument is given implicitly,
    /// fill the implicit argument with a new hole of the required type.
    /// If `apply_weak` is true, we also apply weak implicit parameters.
    ///
    /// Returns the expression with implicit parameters substituted, and its type.
    pub fn infer_type(
        &mut self,
        expr: Expression<'cache>,
        ctx: &Context<'cache>,
        apply_weak: bool,
    ) -> Dr<TypedExpression<'cache>> {
        self.infer_type_with_constraints(expr).map(|ty| {
            // For now, ignore the constraints on the type.
            self.apply_implicit_args(expr, ty.expr, ctx, apply_weak)
        })
    }

    fn apply_implicit_args(
        &mut self,
        mut expr: Expression<'cache>,
        mut ty: Expression<'cache>,
        ctx: &Context<'cache>,
        apply_weak: bool,
    ) -> TypedExpression<'cache> {
        while let ExpressionT::Pi(pi) = ty.value(self.cache()) {
            match pi.structure.binder_annotation {
                BinderAnnotation::Explicit => break,
                BinderAnnotation::ImplicitEager => {
                    let hole = self.hole(
                        ctx,
                        expr.provenance(self.cache()),
                        Some(pi.structure.bound.ty),
                    );
                    expr = Expression::new(
                        self.cache(),
                        expr.provenance(self.cache()),
                        ExpressionT::Apply(Apply {
                            function: expr,
                            argument: hole,
                        }),
                    );
                    ty = pi.result.instantiate(self.cache(), hole);
                }
                BinderAnnotation::ImplicitWeak => {
                    if apply_weak {
                        let hole = self.hole(
                            ctx,
                            expr.provenance(self.cache()),
                            Some(pi.structure.bound.ty),
                        );
                        expr = Expression::new(
                            self.cache(),
                            expr.provenance(self.cache()),
                            ExpressionT::Apply(Apply {
                                function: expr,
                                argument: hole,
                            }),
                        );
                        ty = pi.result.instantiate(self.cache(), hole);
                    } else {
                        break;
                    }
                }
                BinderAnnotation::ImplicitTypeclass => todo!("TODO: typeclass resolution"),
            }
        }
        TypedExpression { expr, ty }
    }

    pub fn pretty_print(&self, expr: Expression<'cache>) -> String {
        pexpression_to_document(
            self.db(),
            &delaborate(self.cache(), expr, &Default::default(), true),
        )
        .pretty_print(100)
    }

    /// Adds a unification constraint.
    pub fn add_unification_constraint(
        &mut self,
        expected: Expression<'cache>,
        actual: Expression<'cache>,
        justification: Justification<'cache>,
    ) {
        // tracing::trace!(
        //     "direct: unifying {} =?= {} because {}",
        //     self.pretty_print(expected),
        //     self.pretty_print(actual),
        //     justification.display(self),
        // );
        self.unification_constraints.push(UnificationConstraint {
            expected,
            actual,
            justification,
        });
    }

    /// Declares the current type and universe parameters for this definition.
    pub fn set_current_definition_type(
        &mut self,
        current_definition_type: Expression<'cache>,
        universe_params: &[Name],
    ) {
        assert!(self.current_definition_type.is_none());
        self.current_definition_type = Some((current_definition_type, universe_params.to_owned()));
    }

    pub fn inst_definition(&self, provenance: Provenance) -> Inst {
        Inst {
            name: QualifiedName(WithProvenance::new(
                provenance,
                self.source
                    .path(self.db())
                    .segments(self.db())
                    .iter()
                    .map(|s| Name(WithProvenance::new(provenance, *s)))
                    .chain(std::iter::once(self.current_definition_name))
                    .collect(),
            )),
            universes: self
                .current_definition_type
                .as_ref()
                .unwrap()
                .1
                .iter()
                .map(|name| {
                    Universe::new(
                        name.0.provenance,
                        UniverseContents::UniverseVariable(UniverseVariable(*name)),
                    )
                })
                .collect(),
        }
    }
}
