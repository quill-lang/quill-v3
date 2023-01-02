use std::collections::BTreeMap;

use fcommon::{Source, SourceSpan, Span, Str};
use fkernel::{
    basic::{Provenance, WithProvenance},
    expr::*,
    result::Dr,
    universe::{MetauniverseGenerator, UniverseContents},
};
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
    meta_gen: MetavariableGenerator<Expression<'cache>>,
    metauniverse_gen: MetauniverseGenerator,
    /// TODO: This probably shouldn't be a [`Vec`].
    /// The API is designed so that changing this type should be easy.
    unification_constraints: Vec<UnificationConstraint<'cache>>,
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

impl<'a, 'cache> Elaborator<'a, 'cache> {
    /// Creates a new elaborator.
    /// `largest_unusable` is used to instantiate the metavariable generator.
    pub fn new(
        cache: &'a ExpressionCache<'cache>,
        source: Source,
        largest_unusable: Option<u32>,
        largest_unusable_metauniverse: Option<u32>,
    ) -> Self {
        Self {
            cache,
            source,
            meta_gen: MetavariableGenerator::new(largest_unusable),
            metauniverse_gen: MetauniverseGenerator::new(largest_unusable_metauniverse),
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

    pub fn db(&self) -> &'a dyn fkernel::Db {
        self.cache.db()
    }

    pub fn meta_gen(&mut self) -> &mut MetavariableGenerator<Expression<'cache>> {
        &mut self.meta_gen
    }

    pub fn metauniverse_gen(&mut self) -> &mut MetauniverseGenerator {
        &mut self.metauniverse_gen
    }

    pub fn provenance(&self, span: Span) -> Provenance {
        Provenance::Quill(SourceSpan {
            source: self.source,
            span,
        })
    }

    /// Creates a new hole: a metavariable with a given type, in a given context.
    /// If the expected type is unknown, it is created as another hole.
    ///
    /// Since only closed expressions can be assigned to metavariables, creating a hole of type `C` inside a context `x: A, y: B`
    /// actually creates the metavariable `m: (x: A) -> (y: B) -> C` and returns `m x y`.
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
                ExpressionT::Sort(Sort(WithProvenance::new_with_provenance(
                    provenance,
                    UniverseContents::Metauniverse(self.metauniverse_gen().gen()),
                ))),
            ));
            self.hole(ctx, provenance, ty_ty)
        });

        // TODO: `create_nary_application` and `abstract_nary_pi` work strangely with local constants
        // introduced by function types invoked from behind a borrow.
        Expression::new(
            self.cache(),
            provenance,
            ExpressionT::Metavariable(
                self.meta_gen.gen(
                    ty.abstract_nary_pi(
                        self.cache(),
                        ctx.local_variables
                            .values()
                            .map(|constant| (provenance, *constant)),
                    ),
                ),
            ),
        )
        .create_nary_application(
            self.cache(),
            ctx.local_variables.values().map(|constant| {
                (
                    provenance,
                    Expression::new(
                        self.cache(),
                        constant.structure.bound.name.0.provenance,
                        ExpressionT::LocalConstant(*constant),
                    ),
                )
            }),
        )
    }

    /// Adds a unification constraint.
    pub fn add_unification_constraint(
        &mut self,
        expected: Expression<'cache>,
        actual: Expression<'cache>,
        justification: Justification,
    ) {
        self.unification_constraints.push(UnificationConstraint {
            expected,
            actual,
            justification,
        });
        tracing::info!(
            "unifying {} with {}",
            expected.to_heap(self.cache()).display(self.db()),
            actual.to_heap(self.cache()).display(self.db())
        )
    }
}
