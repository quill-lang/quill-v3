//! # Expressions and terms
//!
//! A term is a feather value. An expression is a term with provenance data; it tracks where expressions were written in code.
//! Expressions should be used for user-provided data, and things like type checking where we want to be able to output error messages at precise locations.
//! Terms should be used for things like kernel computation and code generation, where we either discard provenance data, or it is not relevant.
//!
//! ## Type parameters
//!
//! Throughout this file, we work under the assumption that we have a type variable `E` representing an expression or term type.
//! Most commonly, this will be [`Term`] or [`Expression`].
//! We then construct the type [`ExpressionT`], generic over this parameter `E`.
//! This allows us to write functions that are generic over both [`Term`] and [`Expression`].
//!
//! ## Interning
//!
//! Terms can be interned by salsa, as they have no provenance information.
//! Since [`ExpressionT<(), Term>`] is parametrised by the interned `Term` type, when we look up an interned term value, we only 'unbox' one level at a time.
//! This improves efficiency, and allows us to cache various results about many small terms, such as their type.

use std::cmp::max;

use fcommon::with_local_database;
use serde::{Deserialize, Serialize};

use crate::{
    basic::*,
    multiplicity::{InvocationType, ParameterOwnership},
    universe::{Universe, UniverseContents, UniverseSucc},
    Db,
};

/// Use a bound local variable inside a `let` or an abstraction.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Local {
    /// The local variable to be used.
    pub index: DeBruijnIndex,
}

/// Borrow from an expression.
/// In valid programs, the borrowed value must be a [`Local`] variable.
/// However, we don't make this restriction yet.
/// This allows us to (for example) perform analysis on expressions like `&(a + b)`,
/// instead of having to reason indirectly about local variables and binders.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Borrow<E> {
    /// The region for which the value is borrowed.
    /// This should usually be a metavariable, to be filled in by the borrow checker.
    pub region: E,
    /// The value to be borrowed.
    pub value: E,
}

/// A Delta-type (Δ-type) is the type of borrowed values of another type.
/// For instance, if `x : T`, `&x : ΔT`.
/// Note that `&T` is a value which is borrowed, and the value behind the borrow is a type;
/// `ΔT` is a type in its own right.
///
/// Note: the name `Δ` was chosen for the initial letter of the Greek words "δάνειο" and
/// "δανείζομαι" (roughly, "loan" and "borrow"). A capital beta for "borrow" was an option,
/// but this would look identical to a Latin letter B.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Delta<E> {
    /// The region for which a value is borrowed.
    pub region: E,
    /// The type of values which is to be borrowed.
    pub ty: E,
}

/// Either a definition or an inductive data type.
/// Parametrised by a list of universe parameters.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Inst<P>
where
    P: Default + PartialEq,
{
    pub name: QualifiedName<P>,
    pub universes: Vec<Universe<P>>,
}

/// A bound variable in a lambda, pi, let, or lifespan expression.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BoundVariable<P, E>
where
    P: Default + PartialEq,
{
    /// The name of the local variable to bind.
    pub name: Name<P>,
    /// The type of the value assigned to the bound variable.
    pub ty: E,
    /// The multiplicity for which the value is bound.
    pub ownership: ParameterOwnership,
}

impl BoundVariable<Provenance, Box<Expression>> {
    fn without_provenance(&self, db: &dyn Db) -> BoundVariable<(), Term> {
        BoundVariable {
            name: self.name.without_provenance(),
            ty: self.ty.to_term(db),
            ownership: self.ownership,
        }
    }
}

impl BoundVariable<(), Term> {
    fn synthetic(&self, db: &dyn Db) -> BoundVariable<Provenance, Box<Expression>> {
        BoundVariable {
            name: self.name.synthetic(),
            ty: Box::new(self.ty.to_expression(db)),
            ownership: self.ownership,
        }
    }
}

#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Let<P, E>
where
    P: Default + PartialEq,
{
    /// The local variable to bind.
    pub bound: BoundVariable<P, E>,
    /// The value to assign to the new bound variable.
    pub to_assign: E,
    /// The main body of the expression to be executed after assigning the value.
    pub body: E,
}

/// How should the argument to this function be given?
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum BinderAnnotation {
    /// The argument is to be given explicitly.
    Explicit,
    /// The argument is implicit, and is to be filled eagerly by the elaborator.
    ImplicitEager,
    /// The argument is implicit, and is to be filled by the elaborator only when another later parameter is given.
    ImplicitWeak,
    /// The argument is implicit, and is to be filled by the elaborator by typeclass resolution.
    ImplicitTypeclass,
}

#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BinderStructure<P, E>
where
    P: Default + PartialEq,
{
    /// The local variable to bind.
    pub bound: BoundVariable<P, E>,
    /// How the parameter should be filled when calling the function.
    pub binder_annotation: BinderAnnotation,
    /// The style by which the function is invoked.
    pub invocation_type: InvocationType,
    /// The region for which the function may be owned.
    pub region: E,
}

impl BinderStructure<Provenance, Box<Expression>> {
    pub fn without_provenance(&self, db: &dyn Db) -> BinderStructure<(), Term> {
        BinderStructure {
            bound: self.bound.without_provenance(db),
            binder_annotation: self.binder_annotation,
            invocation_type: self.invocation_type,
            region: self.region.to_term(db),
        }
    }
}

impl BinderStructure<(), Term> {
    pub fn synthetic(&self, db: &dyn Db) -> BinderStructure<Provenance, Box<Expression>> {
        BinderStructure {
            bound: self.bound.synthetic(db),
            binder_annotation: self.binder_annotation,
            invocation_type: self.invocation_type,
            region: Box::new(self.region.to_expression(db)),
        }
    }
}

/// Either a lambda abstraction or the type of such lambda abstractions.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Binder<P, E>
where
    P: Default + PartialEq,
{
    /// The structure of the binder.
    pub structure: BinderStructure<P, E>,
    /// The result.
    /// If this is a lambda abstraction, this is the lambda term.
    /// If this is a function type, this is the type of the function's body.
    pub result: E,
}

impl<P, E> BinderStructure<P, E>
where
    P: Default + Clone + PartialEq,
    E: Clone,
{
    /// Generates a local constant that represents the argument to this dependent function type.
    pub fn generate_local_with_gen(
        &self,
        meta_gen: &mut MetavariableGenerator<E>,
    ) -> LocalConstant<P, E> {
        LocalConstant {
            metavariable: meta_gen.gen(self.bound.ty.clone()),
            structure: self.clone(),
        }
    }

    /// Generates a local constant that represents the argument to this dependent function type.
    /// The index of the metavariable is guaranteed not to collide with the metavariables in `t`.
    pub fn generate_local(&self, db: &dyn Db, t: Term) -> LocalConstant<P, E> {
        self.generate_local_with_gen(&mut MetavariableGenerator::new(
            largest_unusable_metavariable(db, t),
        ))
    }
}

/// A [`Binder`] that takes an arbitrary amount of parameters, including zero.
/// Each binder may depend on the previous ones.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct NaryBinder<P, E>
where
    P: Default + PartialEq,
{
    /// The structures of each successive binder.
    pub structures: Vec<BinderStructure<P, E>>,
    /// The result.
    /// If this is a lambda abstraction, this is the lambda term.
    /// If this is a function type, this is the type of the function's body.
    pub result: E,
}

impl NaryBinder<Provenance, Box<Expression>> {
    pub fn without_provenance(&self, db: &dyn Db) -> NaryBinder<(), Term> {
        NaryBinder {
            structures: self
                .structures
                .iter()
                .map(|structure| structure.without_provenance(db))
                .collect(),
            result: self.result.to_term(db),
        }
    }
}

/// A region-polymorphic value, or the type of such values.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct RegionBinder<P, E>
where
    P: Default + PartialEq,
{
    /// The name of the parameter.
    pub region_name: Name<P>,
    /// The body of the expression.
    pub body: E,
}

#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Apply<E> {
    /// The function to be invoked.
    pub function: E,
    /// The argument to apply to the function.
    pub argument: E,
}

/// Constructs an inductive data type using an introduction rule.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Intro<P, E>
where
    P: Default + PartialEq,
{
    /// The inductive that we are constructing.
    pub inductive: QualifiedName<P>,
    /// The universe parameters on the inductive.
    pub universes: Vec<Universe<P>>,
    /// The name of the variant we are constructing.
    pub variant: Name<P>,
    /// The parameters we supply to the introduction rule.
    /// This is the sequence of global parameters, followed by the list of fields.
    pub parameters: Vec<E>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct MinorPremise<P, E>
where
    P: Default + PartialEq,
{
    /// The variant that this minor premise operates on.
    pub variant: Name<P>,
    /// The number of fields (non-global parameters) that this variant has.
    ///
    /// Technically this is data duplication, since we can infer it from the type of the major premise after
    /// scanning the environment for the relevant definition.
    /// However, we would like to be able to compute with de Bruijn indices without consulting the definitions in the database.
    pub fields: u32,
    /// The result that this pattern match operation yields.
    /// Inside this expression, the lowest indices of local variables correspond to the fields of the relevant inductive
    /// (excluding the global parameters, which are implicitly given by supplying the major premise to the match expression).
    pub result: E,
}

/// Performs dependent pattern matching on an inductive data type.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Match<P, E>
where
    P: Default + PartialEq,
{
    /// The value to eliminate.
    /// The type of the major premise must be an inductive.
    /// We supply this here, instead of making [`Match`] return a function, to avoid issues with lifetimes.
    pub major_premise: E,
    /// The number of index parameters that this inductive has.
    ///
    /// Technically this is data duplication, since we can infer it from the type of the major premise after
    /// scanning the environment for the relevant definition.
    /// However, we would like to be able to compute with de Bruijn indices without consulting the definitions in the database.
    pub index_params: u32,
    /// The type that will be produced by the match operation.
    /// Inside this expression, the local variable with index zero represents the major premise, and higher variables are
    /// the indices of the inductive being matched, so `index_params + 1` variables are bound in this expression.
    /// The type of this expression should be a [`Sort`].
    pub motive: E,
    /// The set of minor premises that represent each possible branch of the match expression.
    pub minor_premises: Vec<MinorPremise<P, E>>,
}

/// The fixed point construction on inductive data types.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Fix<P, E>
where
    P: Default + PartialEq,
{
    /// The concrete argument to instantiate the parameter to the fixed point construction with.
    /// We supply this here, instead of making [`Fix`] return a function, to avoid issues with lifetimes.
    pub argument: E,
    /// The name supplied to the argument to the fixed point construction.
    pub argument_name: Name<P>,
    /// The local variable to be constructed by a fixed point process.
    /// The parameter is bound at index 0 in this expression.
    pub fixpoint: BoundVariable<P, E>,
    /// The main body of the fixed point expression.
    /// The parameter is bound at index 0 and the function `parameter -> fixpoint` is bound at index 1 in this expression.
    /// The parameter `fixpoint` should only be invoked with structurally smaller parameters.
    /// The type of this expression should be `fixpoint.ty`.
    pub body: E,
}

/// Represents the universe of types corresponding to the given universe.
/// For example, if the universe is `0`, this is `Prop`, the type of propositions.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sort<P>(pub Universe<P>)
where
    P: Default + PartialEq;

/// The maximum possible lifespan of a type.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Lifespan<E> {
    /// The type we are analysing the lifespan of.
    pub ty: E,
}

/// An inference variable.
/// May have theoretically any type.
/// Metavariables can be used for region variables that are to be inferred by the borrow checker.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Metavariable<E> {
    pub index: u32,
    /// We store the types of metavariables explicitly, since they can't be inferred.
    pub ty: E,
}

/// De Bruijn indices (bound variables) are replaced with local constants while we're inside the function body.
/// Should not be used in functions manually.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct LocalConstant<P, E>
where
    P: Default + PartialEq,
{
    pub metavariable: Metavariable<E>,
    /// The structure of the binder that introduced this local constant.
    pub structure: BinderStructure<P, E>,
}

/// Generates unique inference variable names.
#[derive(Default)]
pub struct MetavariableGenerator<E> {
    _phantom: std::marker::PhantomData<E>,
    next_var: u32,
}

impl<E> MetavariableGenerator<E> {
    /// Creates a new variable generator.
    /// Its variables will all be greater than the provided "largest unusable" variable name.
    /// If one was not provided, no guarantees are made about name clashing.
    pub fn new(largest_unusable: Option<u32>) -> Self {
        Self {
            _phantom: Default::default(),
            next_var: largest_unusable.map_or(0, |x| x + 1),
        }
    }

    pub fn gen(&mut self, ty: E) -> Metavariable<E> {
        let result = self.next_var;
        self.next_var += 1;
        Metavariable { index: result, ty }
    }
}

/// The main expression type.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExpressionT<P, E>
where
    P: Default + PartialEq,
{
    Local(Local),
    Borrow(Borrow<E>),
    Delta(Delta<E>),
    Inst(Inst<P>),
    Let(Let<P, E>),
    Lambda(Binder<P, E>),
    Pi(Binder<P, E>),
    RegionLambda(RegionBinder<P, E>),
    RegionPi(RegionBinder<P, E>),
    Apply(Apply<E>),
    Intro(Intro<P, E>),
    Match(Match<P, E>),
    Fix(Fix<P, E>),
    Sort(Sort<P>),
    Region,
    /// The type of [`ExpressionT::Region`], and the type of itself.
    RegionT,
    /// TODO: Remove this field, replacing it with a call to [`Inst`] to simplify the kernel.
    StaticRegion,
    Lifespan(Lifespan<E>),
    Metavariable(Metavariable<E>),
    LocalConstant(LocalConstant<P, E>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expression {
    pub value: WithProvenance<Provenance, ExpressionT<Provenance, Box<Expression>>>,
}

impl Expression {
    pub fn new_synthetic(value: ExpressionT<Provenance, Box<Expression>>) -> Self {
        Self {
            value: WithProvenance::new_synthetic(value),
        }
    }
}

impl Serialize for Expression {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.value.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Expression {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        WithProvenance::deserialize(deserializer).map(|value| Self { value })
    }
}

#[salsa::interned]
pub struct Term {
    #[return_ref]
    pub value: ExpressionT<(), Term>,
}

impl Term {
    /// We use [`ron`] to provide nice debug output for terms.
    pub fn display(&self, db: &dyn Db) -> String {
        with_local_database(db, || {
            ron::ser::to_string_pretty(&self.to_expression(db), ron::ser::PrettyConfig::default())
                .unwrap()
        })
    }

    /// Returns the sort of proof-irrelevant propositions.
    pub fn sort_prop(db: &dyn Db) -> Term {
        Term::new(
            db,
            ExpressionT::Sort(Sort(Universe::new(UniverseContents::UniverseZero))),
        )
    }

    /// Returns the sort of small types.
    pub fn sort_type(db: &dyn Db) -> Term {
        Term::new(
            db,
            ExpressionT::Sort(Sort(Universe::new(UniverseContents::UniverseSucc(
                UniverseSucc(Box::new(Universe::new(UniverseContents::UniverseZero))),
            )))),
        )
    }
}

/// Returns the largest metavariable index that was referenced in the given term, or [`None`] if none were referenced.
/// We are free to use metavariables with strictly higher indices than what is returned here without name clashing.
#[must_use]
#[salsa::tracked]
pub fn largest_unusable_metavariable(db: &dyn Db, t: Term) -> Option<u32> {
    match t.value(db) {
        ExpressionT::Local(_) => None,
        ExpressionT::Borrow(t) => max(
            largest_unusable_metavariable(db, t.region),
            largest_unusable_metavariable(db, t.value),
        ),
        ExpressionT::Delta(t) => max(
            largest_unusable_metavariable(db, t.region),
            largest_unusable_metavariable(db, t.ty),
        ),
        ExpressionT::Inst(_) => None,
        ExpressionT::Let(t) => max(
            max(
                largest_unusable_metavariable(db, t.bound.ty),
                largest_unusable_metavariable(db, t.to_assign),
            ),
            largest_unusable_metavariable(db, t.body),
        ),
        ExpressionT::Lambda(t) | ExpressionT::Pi(t) => max(
            max(
                largest_unusable_metavariable(db, t.structure.bound.ty),
                largest_unusable_metavariable(db, t.structure.region),
            ),
            largest_unusable_metavariable(db, t.result),
        ),
        ExpressionT::RegionLambda(t) | ExpressionT::RegionPi(t) => {
            largest_unusable_metavariable(db, t.body)
        }
        ExpressionT::Apply(t) => max(
            largest_unusable_metavariable(db, t.function),
            largest_unusable_metavariable(db, t.argument),
        ),
        ExpressionT::Intro(t) => t
            .parameters
            .iter()
            .map(|param| largest_unusable_metavariable(db, *param))
            .max()
            .unwrap_or(None),
        ExpressionT::Match(t) => t
            .minor_premises
            .iter()
            .map(|premise| largest_unusable_metavariable(db, premise.result))
            .chain(std::iter::once(largest_unusable_metavariable(
                db,
                t.major_premise,
            )))
            .chain(std::iter::once(largest_unusable_metavariable(db, t.motive)))
            .max()
            .unwrap(),
        ExpressionT::Fix(t) => max(
            max(
                largest_unusable_metavariable(db, t.fixpoint.ty),
                largest_unusable_metavariable(db, t.body),
            ),
            largest_unusable_metavariable(db, t.argument),
        ),
        ExpressionT::Sort(_)
        | ExpressionT::Region
        | ExpressionT::RegionT
        | ExpressionT::StaticRegion => None,
        ExpressionT::Lifespan(t) => largest_unusable_metavariable(db, t.ty),
        ExpressionT::Metavariable(t) => Some(t.index),
        ExpressionT::LocalConstant(t) => Some(t.metavariable.index),
    }
}

impl Term {
    /// Converts a term into an expression, using [`Provenance::Synthetic`] where necessary.
    pub fn to_expression(&self, db: &dyn Db) -> Expression {
        match self.value(db) {
            ExpressionT::Local(e) => Expression::new_synthetic(ExpressionT::Local(*e)),
            ExpressionT::Borrow(e) => Expression::new_synthetic(ExpressionT::Borrow(Borrow {
                region: Box::new(e.region.to_expression(db)),
                value: Box::new(e.value.to_expression(db)),
            })),
            ExpressionT::Delta(e) => Expression::new_synthetic(ExpressionT::Delta(Delta {
                region: Box::new(e.region.to_expression(db)),
                ty: Box::new(e.ty.to_expression(db)),
            })),
            ExpressionT::Inst(e) => Expression::new_synthetic(ExpressionT::Inst(Inst {
                name: e.name.synthetic(),
                universes: e
                    .universes
                    .iter()
                    .map(|u| WithProvenance::new_synthetic(u.synthetic()))
                    .collect(),
            })),
            ExpressionT::Let(e) => Expression::new_synthetic(ExpressionT::Let(Let {
                bound: e.bound.synthetic(db),
                to_assign: Box::new(e.to_assign.to_expression(db)),
                body: Box::new(e.body.to_expression(db)),
            })),
            ExpressionT::Lambda(e) => Expression::new_synthetic(ExpressionT::Lambda(Binder {
                structure: e.structure.synthetic(db),
                result: Box::new(e.result.to_expression(db)),
            })),
            ExpressionT::Pi(e) => Expression::new_synthetic(ExpressionT::Pi(Binder {
                structure: e.structure.synthetic(db),
                result: Box::new(e.result.to_expression(db)),
            })),
            ExpressionT::RegionLambda(e) => {
                Expression::new_synthetic(ExpressionT::RegionLambda(RegionBinder {
                    region_name: e.region_name.synthetic(),
                    body: Box::new(e.body.to_expression(db)),
                }))
            }
            ExpressionT::RegionPi(e) => {
                Expression::new_synthetic(ExpressionT::RegionPi(RegionBinder {
                    region_name: e.region_name.synthetic(),
                    body: Box::new(e.body.to_expression(db)),
                }))
            }
            ExpressionT::Apply(e) => Expression::new_synthetic(ExpressionT::Apply(Apply {
                function: Box::new(e.function.to_expression(db)),
                argument: Box::new(e.argument.to_expression(db)),
            })),
            ExpressionT::Intro(e) => Expression::new_synthetic(ExpressionT::Intro(Intro {
                inductive: e.inductive.synthetic(),
                universes: e
                    .universes
                    .iter()
                    .map(|u| WithProvenance::new_synthetic(u.synthetic()))
                    .collect(),
                variant: e.variant.synthetic(),
                parameters: e
                    .parameters
                    .iter()
                    .map(|term| Box::new(term.to_expression(db)))
                    .collect(),
            })),
            ExpressionT::Match(e) => Expression::new_synthetic(ExpressionT::Match(Match {
                major_premise: Box::new(e.major_premise.to_expression(db)),
                index_params: e.index_params,
                motive: Box::new(e.motive.to_expression(db)),
                minor_premises: e
                    .minor_premises
                    .iter()
                    .map(|premise| MinorPremise {
                        variant: premise.variant.synthetic(),
                        fields: premise.fields,
                        result: Box::new(premise.result.to_expression(db)),
                    })
                    .collect(),
            })),
            ExpressionT::Fix(e) => Expression::new_synthetic(ExpressionT::Fix(Fix {
                argument: Box::new(e.argument.to_expression(db)),
                argument_name: e.argument_name.synthetic(),
                fixpoint: e.fixpoint.synthetic(db),
                body: Box::new(e.body.to_expression(db)),
            })),
            ExpressionT::Sort(e) => Expression::new_synthetic(ExpressionT::Sort(Sort(
                WithProvenance::new_synthetic(e.0.synthetic()),
            ))),
            ExpressionT::Region => Expression::new_synthetic(ExpressionT::Region),
            ExpressionT::RegionT => Expression::new_synthetic(ExpressionT::RegionT),
            ExpressionT::StaticRegion => Expression::new_synthetic(ExpressionT::StaticRegion),
            ExpressionT::Lifespan(e) => {
                Expression::new_synthetic(ExpressionT::Lifespan(Lifespan {
                    ty: Box::new(e.ty.to_expression(db)),
                }))
            }
            ExpressionT::Metavariable(e) => {
                Expression::new_synthetic(ExpressionT::Metavariable(Metavariable {
                    index: e.index,
                    ty: Box::new(e.ty.to_expression(db)),
                }))
            }
            ExpressionT::LocalConstant(e) => {
                Expression::new_synthetic(ExpressionT::LocalConstant(LocalConstant {
                    metavariable: Metavariable {
                        index: e.metavariable.index,
                        ty: Box::new(e.metavariable.ty.to_expression(db)),
                    },
                    structure: e.structure.synthetic(db),
                }))
            }
        }
    }
}

impl Expression {
    pub fn to_term(&self, db: &dyn Db) -> Term {
        match &self.value.contents {
            ExpressionT::Local(e) => Term::new(db, ExpressionT::Local(*e)),
            ExpressionT::Borrow(e) => Term::new(
                db,
                ExpressionT::Borrow(Borrow {
                    region: e.region.to_term(db),
                    value: e.value.to_term(db),
                }),
            ),
            ExpressionT::Delta(e) => Term::new(
                db,
                ExpressionT::Delta(Delta {
                    region: e.region.to_term(db),
                    ty: e.ty.to_term(db),
                }),
            ),
            ExpressionT::Inst(e) => Term::new(
                db,
                ExpressionT::Inst(Inst {
                    name: e.name.clone().without_provenance(),
                    universes: e
                        .universes
                        .iter()
                        .map(|u| WithProvenance::new(u.contents.without_provenance()))
                        .collect(),
                }),
            ),
            ExpressionT::Let(e) => Term::new(
                db,
                ExpressionT::Let(Let {
                    bound: e.bound.without_provenance(db),
                    to_assign: e.to_assign.to_term(db),
                    body: e.body.to_term(db),
                }),
            ),
            ExpressionT::Lambda(e) => Term::new(
                db,
                ExpressionT::Lambda(Binder {
                    structure: e.structure.without_provenance(db),
                    result: e.result.to_term(db),
                }),
            ),
            ExpressionT::Pi(e) => Term::new(
                db,
                ExpressionT::Pi(Binder {
                    structure: e.structure.without_provenance(db),
                    result: e.result.to_term(db),
                }),
            ),
            ExpressionT::RegionLambda(e) => Term::new(
                db,
                ExpressionT::RegionLambda(RegionBinder {
                    region_name: e.region_name.without_provenance(),
                    body: e.body.to_term(db),
                }),
            ),
            ExpressionT::RegionPi(e) => Term::new(
                db,
                ExpressionT::RegionPi(RegionBinder {
                    region_name: e.region_name.without_provenance(),
                    body: e.body.to_term(db),
                }),
            ),
            ExpressionT::Apply(e) => Term::new(
                db,
                ExpressionT::Apply(Apply {
                    function: e.function.to_term(db),
                    argument: e.argument.to_term(db),
                }),
            ),
            ExpressionT::Intro(e) => Term::new(
                db,
                ExpressionT::Intro(Intro {
                    inductive: e.inductive.without_provenance(),
                    universes: e
                        .universes
                        .iter()
                        .map(|u| WithProvenance::new(u.contents.without_provenance()))
                        .collect(),
                    variant: e.variant.without_provenance(),
                    parameters: e.parameters.iter().map(|e| e.to_term(db)).collect(),
                }),
            ),
            ExpressionT::Match(e) => Term::new(
                db,
                ExpressionT::Match(Match {
                    major_premise: e.major_premise.to_term(db),
                    index_params: e.index_params,
                    motive: e.motive.to_term(db),
                    minor_premises: e
                        .minor_premises
                        .iter()
                        .map(|premise| MinorPremise {
                            variant: premise.variant.without_provenance(),
                            fields: premise.fields,
                            result: premise.result.to_term(db),
                        })
                        .collect(),
                }),
            ),
            ExpressionT::Fix(e) => Term::new(
                db,
                ExpressionT::Fix(Fix {
                    argument: e.argument.to_term(db),
                    argument_name: e.argument_name.without_provenance(),
                    fixpoint: e.fixpoint.without_provenance(db),
                    body: e.body.to_term(db),
                }),
            ),
            ExpressionT::Sort(e) => Term::new(
                db,
                ExpressionT::Sort(Sort(WithProvenance::new(e.0.contents.without_provenance()))),
            ),
            ExpressionT::Region => Term::new(db, ExpressionT::Region),
            ExpressionT::RegionT => Term::new(db, ExpressionT::RegionT),
            ExpressionT::StaticRegion => Term::new(db, ExpressionT::StaticRegion),
            ExpressionT::Lifespan(e) => Term::new(
                db,
                ExpressionT::Lifespan(Lifespan {
                    ty: e.ty.to_term(db),
                }),
            ),
            ExpressionT::Metavariable(e) => Term::new(
                db,
                ExpressionT::Metavariable(Metavariable {
                    index: e.index,
                    ty: e.ty.to_term(db),
                }),
            ),
            ExpressionT::LocalConstant(e) => Term::new(
                db,
                ExpressionT::LocalConstant(LocalConstant {
                    metavariable: Metavariable {
                        index: e.metavariable.index,
                        ty: e.metavariable.ty.to_term(db),
                    },
                    structure: e.structure.without_provenance(db),
                }),
            ),
        }
    }
}
