//! # Expressions and terms
//!
//! A term is a feather value. An expression is a term with provenance data; it tracks where expressions were written in code.
//! Expressions should be used for user-provided data, and things like type checking where we want to be able to output error messages at precise locations.
//! Terms should be used for things like kernel computation and code generation, where we either discard provenance data, or it is not relevant.
//!
//! ## Type parameters
//!
//! Throughout this file, we work under the assumption that we have a type variable `E` representing an expression or term type.
//! Most commonly, this will be `Term` or `Expression`.
//! We then construct the type `ExpressionT`, generic over this parameter `E`.
//! This allows us to write functions that are generic over both `Term` and `Expression`.
//!
//! ## Interning
//!
//! Terms can be interned, as they have no provenance information. The type `Term` is the interned version, and `TermData` is the 'unboxed' version.
//! Since `TermData = ExpressionT<Term>` is parametrised by `Term` and not `TermData`, when we look up an interned term value, we only 'unbox' one level at a time.
//! This improves efficiency, and allows us to cache various results about many small terms, such as their type.

use salsa::{InternId, InternKey};
use serde::{Deserialize, Serialize};

use crate::{
    basic::*,
    multiplicity::{InvocationType, ParameterOwnership},
    universe::Universe,
};

/// An interned term type.
/// Can be safely copied and compared cheaply.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Term(InternId);

impl InternKey for Term {
    fn from_intern_id(v: InternId) -> Self {
        Self(v)
    }

    fn as_intern_id(&self) -> InternId {
        self.0
    }
}

/// Provides utilities for interning various data types.
///
/// The [`Debug`] constraint is used to give databases a simple [`Debug`] implementation
/// for use in tracing messages.
#[salsa::query_group(TermInternStorage)]
pub trait TermIntern: std::fmt::Debug {
    #[salsa::interned]
    fn intern_term_data(&self, data: TermData) -> Term;
}

impl Term {
    pub fn lookup(&self, db: &dyn TermIntern) -> TermData {
        db.lookup_intern_term_data(*self)
    }
}

impl TermData {
    pub fn intern(self, db: &dyn TermIntern) -> Term {
        db.intern_term_data(self)
    }
}

pub trait ExpressionVariant<E> {
    fn sub_expressions(&self) -> Vec<&E>;
    fn sub_expressions_mut(&mut self) -> Vec<&mut E>;
}

/// A bound local variable inside an abstraction.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Bound {
    pub index: DeBruijnIndex,
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

#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Let<P, E>
where
    P: Default + PartialEq,
{
    /// The name of the local variable to bind.
    pub name_to_assign: Name<P>,
    /// The value to assign to the new bound variable.
    /// The type of the value to assign to the bound variable.
    pub to_assign_ty: E,
    /// The main body of the expression to be executed after assigning the value.
    pub body: E,
}

#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Borrow<E> {
    /// The region for which to borrow the value.
    pub region: DeBruijnIndex,
    /// The value to be borrowed.
    pub value: E,
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
pub struct Lambda<P, E>
where
    P: Default + PartialEq,
{
    /// The name of the parameter.
    pub parameter_name: Name<P>,
    /// How the parameter should be filled when calling the function.
    pub binder_annotation: BinderAnnotation,
    /// The multiplicity for which the parameter to the function is owned.
    pub ownership: ParameterOwnership,
    /// The style by which the function is invoked.
    pub invocation_type: InvocationType,
    /// The region for which the function may be owned.
    pub region: E,
    /// The type of the parameter.
    pub parameter_ty: E,
    /// The body of the lambda, also called the lambda term.
    pub result: E,
}

impl<P, E> Lambda<P, E>
where
    P: Default + Clone + PartialEq,
    E: Clone,
{
    /// Generates a local constant that represents the argument to this lambda abstraction.
    pub fn generate_local(&self, meta_gen: &mut MetavariableGenerator<E>) -> LocalConstant<P, E> {
        LocalConstant {
            name: self.parameter_name.clone(),
            metavariable: meta_gen.gen(self.parameter_ty.clone()),
            binder_annotation: self.binder_annotation,
        }
    }
}

/// A region-polymorphic value.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct RegionLambda<P, E>
where
    P: Default + PartialEq,
{
    /// The name of the parameter.
    pub region_name: Name<P>,
    /// The body of the expression.
    pub body: E,
}

#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Pi<P, E>
where
    P: Default + PartialEq,
{
    /// The name of the parameter.
    pub parameter_name: Name<P>,
    /// How the parameter should be filled when calling the function.
    pub binder_annotation: BinderAnnotation,
    /// The multiplicity for which the parameter to the function is owned.
    pub ownership: ParameterOwnership,
    /// The style by which the function is invoked.
    pub invocation_type: InvocationType,
    /// The region for which the function may be owned.
    pub region: E,
    /// The type of the parameter.
    pub parameter_ty: E,
    /// The type of the result.
    pub result: E,
}

impl<P, E> Pi<P, E>
where
    P: Default + Clone + PartialEq,
    E: Clone,
{
    /// Generates a local constant that represents the argument to this dependent function type.
    pub fn generate_local(&self, meta_gen: &mut MetavariableGenerator<E>) -> LocalConstant<P, E> {
        LocalConstant {
            name: self.parameter_name.clone(),
            metavariable: meta_gen.gen(self.parameter_ty.clone()),
            binder_annotation: self.binder_annotation,
        }
    }
}

/// A region-polymorphic type.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct RegionPi<P, E>
where
    P: Default + PartialEq,
{
    /// The name of the parameter.
    pub region_name: Name<P>,
    /// The body of the expression.
    pub body: E,
}

/// Introduces a new region variable into the local context.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct LetRegion<P, E>
where
    P: Default + PartialEq,
{
    /// The name of the parameter.
    pub region_name: Name<P>,
    /// The body of the expression.
    pub body: E,
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

#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Apply<E> {
    /// The function to be invoked.
    pub function: E,
    /// The argument to apply to the function.
    pub argument: E,
}

/// Represents the universe of types corresponding to the given universe.
/// For example, if the universe is `0`, this is `Prop`, the type of propositions.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sort<P>(pub Universe<P>)
where
    P: Default + PartialEq;

/// An inference variable.
/// May have theoretically any type.
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
    /// The position of the name is where it was defined, not where it was used.
    pub name: Name<P>,
    pub metavariable: Metavariable<E>,
    /// How was this local variable introduced?
    pub binder_annotation: BinderAnnotation,
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
    pub fn new(largest_unusable: Option<Metavariable<E>>) -> Self {
        Self {
            _phantom: Default::default(),
            next_var: largest_unusable.map_or(0, |x| x.index + 1),
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
    Bound(Bound),
    Inst(Inst<P>),
    Let(Let<P, E>),
    Borrow(Borrow<E>),
    Lambda(Lambda<P, E>),
    RegionLambda(RegionLambda<P, E>),
    Pi(Pi<P, E>),
    RegionPi(RegionPi<P, E>),
    LetRegion(LetRegion<P, E>),
    Delta(Delta<E>),
    Apply(Apply<E>),
    Sort(Sort<P>),
    Region,
    StaticRegion,
    Metavariable(Metavariable<E>),
    LocalConstant(LocalConstant<P, E>),
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expression(pub WithProvenance<Provenance, ExpressionT<Provenance, Box<Expression>>>);

pub type TermData = ExpressionT<(), Term>;

impl Expression {
    pub fn to_term(self, db: &dyn TermIntern) -> Term {
        match self.0.contents {
            ExpressionT::Bound(e) => ExpressionT::Bound(e).intern(db),
            ExpressionT::Inst(e) => ExpressionT::Inst(Inst {
                name: e.name.clone().without_provenance(),
                universes: e
                    .universes
                    .into_iter()
                    .map(Universe::without_provenance)
                    .collect(),
            })
            .intern(db),
            ExpressionT::Let(e) => ExpressionT::Let(Let {
                name_to_assign: e.name_to_assign.without_provenance(),
                to_assign_ty: e.to_assign_ty.to_term(db),
                body: e.body.to_term(db),
            })
            .intern(db),
            ExpressionT::Borrow(e) => ExpressionT::Borrow(Borrow {
                region: e.region,
                value: e.value.to_term(db),
            })
            .intern(db),
            ExpressionT::Lambda(e) => ExpressionT::Lambda(Lambda {
                parameter_name: e.parameter_name.without_provenance(),
                binder_annotation: e.binder_annotation,
                ownership: e.ownership,
                invocation_type: e.invocation_type,
                region: e.region.to_term(db),
                parameter_ty: e.parameter_ty.to_term(db),
                result: e.result.to_term(db),
            })
            .intern(db),
            ExpressionT::RegionLambda(e) => ExpressionT::RegionLambda(RegionLambda {
                region_name: e.region_name.without_provenance(),
                body: e.body.to_term(db),
            })
            .intern(db),
            ExpressionT::Pi(e) => ExpressionT::Pi(Pi {
                parameter_name: e.parameter_name.without_provenance(),
                binder_annotation: e.binder_annotation,
                ownership: e.ownership,
                invocation_type: e.invocation_type,
                region: e.region.to_term(db),
                parameter_ty: e.parameter_ty.to_term(db),
                result: e.result.to_term(db),
            })
            .intern(db),
            ExpressionT::RegionPi(e) => ExpressionT::RegionPi(RegionPi {
                region_name: e.region_name.without_provenance(),
                body: e.body.to_term(db),
            })
            .intern(db),
            ExpressionT::LetRegion(e) => ExpressionT::LetRegion(LetRegion {
                region_name: e.region_name.without_provenance(),
                body: e.body.to_term(db),
            })
            .intern(db),
            ExpressionT::Delta(e) => ExpressionT::Delta(Delta {
                region: e.region.to_term(db),
                ty: e.ty.to_term(db),
            })
            .intern(db),
            ExpressionT::Apply(e) => ExpressionT::Apply(Apply {
                function: e.function.to_term(db),
                argument: e.argument.to_term(db),
            })
            .intern(db),
            ExpressionT::Sort(e) => ExpressionT::Sort(Sort(e.0.without_provenance())).intern(db),
            ExpressionT::Region => ExpressionT::Region.intern(db),
            ExpressionT::StaticRegion => ExpressionT::StaticRegion.intern(db),
            ExpressionT::Metavariable(e) => ExpressionT::Metavariable(Metavariable {
                index: e.index,
                ty: e.ty.to_term(db),
            })
            .intern(db),
            ExpressionT::LocalConstant(e) => ExpressionT::LocalConstant(LocalConstant {
                name: e.name.without_provenance(),
                metavariable: Metavariable {
                    index: e.metavariable.index,
                    ty: e.metavariable.ty.to_term(db),
                },
                binder_annotation: e.binder_annotation,
            })
            .intern(db),
        }
    }
}
