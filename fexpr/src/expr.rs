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

use serde::{Deserialize, Serialize};

use crate::{
    basic::*,
    multiplicity::{InvocationType, ParameterOwnership},
    universe::Universe,
    Db,
};

/// Use a bound local variable inside a `let` or an abstraction.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Local {
    /// The local variable to be used.
    pub index: DeBruijnIndex,
}

/// Borrow from a bound local variable inside a `let` or an abstraction.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Borrow {
    /// The local variable to be borrowed.
    pub index: DeBruijnIndex,
}

/// Retrieves the region that a given local variable may be borrowed for.
/// Intuitively, this is the set of instructions for which the variable is in scope
/// but has not yet been used in a [`Bound`] expression.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct LocalRegion {
    /// The local variable that we want to extract the region from.
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
    fn without_provenance(self, db: &dyn Db) -> BoundVariable<(), Term> {
        BoundVariable {
            name: self.name.without_provenance(),
            ty: self.ty.to_term(db),
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
    fn without_provenance(self, db: &dyn Db) -> BinderStructure<(), Term> {
        BinderStructure {
            bound: self.bound.without_provenance(db),
            binder_annotation: self.binder_annotation,
            invocation_type: self.invocation_type,
            region: self.region.to_term(db),
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

impl<P, E> Binder<P, E>
where
    P: Default + Clone + PartialEq,
    E: Clone,
{
    /// Generates a local constant that represents the argument to this dependent function type.
    pub fn generate_local(&self, meta_gen: &mut MetavariableGenerator<E>) -> LocalConstant<P, E> {
        LocalConstant {
            metavariable: meta_gen.gen(self.structure.bound.ty.clone()),
            structure: self.structure.clone(),
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

/// The maximum possible lifespan of a type.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Lifespan<E> {
    /// The type we are analysing the lifespan of.
    pub ty: E,
}

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
    Local(Local),
    Borrow(Borrow),
    LocalRegion(LocalRegion),
    Inst(Inst<P>),
    Let(Let<P, E>),
    Lambda(Binder<P, E>),
    Pi(Binder<P, E>),
    RegionLambda(RegionBinder<P, E>),
    RegionPi(RegionBinder<P, E>),
    Delta(Delta<E>),
    Apply(Apply<E>),
    Sort(Sort<P>),
    Region,
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

impl Expression {
    pub fn to_term(self, db: &dyn Db) -> Term {
        match self.value.contents {
            ExpressionT::Local(e) => Term::new(db, ExpressionT::Local(e)),
            ExpressionT::Borrow(e) => Term::new(db, ExpressionT::Borrow(e)),
            ExpressionT::LocalRegion(e) => Term::new(db, ExpressionT::LocalRegion(e)),
            ExpressionT::Inst(e) => Term::new(
                db,
                ExpressionT::Inst(Inst {
                    name: e.name.clone().without_provenance(),
                    universes: e
                        .universes
                        .into_iter()
                        .map(Universe::without_provenance)
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
            ExpressionT::Delta(e) => Term::new(
                db,
                ExpressionT::Delta(Delta {
                    region: e.region.to_term(db),
                    ty: e.ty.to_term(db),
                }),
            ),
            ExpressionT::Apply(e) => Term::new(
                db,
                ExpressionT::Apply(Apply {
                    function: e.function.to_term(db),
                    argument: e.argument.to_term(db),
                }),
            ),
            ExpressionT::Sort(e) => {
                Term::new(db, ExpressionT::Sort(Sort(e.0.without_provenance())))
            }
            ExpressionT::Region => Term::new(db, ExpressionT::Region),
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
