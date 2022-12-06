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

use crate::{basic_nodes::*, universe::Universe};

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

pub trait ExpressionVariant<E> {
    fn sub_expressions(&self) -> Vec<&E>;
    fn sub_expressions_mut(&mut self) -> Vec<&mut E>;
}

/// A bound local variable inside an abstraction.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Bound {
    pub index: DeBruijnIndex,
}

/// Either a definition or an inductive data type.
/// Parametrised by a list of universe parameters.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Inst {
    pub name: QualifiedName,
    pub universes: Vec<Universe>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Let<E> {
    /// The name of the local variable to bind.
    pub name_to_assign: Name,
    /// The value to assign to the new bound variable.
    /// The type of the value to assign to the bound variable.
    pub to_assign_ty: Box<E>,
    /// The main body of the expression to be executed after assigning the value.
    pub body: Box<E>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Borrow<E> {
    /// The region for which to borrow the value.
    pub region: Box<E>,
    /// The value to be borrowed.
    pub value: Box<E>,
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

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Lambda<E> {
    /// The name of the parameter.
    pub parameter_name: Name,
    /// How the parameter should be filled when calling the function.
    pub binder_annotation: BinderAnnotation,
    /// The type of the parameter.
    pub parameter_ty: Box<E>,
    /// The body of the lambda, also called the lambda term.
    pub result: Box<E>,
}

impl<E> Lambda<E>
where
    E: Clone,
{
    /// Generates a local constant that represents the argument to this lambda abstraction.
    pub fn generate_local(&self, meta_gen: &mut MetavariableGenerator<E>) -> LocalConstant<E> {
        LocalConstant {
            name: self.parameter_name.clone(),
            metavariable: meta_gen.gen(*self.parameter_ty.clone()),
            binder_annotation: self.binder_annotation,
        }
    }
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Pi<E> {
    /// The name of the parameter.
    pub parameter_name: Name,
    /// How the parameter should be filled when calling the function.
    pub binder_annotation: BinderAnnotation,
    /// The type of the parameter.
    pub parameter_ty: Box<E>,
    /// The type of the result.
    pub result: Box<E>,
}

impl<E> Pi<E>
where
    E: Clone,
{
    /// Generates a local constant that represents the argument to this dependent function type.
    pub fn generate_local(&self, meta_gen: &mut MetavariableGenerator<E>) -> LocalConstant<E> {
        LocalConstant {
            name: self.parameter_name.clone(),
            metavariable: meta_gen.gen(*self.parameter_ty.clone()),
            binder_annotation: self.binder_annotation,
        }
    }
}

/// A Delta-type (Δ-type) is the type of borrowed values of another type.
/// For instance, if `x : T`, `&x : ΔT`.
/// Note that `&T` is a value which is borrowed, and the value behind the borrow is a type;
/// `ΔT` is a type in its own right.
///
/// Note: the name `Δ` was chosen for the initial letter of the Greek words "δάνειο" and
/// "δανείζομαι" (roughly, "loan" and "borrow"). A capital beta for "borrow" was an option,
/// but this would look identical to a Latin letter B.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Delta<E> {
    /// The region for which a value is borrowed.
    pub region: Box<E>,
    /// The type of values which is to be borrowed.
    pub ty: Box<E>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Apply<E> {
    /// The function to be invoked.
    pub function: Box<E>,
    /// The argument to apply to the function.
    pub argument: Box<E>,
}

/// Represents the universe of types corresponding to the given universe.
/// For example, if the universe is `0`, this is `Prop`, the type of propositions.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sort(pub Universe);

/// The sort of regions. All regions have this sort as their type.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Region;

/// An inference variable.
/// May have theoretically any type.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Metavariable<E> {
    pub index: u32,
    /// We store the types of metavariables explicitly, since they can't be inferred.
    pub ty: Box<E>,
}

/// De Bruijn indices (bound variables) are replaced with local constants while we're inside the function body.
/// Should not be used in functions manually.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct LocalConstant<E> {
    /// The position of the name is where it was defined, not where it was used.
    pub name: Name,
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
        Metavariable {
            index: result,
            ty: Box::new(ty),
        }
    }
}

/// The main expression type.
/// The type parameter `E` is the type of sub-expressions.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExpressionT<E> {
    Bound(Bound),
    Inst(Inst),
    Let(Let<E>),
    Borrow(Borrow<E>),
    Lambda(Lambda<E>),
    Pi(Pi<E>),
    Delta(Delta<E>),
    Apply(Apply<E>),
    Sort(Sort),
    Region(Region),
    Metavariable(Metavariable<E>),
    LocalConstant(LocalConstant<E>),
}

pub type TermData = ExpressionT<Term>;

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct Expression(pub WithProvenance<ExpressionT<Expression>>);
