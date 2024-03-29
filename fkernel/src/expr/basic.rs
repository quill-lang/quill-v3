//! # Expressions and terms
//!
//! TODO: Rewrite this documentation.
//!
//! A term is a feather value. An expression is a term with provenance data; it tracks where expressions were written in code.
//! Expressions should be used for user-provided data, and things like type checking where we want to be able to output error messages at precise locations.
//! Expressions should be used for things like kernel computation and code generation, where we either discard provenance data, or it is not relevant.
//!
//! ## Type parameters
//!
//! Throughout this file, we work under the assumption that we have a type variable `E` representing an expression type.
//! Most commonly, this will be [`Expression`] or [`Expression`].
//! We then construct the type [`ExpressionT`], generic over this parameter `E`.
//! This allows us to write functions that are generic over both [`Expression`] and [`Expression`].
//!
//! ## Interning
//!
//! Expressions can be interned by salsa, as they have no provenance information.
//! Since [`ExpressionT<Expression>`] is parametrised by the interned `Expression` type, when we look up an interned term value, we only 'unbox' one level at a time.
//! This improves efficiency, and allows us to cache various results about many small terms, such as their type.

use std::{
    cell::{Cell, RefCell},
    collections::{hash_map::Entry, HashMap},
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
};

use fcommon::{Span, Spanned};
use serde::{Deserialize, Serialize};

use crate::{
    basic::*,
    multiplicity::ParameterOwnership,
    universe::{Metauniverse, MetauniverseGenerator, Universe, UniverseContents, UniverseSucc},
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

/// Dereference a borrowed value.
/// In valid programs, the type of the borrowed value must be dereferencable.
/// However, we don't make this restriction yet.
/// This allows us to (for example) make `*&a` definitionally equal to `a` for all `a`.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Dereference<E> {
    /// The value to be dereferenced.
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
pub struct Inst {
    pub name: QualifiedName,
    pub universes: Vec<Universe>,
}

/// A bound variable in a lambda, pi, let, or lifespan expression.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BoundVariable<E> {
    /// The name of the local variable to bind.
    pub name: Name,
    /// The type of the value assigned to the bound variable.
    pub ty: E,
    /// The multiplicity for which the value is bound.
    pub ownership: ParameterOwnership,
}

impl BoundVariable<HeapExpression> {
    pub fn from_heap<'cache>(
        &self,
        cache: &ExpressionCache<'cache>,
    ) -> BoundVariable<Expression<'cache>> {
        BoundVariable {
            name: self.name,
            ty: self.ty.from_heap(cache),
            ownership: self.ownership,
        }
    }
}

impl<'cache> BoundVariable<Expression<'cache>> {
    pub fn to_heap(self, cache: &ExpressionCache<'cache>) -> BoundVariable<HeapExpression> {
        BoundVariable {
            name: self.name,
            ty: self.ty.to_heap(cache),
            ownership: self.ownership,
        }
    }
}

#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Let<E> {
    /// The local variable to bind.
    pub bound: BoundVariable<E>,
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

/// How should the function be called?
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum FunctionOwnership {
    /// The function is to be called exactly once.
    Once,
    /// The function can be called arbitrarily many times, from behind a borrow.
    /// Such functions can be dropped (as in [`Drop`]).
    Many,
}

#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BinderStructure<E> {
    /// The local variable to bind.
    pub bound: BoundVariable<E>,
    /// How the parameter should be filled when calling the function.
    pub binder_annotation: BinderAnnotation,
    /// How the function should be called.
    pub function_ownership: FunctionOwnership,
    /// The region for which the function may be owned.
    pub region: E,
}

impl BinderStructure<HeapExpression> {
    pub fn from_heap<'cache>(
        &self,
        cache: &ExpressionCache<'cache>,
    ) -> BinderStructure<Expression<'cache>> {
        BinderStructure {
            bound: self.bound.from_heap(cache),
            binder_annotation: self.binder_annotation,
            function_ownership: self.function_ownership,
            region: self.region.from_heap(cache),
        }
    }
}

impl<'cache> BinderStructure<Expression<'cache>> {
    pub fn to_heap(&self, cache: &ExpressionCache<'cache>) -> BinderStructure<HeapExpression> {
        BinderStructure {
            bound: self.bound.to_heap(cache),
            binder_annotation: self.binder_annotation,
            function_ownership: self.function_ownership,
            region: self.region.to_heap(cache),
        }
    }
}

/// Either a lambda abstraction or the type of such lambda abstractions.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Binder<E> {
    /// The structure of the binder.
    pub structure: BinderStructure<E>,
    /// The result.
    /// If this is a lambda abstraction, this is the lambda term.
    /// If this is a function type, this is the type of the function's body.
    pub result: E,
}

/// A [`Binder`] that takes an arbitrary amount of parameters, including zero.
/// Each binder may depend on the previous ones.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct NaryBinder<E> {
    /// The structures of each successive binder.
    pub structures: Vec<BinderStructure<E>>,
    /// The result.
    /// If this is a lambda abstraction, this is the lambda term.
    /// If this is a function type, this is the type of the function's body.
    pub result: E,
}

impl NaryBinder<HeapExpression> {
    pub fn from_heap<'cache>(
        &self,
        cache: &ExpressionCache<'cache>,
    ) -> NaryBinder<Expression<'cache>> {
        NaryBinder {
            structures: self
                .structures
                .iter()
                .map(|structure| structure.from_heap(cache))
                .collect(),
            result: self.result.from_heap(cache),
        }
    }
}

impl<'cache> NaryBinder<Expression<'cache>> {
    pub fn to_heap(&self, cache: &ExpressionCache<'cache>) -> NaryBinder<HeapExpression> {
        NaryBinder {
            structures: self
                .structures
                .iter()
                .map(|structure| structure.to_heap(cache))
                .collect(),
            result: self.result.to_heap(cache),
        }
    }
}

/// A region-polymorphic value, or the type of such values.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct RegionBinder<E> {
    /// The name of the parameter.
    pub region_name: Name,
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
pub struct Intro<E> {
    /// The inductive that we are constructing.
    pub inductive: QualifiedName,
    /// The universe parameters on the inductive.
    pub universes: Vec<Universe>,
    /// The name of the variant we are constructing.
    pub variant: Name,
    /// The parameters we supply to the introduction rule.
    /// This is the sequence of global parameters, followed by the list of fields.
    pub parameters: Vec<E>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct MinorPremise<E> {
    /// The variant that this minor premise operates on.
    pub variant: Name,
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
pub struct Match<E> {
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
    pub minor_premises: Vec<MinorPremise<E>>,
}

/// The fixed point construction on inductive data types.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Fix<E> {
    /// The concrete argument to instantiate the parameter to the fixed point construction with.
    /// We supply this here, instead of making [`Fix`] return a function, to avoid issues with lifetimes.
    pub argument: E,
    /// The name supplied to the argument to the fixed point construction.
    pub argument_name: Name,
    /// The local variable to be constructed by a fixed point process.
    /// The parameter is bound at index 0 in this expression.
    pub fixpoint: BoundVariable<E>,
    /// The main body of the fixed point expression.
    /// The parameter is bound at index 0 and the function `parameter -> fixpoint` is bound at index 1 in this expression.
    /// The parameter `fixpoint` should only be invoked with structurally smaller parameters.
    /// The type of this expression should be `fixpoint.ty`.
    pub body: E,
}

/// Represents the universe of types corresponding to the given universe.
/// For example, if the universe is `0`, this is `Prop`, the type of propositions.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sort(pub Universe);

/// The maximum possible lifespan of a type.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Lifespan<E> {
    /// The type we are analysing the lifespan of.
    pub ty: E,
}

/// An identifier for a hole.
/// These are considered unique for a particular [`ExpressionCache`].
/// When a hole is filled, all holes with this ID are processed in the same way.
///
/// An [`Ord`] implementation is provided to aid with determinism.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HoleId(pub u32);

impl Display for HoleId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{}", self.0)
    }
}

/// An inference variable.
/// May have theoretically any type.
/// Also called a *metavariable*, although this name is sometimes reserved for holes with no arguments.
///
/// When the metavariable is instantiated with an expression `expr`, we instantiate `expr` with `args`, and
/// replace this expression with the result. This result should always be a closed expression.
/// This approach to metavariables allows us to avoid using pi types and function application unnecessarily,
/// which is helpful when reasoning about regions, which behave weirdly with functions.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Hole<E> {
    /// An index for this metavariable.
    /// This is unique for a particular [`ExpressionCache`].
    /// When a hole is filled, all holes with this ID are processed in the same way.
    pub id: HoleId,
    /// A list of arguments to the metavariable.
    /// The value and type of the hole should be closed expressions, once instantiated with `args`.
    ///
    /// These arguments should either be bound variables or local constants, all of which must be distinct.
    pub args: Vec<E>,
    /// The type of this hole, which is evaluated in the context of `args`.
    pub ty: E,
}

/// An identifier for a local constant.
/// These are considered unique for a particular [`ExpressionCache`].
///
/// An [`Ord`] implementation is provided to aid with determinism.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalConstantId(pub u32);

/// De Bruijn indices (bound variables) are replaced with local constants while we're inside the function body.
/// Should not be used in functions manually.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct LocalConstant<E> {
    /// An id created to ensure that local constants with the same name are not considered equal.
    /// All local constants with the same `id` must have the same `structure`, modulo filling holes or instantiating bound variables.
    pub id: LocalConstantId,
    /// The structure of the binder that introduced this local constant.
    /// This field provides the type of this variable.
    pub structure: BinderStructure<E>,
}

/// Generates unique hole and local constant IDs.
pub struct MetavariableGenerator<E> {
    _phantom: std::marker::PhantomData<E>,
    next_hole: HoleId,
    next_local: LocalConstantId,
}

impl<E> MetavariableGenerator<E> {
    /// Creates a new variable generator.
    /// Its hole IDs will all be greater than the provided largest used ID, and the same holds for local constant IDs.
    /// If one was not provided, no guarantees are made about name clashing.
    pub fn new(largest_hole: Option<HoleId>, largest_local: Option<LocalConstantId>) -> Self {
        Self {
            _phantom: Default::default(),
            next_hole: largest_hole.map_or(HoleId(0), |x| HoleId(x.0 + 1)),
            next_local: largest_local.map_or(LocalConstantId(0), |x| LocalConstantId(x.0 + 1)),
        }
    }

    pub fn gen_hole(&mut self, args: Vec<E>, ty: E) -> Hole<E> {
        let result = self.next_hole;
        self.next_hole.0 += 1;
        Hole {
            id: result,
            args,
            ty,
        }
    }

    pub fn gen_local(&mut self, structure: BinderStructure<E>) -> LocalConstant<E> {
        let result = self.next_local;
        self.next_local.0 += 1;
        LocalConstant {
            id: result,
            structure,
        }
    }
}

/// The main expression type.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExpressionT<E> {
    Local(Local),
    Borrow(Borrow<E>),
    Dereference(Dereference<E>),
    Delta(Delta<E>),
    Inst(Inst),
    Let(Let<E>),
    Lambda(Binder<E>),
    Pi(Binder<E>),
    RegionLambda(RegionBinder<E>),
    RegionPi(RegionBinder<E>),
    Apply(Apply<E>),
    Intro(Intro<E>),
    Match(Match<E>),
    Fix(Fix<E>),
    Sort(Sort),
    Region,
    /// The type of [`ExpressionT::Region`], and the type of itself.
    RegionT,
    StaticRegion,
    Lifespan(Lifespan<E>),
    Hole(Hole<E>),
    /// A hole that has type `Region`.
    /// These are allowed to be unfilled until the borrow checking stage.
    /// TODO: Establish a contract for the use of this variant to speed up certain kernel operations by assuming facts about region holes.
    RegionHole(Hole<E>),
    LocalConstant(LocalConstant<E>),
}

/// Caches values and properties of expressions.
///
/// This is intended to be used on a more granular level than `salsa` queries:
/// when a query is executed, we create and manipulate a cache.
/// Then, when the query ends, we can safely destroy the cache.
pub struct ExpressionCache<'cache> {
    db: &'cache dyn Db,
    next_id: Cell<u64>,
    meta_gen: RefCell<MetavariableGenerator<Expression<'cache>>>,
    metauniverse_gen: RefCell<MetauniverseGenerator>,
    /// Maps from expressions to their IDs.
    /// Inverse to `expressions`.
    ids: RefCell<HashMap<WithProvenance<ExpressionT<Expression<'cache>>>, Expression<'cache>>>,
    /// Maps from IDs to the expressions they represent.
    /// Inverse to `ids`.
    expressions:
        RefCell<HashMap<Expression<'cache>, WithProvenance<ExpressionT<Expression<'cache>>>>>,

    /// Memoised results of `largest_hole`.
    pub(crate) largest_hole: RefCell<HashMap<Expression<'cache>, Option<HoleId>>>,
    /// Memoised results of `first_free_variable_index`.
    pub(crate) first_free_variable_index: RefCell<HashMap<Expression<'cache>, DeBruijnIndex>>,
}

impl<'cache> ExpressionCache<'cache> {
    /// Uses branded types to ensure that expressions generated by one cache are never used in another.
    /// See <https://plv.mpi-sws.org/rustbelt/ghostcell/paper.pdf> for more information about this technique.
    pub fn with_cache<R>(
        db: &dyn Db,
        largest_hole: Option<HoleId>,
        largest_local: Option<LocalConstantId>,
        largest_unusable_universe: Option<u32>,
        f: impl for<'a> FnOnce(&ExpressionCache<'a>) -> R,
    ) -> R {
        f(&ExpressionCache {
            db,
            next_id: Cell::new(0),
            meta_gen: RefCell::new(MetavariableGenerator::new(largest_hole, largest_local)),
            metauniverse_gen: RefCell::new(MetauniverseGenerator::new(largest_unusable_universe)),
            ids: Default::default(),
            expressions: Default::default(),
            largest_hole: Default::default(),
            first_free_variable_index: Default::default(),
        })
    }

    pub fn db(&self) -> &dyn Db {
        self.db
    }

    pub fn gen_hole(
        &self,
        args: Vec<Expression<'cache>>,
        ty: Expression<'cache>,
    ) -> Hole<Expression<'cache>> {
        self.meta_gen.borrow_mut().gen_hole(args, ty)
    }

    pub fn gen_local(
        &self,
        structure: BinderStructure<Expression<'cache>>,
    ) -> LocalConstant<Expression<'cache>> {
        self.meta_gen.borrow_mut().gen_local(structure)
    }

    pub fn gen_region_local(
        &self,
        binder: RegionBinder<Expression<'cache>>,
    ) -> LocalConstant<Expression<'cache>> {
        self.gen_local(BinderStructure {
            bound: BoundVariable {
                name: binder.region_name,
                ty: Expression::new(self, binder.region_name.0.provenance, ExpressionT::Region),
                ownership: ParameterOwnership::PCopyable,
            },
            function_ownership: FunctionOwnership::Once,
            binder_annotation: BinderAnnotation::Explicit,
            region: Expression::new(
                self,
                binder.region_name.0.provenance,
                ExpressionT::StaticRegion,
            ),
        })
    }

    pub fn gen_metauniverse(&self) -> Metauniverse {
        self.metauniverse_gen.borrow_mut().gen()
    }
}

/// An ID for an expression, tied to an [`ExpressionCache`] by the `'cache` lifetime.
/// See also [`HeapExpression`].
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Expression<'cache> {
    _phantom: PhantomData<&'cache ()>,
    id: u64,
}

impl<'cache> Debug for Expression<'cache> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.id)
    }
}

/// An expression, stored entirely on the heap.
/// This doesn't use an [`ExpressionCache`], so it can be used as an input or output of a `salsa` query.
/// See also [`Expression`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeapExpression {
    pub value: WithProvenance<Box<ExpressionT<HeapExpression>>>,
}

impl<'cache> Expression<'cache> {
    /// Creates a new [`Expression`] with the given value.
    /// If an expression with this body was already cached, return the cached [`Expression`].
    /// Note that expressions with differing provenance are considered different.
    pub fn new(
        cache: &ExpressionCache<'cache>,
        provenance: Provenance,
        value: ExpressionT<Expression<'cache>>,
    ) -> Self {
        let value = WithProvenance::new(provenance, value);
        match cache.ids.borrow_mut().entry(value.clone()) {
            Entry::Occupied(occupied) => *occupied.get(),
            Entry::Vacant(vacant) => {
                let id = cache.next_id.get();
                let e = Expression {
                    _phantom: PhantomData,
                    id,
                };
                cache.next_id.replace(id + 1);
                cache.expressions.borrow_mut().insert(e, value);
                vacant.insert(e);
                e
            }
        }
    }

    pub fn provenance(self, cache: &ExpressionCache<'cache>) -> Provenance {
        cache
            .expressions
            .borrow()
            .get(&self)
            .expect("expression not found in cache")
            .provenance
    }

    pub fn span(self, cache: &ExpressionCache<'cache>) -> Span {
        self.provenance(cache).span()
    }

    pub fn value(self, cache: &ExpressionCache<'cache>) -> ExpressionT<Expression<'cache>> {
        cache
            .expressions
            .borrow()
            .get(&self)
            .expect("expression not found in cache")
            .contents
            .clone()
    }
}

impl HeapExpression {
    pub fn new(provenance: Provenance, contents: ExpressionT<HeapExpression>) -> Self {
        Self {
            value: WithProvenance {
                provenance,
                contents: Box::new(contents),
            },
        }
    }
}

impl Serialize for HeapExpression {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.value.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for HeapExpression {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        WithProvenance::deserialize(deserializer).map(|value| Self { value })
    }
}

impl HeapExpression {
    /// We use [`ron`] to provide nice debug output for terms.
    pub fn display(&self, db: &dyn Db) -> String {
        fcommon::with_local_database(db, || {
            ron::ser::to_string_pretty(self, ron::ser::PrettyConfig::default()).unwrap()
        })
    }
}

impl<'cache> Expression<'cache> {
    /// Returns the sort of proof-irrelevant propositions.
    pub fn sort_prop(cache: &ExpressionCache<'cache>) -> Self {
        Self::new(
            cache,
            Provenance::Synthetic,
            ExpressionT::Sort(Sort(Universe::new_synthetic(
                UniverseContents::UniverseZero,
            ))),
        )
    }

    /// Returns the sort of small types.
    pub fn sort_type(cache: &ExpressionCache<'cache>) -> Self {
        Self::new(
            cache,
            Provenance::Synthetic,
            ExpressionT::Sort(Sort(Universe::new_synthetic(
                UniverseContents::UniverseSucc(UniverseSucc(Box::new(Universe::new_synthetic(
                    UniverseContents::UniverseZero,
                )))),
            ))),
        )
    }

    /// Returns the sort of regions.
    pub fn region(cache: &ExpressionCache<'cache>) -> Self {
        Self::new(cache, Provenance::Synthetic, ExpressionT::Region)
    }

    /// Returns the static region.
    pub fn static_region(cache: &ExpressionCache<'cache>) -> Self {
        Self::new(cache, Provenance::Synthetic, ExpressionT::StaticRegion)
    }
}

/// An expression is *stuck* if computation cannot continue without filling a hole.
#[derive(Debug)]
pub enum StuckExpression<'cache> {
    /// An expression is a stuck application if its [head symbol](Expression::head) is a hole,
    /// or a borrow of a hole.
    /// If the given hole is instantiated with an unstuck expression,
    /// the expression will no longer be stuck.
    Application(Hole<Expression<'cache>>),
    /// An expression is a stuck match if it is a match, where the major premise is stuck.
    /// If the given hole is instantiated with an unstuck expression,
    /// the expression will no longer be stuck.
    Match(Hole<Expression<'cache>>),
}

impl<'cache> Expression<'cache> {
    /// If the expression is stuck, return the reason why.
    pub fn stuck(self, cache: &ExpressionCache<'cache>) -> Option<StuckExpression<'cache>> {
        if let ExpressionT::Match(match_expr) = self.value(cache) {
            return match_expr.major_premise.stuck(cache);
        }
        match self.head(cache).value(cache) {
            ExpressionT::Hole(hole) | ExpressionT::RegionHole(hole) => {
                Some(StuckExpression::Application(hole))
            }
            ExpressionT::Borrow(borrow) => {
                if let ExpressionT::Hole(hole) | ExpressionT::RegionHole(hole) =
                    borrow.value.value(cache)
                {
                    Some(StuckExpression::Application(hole))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}
