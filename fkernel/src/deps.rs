use std::collections::HashSet;

use fcommon::{Intern, Path};
use fexpr::expr::*;
use upcast::Upcast;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Dependencies {
    pub defs: HashSet<Path>,
}

impl Dependencies {
    pub fn new_with(path: Path) -> Self {
        Self {
            defs: {
                let mut set = HashSet::new();
                set.insert(path);
                set
            },
        }
    }

    pub fn with(self, other: Self) -> Self {
        Self {
            defs: self.defs.into_iter().chain(other.defs).collect(),
        }
    }
}

#[salsa::query_group(DependencyAnalyserStorage)]
pub trait DependencyAnalyser:
    Intern + TermIntern + Upcast<dyn Intern> + Upcast<dyn TermIntern>
{
    /// Computes the direct dependencies that this term has on previous definitions.
    /// This does not compute *transitive* dependencies.
    fn dependencies(&self, term: Term) -> Dependencies;
}

#[tracing::instrument(level = "debug")]
fn dependencies(db: &dyn DependencyAnalyser, term: Term) -> Dependencies {
    match term.lookup(db.up()) {
        ExpressionT::Bound(_) => Default::default(),
        ExpressionT::Inst(t) => Dependencies::new_with(t.name.to_path(db.up())),
        ExpressionT::Let(t) => db
            .dependencies(t.to_assign_ty)
            .with(db.dependencies(t.body)),
        ExpressionT::Borrow(t) => db.dependencies(t.value),
        ExpressionT::Lambda(t) => db
            .dependencies(t.region)
            .with(db.dependencies(t.parameter_ty))
            .with(db.dependencies(t.result)),
        ExpressionT::RegionLambda(t) => db.dependencies(t.body),
        ExpressionT::Pi(t) => db
            .dependencies(t.region)
            .with(db.dependencies(t.parameter_ty))
            .with(db.dependencies(t.result)),
        ExpressionT::RegionPi(t) => db.dependencies(t.body),
        ExpressionT::LetRegion(t) => db.dependencies(t.body),
        ExpressionT::Delta(t) => db.dependencies(t.region).with(db.dependencies(t.ty)),
        ExpressionT::Apply(t) => db
            .dependencies(t.function)
            .with(db.dependencies(t.argument)),
        ExpressionT::Sort(_) => Default::default(),
        ExpressionT::Region => Default::default(),
        ExpressionT::StaticRegion => Default::default(),
        ExpressionT::Metavariable(t) => db.dependencies(t.ty),
        ExpressionT::LocalConstant(t) => db.dependencies(t.metavariable.ty),
    }
}
