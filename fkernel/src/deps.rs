use std::collections::HashSet;

use fcommon::Path;
use fexpr::expr::*;

use crate::Db;

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

/// Computes the direct dependencies that this term has on previous definitions.
/// This does not compute *transitive* dependencies.
#[salsa::tracked]
#[tracing::instrument(level = "debug")]
pub fn dependencies(db: &dyn Db, term: Term) -> Dependencies {
    match term.value(db) {
        ExpressionT::Bound(_) => Default::default(),
        ExpressionT::Inst(t) => Dependencies::new_with(t.name.to_path(db)),
        ExpressionT::Let(t) => dependencies(db, t.to_assign_ty).with(dependencies(db, t.body)),
        ExpressionT::Borrow(t) => dependencies(db, t.value),
        ExpressionT::Lambda(t) => dependencies(db, t.region)
            .with(dependencies(db, t.parameter_ty))
            .with(dependencies(db, t.result)),
        ExpressionT::RegionLambda(t) => dependencies(db, t.body),
        ExpressionT::Pi(t) => dependencies(db, t.region)
            .with(dependencies(db, t.parameter_ty))
            .with(dependencies(db, t.result)),
        ExpressionT::RegionPi(t) => dependencies(db, t.body),
        ExpressionT::LetRegion(t) => dependencies(db, t.body),
        ExpressionT::Delta(t) => dependencies(db, t.region).with(dependencies(db, t.ty)),
        ExpressionT::Apply(t) => dependencies(db, t.function).with(dependencies(db, t.argument)),
        ExpressionT::Sort(_) => Default::default(),
        ExpressionT::Region => Default::default(),
        ExpressionT::StaticRegion => Default::default(),
        ExpressionT::Metavariable(t) => dependencies(db, t.ty),
        ExpressionT::LocalConstant(t) => dependencies(db, t.metavariable.ty),
    }
}
