use std::collections::HashSet;

use fcommon::Path;
use fexpr::expr::*;

use crate::{term::for_each_term, Db};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Dependencies {
    pub defs: HashSet<Path>,
}

/// Computes the direct dependencies that this term has on previous definitions.
/// This does not compute *transitive* dependencies.
#[tracing::instrument(level = "debug")]
#[salsa::tracked]
pub fn dependencies(db: &dyn Db, term: Term) -> Dependencies {
    let mut deps = Dependencies::default();
    for_each_term(db, term, |t, _offset| {
        if let ExpressionT::Inst(inst) = t.value(db) {
            deps.defs.insert(inst.name.to_path(db));
        }
    });
    deps
}
