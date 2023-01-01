use std::collections::HashSet;

use fcommon::Path;
use fexpr::expr::*;

use crate::{expr::for_each_term, Db};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Dependencies {
    pub defs: HashSet<Path>,
}

/// Computes the direct dependencies that this expression has on previous definitions.
/// This does not compute *transitive* dependencies.
#[tracing::instrument(level = "debug")]
#[salsa::tracked]
pub fn dependencies(db: &dyn Db, term: Term) -> Dependencies {
    let mut deps = Dependencies::default();
    for_each_term(db, term, |t, _offset| match t.value(db) {
        ExpressionT::Inst(inst) => {
            deps.defs.insert(inst.name.to_path(db));
        }
        ExpressionT::Intro(intro) => deps.defs.insert(intro.inductive.to_path(db)),
        _ => (),
    });
    deps
}
