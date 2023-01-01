use std::collections::HashSet;

use fcommon::Path;

use crate::expr::*;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Dependencies {
    pub defs: HashSet<Path>,
}

impl<'cache> Expression<'cache> {
    /// Computes the direct dependencies that this expression has on previous definitions.
    /// This does not compute *transitive* dependencies.
    pub fn dependencies(self, cache: &ExpressionCache<'cache>) -> Dependencies {
        let mut deps = Dependencies::default();
        self.for_each_expression(cache, |e, _offset| match e.value(cache) {
            ExpressionT::Inst(inst) => {
                deps.defs.insert(inst.name.to_path(cache.db()));
            }
            ExpressionT::Intro(intro) => {
                deps.defs.insert(intro.inductive.to_path(cache.db()));
            }
            _ => (),
        });
        deps
    }
}
