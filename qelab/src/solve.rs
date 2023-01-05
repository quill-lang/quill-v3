use std::collections::HashMap;

use fkernel::{
    expr::{Expression, ExpressionCache, ExpressionT, Metavariable, ReplaceResult},
    result::Dr,
    universe::{Metauniverse, Universe},
};

use crate::{
    constraint::{CategorisedConstraint, Justification, PatternConstraint, UnificationConstraint},
    elaborator::Elaborator,
};

#[derive(Default)]
pub struct Solution<'cache> {
    map: HashMap<Metavariable<Expression<'cache>>, Expression<'cache>>,
    universes: HashMap<Metauniverse, Universe>,
}

impl<'cache> Solution<'cache> {
    pub fn substitute(
        &self,
        cache: &ExpressionCache<'cache>,
        expr: Expression<'cache>,
    ) -> Expression<'cache> {
        expr.replace_in_expression(cache, &|expr, _offset| match expr.value(cache) {
            ExpressionT::Inst(mut inst) => {
                for univ in &mut inst.universes {
                    univ.instantiate_metauniverses(&self.universes);
                }
                ReplaceResult::ReplaceWith(Expression::new(
                    cache,
                    expr.provenance(cache),
                    ExpressionT::Inst(inst),
                ))
            }
            ExpressionT::Sort(mut sort) => {
                sort.0.instantiate_metauniverses(&self.universes);
                ReplaceResult::ReplaceWith(Expression::new(
                    cache,
                    expr.provenance(cache),
                    ExpressionT::Sort(sort),
                ))
            }
            ExpressionT::Metavariable(var) => match self.map.get(&var) {
                Some(replacement) => ReplaceResult::ReplaceWith(*replacement),
                None => ReplaceResult::Skip,
            },
            _ => ReplaceResult::Skip,
        })
    }
}

struct Solver<'a, 'cache> {
    elab: Elaborator<'a, 'cache>,
    /// A partial solution, mapping metavariables to their relevant expressions.
    solution: Solution<'cache>,

    pattern_constraints: Vec<(PatternConstraint<'cache>, Justification)>,
}

impl<'a, 'cache> Elaborator<'a, 'cache> {
    /// Solves the constraints in the elaborator.
    /// Returns, if successful, a substitution of metavariables to closed expressions.
    pub fn solve(mut self) -> Dr<Solution<'cache>> {
        let constraints = std::mem::take(&mut self.unification_constraints);
        let mut solver = Solver {
            elab: self,
            solution: Default::default(),
            pattern_constraints: Default::default(),
        };
        solver.add_constraints(constraints);
        solver.solve();
        Dr::ok(solver.solution)
    }
}

impl<'a, 'cache> Solver<'a, 'cache> {
    fn add_constraints(
        &mut self,
        constraints: impl IntoIterator<Item = UnificationConstraint<'cache>>,
    ) {
        for constraint in constraints {
            tracing::trace!(
                "categorising {} =?= {}",
                self.elab.pretty_print(constraint.expected),
                self.elab.pretty_print(constraint.actual)
            );
            for (constraint, justification) in constraint.simplify(self.elab.cache()) {
                match constraint {
                    CategorisedConstraint::Pattern(pattern) => {
                        self.pattern_constraints.push((pattern, justification));
                    }
                }
            }
        }
    }

    fn solve(&mut self) {
        // This is a very basic procedure to solve constraints.
        for (pattern, justification) in std::mem::take(&mut self.pattern_constraints) {
            let solution = pattern
                .replacement
                .abstract_nary_lambda(self.elab.cache(), pattern.arguments.into_iter());
            self.solution.map.insert(pattern.metavariable, solution);
        }
    }
}
