use fkernel::{
    expr::{Expression, ExpressionCache, ExpressionT, Metavariable, ReplaceResult},
    result::Dr,
    universe::{Metauniverse, Universe, UniverseContents},
};
use rpds::RedBlackTreeMap;

use crate::{
    constraint::{
        CategorisedConstraint, Justification, StuckApplicationConstraint, StuckApplicationType,
        UnificationConstraint, UniverseConstraint,
    },
    elaborator::Elaborator,
};

/// A (partial or complete) solution to the problem of instantiating metavariables and metauniverses.
/// This data structure is fast to clone, as its underlying storage uses persistent data structures.
#[derive(Default, Clone)]
pub struct Solution<'cache> {
    map: RedBlackTreeMap<Metavariable<Expression<'cache>>, (Expression<'cache>, Justification)>,
    universes: RedBlackTreeMap<Metauniverse, Universe>,
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
                    univ.instantiate_metauniverses(&|meta| self.universes.get(&meta).cloned());
                }
                ReplaceResult::ReplaceWith(Expression::new(
                    cache,
                    expr.provenance(cache),
                    ExpressionT::Inst(inst),
                ))
            }
            ExpressionT::Sort(mut sort) => {
                sort.0
                    .instantiate_metauniverses(&|meta| self.universes.get(&meta).cloned());
                ReplaceResult::ReplaceWith(Expression::new(
                    cache,
                    expr.provenance(cache),
                    ExpressionT::Sort(sort),
                ))
            }
            ExpressionT::Metavariable(var) => match self.map.get(&var) {
                Some((replacement, _)) => ReplaceResult::ReplaceWith(*replacement),
                None => ReplaceResult::Skip,
            },
            _ => ReplaceResult::Skip,
        })
    }
}

/// The fields of this structure are fast to clone since their underlying storage uses persistent data structures.
struct Solver<'a, 'cache> {
    elab: Elaborator<'a, 'cache>,
    /// A partial solution, mapping metavariables to their relevant expressions.
    solution: Solution<'cache>,

    /// Maps metavariables to the list of constraints on applications that are stuck on the given metavariable.
    /// This is used as a queue of constraints to be solved.
    stuck_applications:
        RedBlackTreeMap<Metavariable<Expression<'cache>>, Vec<StuckApplicationConstraint<'cache>>>,
}

impl<'a, 'cache> Elaborator<'a, 'cache> {
    /// Solves the constraints in the elaborator.
    /// Returns, if successful, a substitution of metavariables to closed expressions.
    pub fn solve(mut self) -> Dr<Solution<'cache>> {
        let constraints = std::mem::take(&mut self.unification_constraints);
        let mut solver = Solver {
            elab: self,
            solution: Default::default(),
            stuck_applications: Default::default(),
        };
        for constraint in constraints {
            solver.add_constraint(constraint);
        }
        solver.solve();
        Dr::ok(solver.solution)
    }
}

impl<'a, 'cache> Solver<'a, 'cache> {
    fn add_constraint(&mut self, constraint: UnificationConstraint<'cache>) {
        // tracing::trace!(
        //     "categorising {} =?= {}",
        //     self.elab.pretty_print(constraint.expected),
        //     self.elab.pretty_print(constraint.actual)
        // );

        // Simplify the unification constraint.
        // This may yield several constraints.
        for constraint in constraint.simplify(&self.elab) {
            match constraint {
                CategorisedConstraint::StuckApplication(stuck_app) => {
                    self.add_stuck_application_constraint(stuck_app);
                }
                CategorisedConstraint::Universe(univ) => {
                    self.add_universe_constraint(univ);
                }
            }
        }
    }

    fn add_stuck_application_constraint(&mut self, stuck_app: StuckApplicationConstraint<'cache>) {
        // Check if a solution for this stuck application is already known.
        match self.solution.map.get(&stuck_app.metavariable) {
            Some((solution, justification)) => {
                // We have solved a constraint for this metavariable already.
                self.add_constraint(UnificationConstraint {
                    expected: solution.create_nary_application(
                        self.elab.cache(),
                        stuck_app.arguments.iter().map(|expr| {
                            (
                                expr.provenance(self.elab.cache()),
                                expr.replace_metavariable(
                                    self.elab.cache(),
                                    stuck_app.metavariable,
                                    *solution,
                                ),
                            )
                        }),
                    ),
                    actual: stuck_app.replacement.replace_metavariable(
                        self.elab.cache(),
                        stuck_app.metavariable,
                        *solution,
                    ),
                    justification: Justification::Join {
                        first: Box::new(justification.clone()),
                        second: Box::new(stuck_app.justification),
                    },
                });
            }
            None => {
                // We did not already solve this constraint.
                match stuck_app.categorise(self.elab.cache()) {
                    StuckApplicationType::Pattern => {
                        // We can solve this constraint immediately.
                        let arguments = stuck_app
                            .arguments
                            .iter()
                            .map(|expr| {
                                if let ExpressionT::LocalConstant(local) =
                                    expr.value(self.elab.cache())
                                {
                                    (expr.provenance(self.elab.cache()), local)
                                } else {
                                    unreachable!("constraint incorrectly categorised")
                                }
                            })
                            .collect::<Vec<_>>();

                        let solution = stuck_app
                            .replacement
                            .abstract_nary_lambda(self.elab.cache(), arguments.into_iter());
                        self.solution.map.insert_mut(
                            stuck_app.metavariable,
                            (solution, stuck_app.justification),
                        );

                        // Assert that the type of the solution matches the type of the metavariable.
                        if let Some(solution_constrained) =
                            self.elab.infer_type_with_constraints(solution).value()
                        {
                            // TODO: Do we need to do anything with `solution_constrained.constraints`?
                            self.add_constraint(UnificationConstraint {
                                expected: stuck_app.metavariable.ty,
                                actual: solution_constrained.expr,
                                justification: Justification::PatternSolution,
                            });
                        } else {
                            // The solution was not correctly typed.
                            todo!()
                        }

                        // We need to revisit all of the constraints that were stuck due to this metavariable.
                        let to_revisit = self
                            .stuck_applications
                            .get(&stuck_app.metavariable)
                            .into_iter()
                            .flatten()
                            .cloned()
                            .collect::<Vec<_>>();
                        self.stuck_applications.remove_mut(&stuck_app.metavariable);
                        for stuck_app in to_revisit {
                            self.add_stuck_application_constraint(stuck_app);
                        }

                        // TODO: Revisit other things like flex-flex and stuck match constraints.
                    }
                    _ => {
                        // We can't solve this constraint immediately.
                        // Add it to the solver's list of stuck application constraints to solve later.
                        match self.stuck_applications.get_mut(&stuck_app.metavariable) {
                            Some(stuck_applications) => {
                                stuck_applications.push(stuck_app);
                            }
                            None => {
                                self.stuck_applications
                                    .insert_mut(stuck_app.metavariable, vec![stuck_app]);
                            }
                        }
                    }
                }
            }
        }
    }

    fn add_universe_constraint(&mut self, univ: UniverseConstraint) {
        // We can often solve universe constraints immediately.
        self.solve_universe_constraint(univ.expected, univ.actual);
    }

    fn solve_universe_constraint(&mut self, expected: Universe, actual: Universe) {
        // We can often solve universe constraints immediately.
        if let UniverseContents::Metauniverse(meta) = expected.contents {
            match self.solution.universes.get(&meta) {
                Some(solution) => return self.solve_universe_constraint(solution.clone(), actual),
                None => {
                    self.solution.universes.insert_mut(meta, actual);
                    return;
                }
            }
        }

        if let UniverseContents::Metauniverse(meta) = actual.contents {
            match self.solution.universes.get(&meta) {
                Some(solution) => {
                    return self.solve_universe_constraint(expected, solution.clone())
                }
                None => {
                    self.solution.universes.insert_mut(meta, expected);
                    return;
                }
            }
        }

        todo!()
    }

    fn solve(&mut self) {
        tracing::debug!(
            "solving constraints for {} metavariables",
            self.stuck_applications.keys().count()
        );
    }
}
