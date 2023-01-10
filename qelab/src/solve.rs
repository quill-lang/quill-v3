use fkernel::{
    expr::{Expression, ExpressionCache, ExpressionT, HoleId, ReplaceResult},
    result::Dr,
    universe::{Metauniverse, Universe, UniverseContents},
};
use rpds::RedBlackTreeMap;

use crate::{
    constraint::{
        CategorisedConstraint, FlexFlexConstraint, Justification, StuckApplicationConstraint,
        StuckApplicationType, UnificationConstraint, UniverseConstraint,
    },
    elaborator::Elaborator,
};

/// A (partial or complete) solution to the problem of instantiating metavariables and metauniverses.
/// This data structure is fast to clone, as its underlying storage uses persistent data structures.
#[derive(Default, Clone)]
pub struct Solution<'cache> {
    map: RedBlackTreeMap<HoleId, (Expression<'cache>, Justification<'cache>)>,
    universes: RedBlackTreeMap<Metauniverse, Universe>,
}

impl<'cache> Solution<'cache> {
    /// Applies the solution to the given expression.
    /// This may fill holes.
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
            ExpressionT::Hole(hole) => match self.map.get(&hole.id) {
                Some((replacement, _)) => {
                    // Since substitution is not idempotent in the current implementation,
                    // we need to perform a substitution operation on the solution to make sure it doesn't contain metavariables.
                    ReplaceResult::ReplaceWith(
                        self.substitute(cache, expr.fill_hole(cache, hole.id, *replacement)),
                    )
                }
                None => ReplaceResult::Skip,
            },
            _ => ReplaceResult::Skip,
        })
    }
}

/// The fields of this structure are fast to clone since their underlying storage uses persistent data structures.
struct Solver<'a, 'cache> {
    elab: Elaborator<'a, 'cache>,
    /// A partial solution, mapping hole IDs to their relevant expressions.
    solution: Solution<'cache>,

    /// Maps hole IDs to the list of constraints on applications that are stuck on the given metavariable.
    /// This is used as a queue of constraints to be solved.
    stuck_applications: RedBlackTreeMap<HoleId, Vec<StuckApplicationConstraint<'cache>>>,
    /// Maps pairs of hole IDs to the list of flex-flex constraints that are stuck on both variables.
    flex_flex: RedBlackTreeMap<(HoleId, HoleId), Vec<FlexFlexConstraint<'cache>>>,
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
            flex_flex: Default::default(),
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
        #[cfg(feature = "elaborator_diagnostics")]
        tracing::trace!(
            "categorising {} =?= {} because {}",
            self.elab.pretty_print(constraint.expected),
            self.elab.pretty_print(constraint.actual),
            constraint.justification.display(&self.elab),
        );

        // Simplify the unification constraint.
        // This may yield several constraints.
        for constraint in constraint.simplify(&self.elab) {
            match constraint {
                CategorisedConstraint::StuckApplication(stuck_app) => {
                    self.add_stuck_application_constraint(stuck_app);
                }
                CategorisedConstraint::FlexFlex(flex_flex) => {
                    self.add_flex_flex_constraint(flex_flex);
                }
                CategorisedConstraint::Universe(univ) => {
                    self.add_universe_constraint(univ);
                }
            }
        }
    }

    fn add_stuck_application_constraint(&mut self, stuck_app: StuckApplicationConstraint<'cache>) {
        // Check if a solution for this stuck application is already known.
        match self.solution.map.get(&stuck_app.hole.id) {
            Some((solution, justification)) => {
                #[cfg(feature = "elaborator_diagnostics")]
                tracing::trace!(
                    "already found solution for {}: {}",
                    stuck_app.hole.id,
                    self.elab.pretty_print(*solution),
                );

                // We have solved a constraint for this metavariable already.
                let hole_solution = stuck_app
                    .hole
                    .args
                    .iter()
                    .rev()
                    .fold(*solution, |acc, e| acc.instantiate(self.elab.cache(), *e));
                self.add_constraint(UnificationConstraint {
                    expected: hole_solution.create_nary_application(
                        self.elab.cache(),
                        stuck_app.arguments.iter().map(|expr| {
                            (
                                expr.provenance(self.elab.cache()),
                                expr.fill_hole(self.elab.cache(), stuck_app.hole.id, *solution),
                            )
                        }),
                    ),
                    actual: stuck_app.replacement.fill_hole(
                        self.elab.cache(),
                        stuck_app.hole.id,
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
                        let all_args = stuck_app
                            .hole
                            .args
                            .iter()
                            .chain(&stuck_app.arguments)
                            .map(|expr| {
                                // The arguments to the hole should be local constants, because it is a "pattern" stuck application.
                                if let ExpressionT::LocalConstant(local) =
                                    expr.value(self.elab.cache())
                                {
                                    local
                                } else {
                                    panic!()
                                }
                            })
                            .collect::<Vec<_>>();

                        // We solve the constraint by abstracting the result as a function taking every argument provided.
                        // This gives the closed-expression form of the solution.
                        let solution_closed = stuck_app.replacement.abstract_nary_lambda(
                            self.elab.cache(),
                            all_args.iter().map(|local| {
                                (stuck_app.replacement.provenance(self.elab.cache()), *local)
                            }),
                        );

                        // Since some of the arguments are given in the hole, we need to remove those arguments from being counted.
                        // We do this by simply moving inside the relevant binders.
                        // This gives the free form of the solution.
                        let solution_free =
                            stuck_app
                                .hole
                                .args
                                .iter()
                                .fold(solution_closed, |solution, _| {
                                    if let ExpressionT::Lambda(lambda) =
                                        solution.value(self.elab.cache())
                                    {
                                        lambda.result
                                    } else {
                                        unreachable!()
                                    }
                                });

                        // We create a form of the solution where the free variables are replaced with the locals from the hole.
                        let solution_locals = stuck_app
                            .hole
                            .args
                            .iter()
                            .rev()
                            .fold(solution_free, |acc, e| {
                                acc.instantiate(self.elab.cache(), *e)
                            });

                        self.solution.map.insert_mut(
                            stuck_app.hole.id,
                            (solution_free, stuck_app.justification),
                        );

                        #[cfg(feature = "elaborator_diagnostics")]
                        tracing::trace!(
                            "solved {} = {}",
                            self.elab.pretty_print(Expression::new(
                                self.elab.cache(),
                                fkernel::basic::Provenance::Synthetic,
                                ExpressionT::Hole(stuck_app.hole.clone())
                            )),
                            self.elab.pretty_print(solution_locals),
                        );

                        // Assert that the type of the solution matches the type of the metavariable.
                        if let Some(solution_constrained) = self
                            .elab
                            .infer_type_with_constraints(solution_locals)
                            .value()
                        {
                            #[cfg(feature = "elaborator_diagnostics")]
                            tracing::trace!(
                                "constrained type was {}",
                                self.elab.pretty_print(solution_constrained.expr)
                            );
                            // TODO: Do we need to do anything with `solution_constrained.constraints`?
                            self.add_constraint(UnificationConstraint {
                                expected: stuck_app
                                    .arguments
                                    .iter()
                                    .fold(stuck_app.hole.ty, |acc, e| {
                                        acc.instantiate(self.elab.cache(), *e)
                                    }),
                                actual: solution_constrained.expr,
                                justification: Justification::PatternSolution,
                            });
                        } else {
                            // The solution was not correctly typed.
                            todo!()
                        }

                        // We need to revisit all of the constraints that were stuck due to this metavariable.
                        // Revisit stuck applications, which are now solved.
                        let to_revisit = self
                            .stuck_applications
                            .get(&stuck_app.hole.id)
                            .into_iter()
                            .flatten()
                            .cloned()
                            .collect::<Vec<_>>();
                        self.stuck_applications.remove_mut(&stuck_app.hole.id);
                        for stuck_app in to_revisit {
                            self.add_stuck_application_constraint(stuck_app);
                        }

                        // Revisit flex-flex constraints, which are now only stuck applications.
                        let mut to_revisit = Vec::new();
                        let mut keys_to_remove = Vec::new();
                        for key in self.flex_flex.keys() {
                            if key.0 == stuck_app.hole.id || key.1 == stuck_app.hole.id {
                                to_revisit
                                    .extend(self.flex_flex.get(key).into_iter().flatten().cloned());
                                keys_to_remove.push(*key);
                            }
                        }
                        for key in keys_to_remove {
                            self.flex_flex.remove_mut(&key);
                        }
                        for flex_flex in to_revisit {
                            self.add_flex_flex_constraint(flex_flex);
                        }

                        // TODO: Revisit other things like stuck match constraints.
                    }
                    _ => {
                        // We can't solve this constraint immediately.
                        // Add it to the solver's list of stuck application constraints to solve later.
                        match self.stuck_applications.get_mut(&stuck_app.hole.id) {
                            Some(stuck_applications) => {
                                stuck_applications.push(stuck_app);
                            }
                            None => {
                                self.stuck_applications
                                    .insert_mut(stuck_app.hole.id, vec![stuck_app]);
                            }
                        }
                    }
                }
            }
        }
    }

    fn add_flex_flex_constraint(&mut self, flex_flex: FlexFlexConstraint<'cache>) {
        // Check if a solution for this stuck application is already known.
        if self.solution.map.contains_key(&flex_flex.expected.id) {
            // We have solved a constraint for this metavariable already.
            // Recategorise this constraint as a stuck application and solve it.
            self.add_stuck_application_constraint(StuckApplicationConstraint {
                hole: flex_flex.expected,
                arguments: flex_flex.expected_arguments,
                replacement: Expression::new(
                    self.elab.cache(),
                    flex_flex.actual.ty.provenance(self.elab.cache()),
                    ExpressionT::Hole(flex_flex.actual),
                )
                .create_nary_application(
                    self.elab.cache(),
                    flex_flex
                        .actual_arguments
                        .into_iter()
                        .map(|expr| (expr.provenance(self.elab.cache()), expr)),
                ),
                justification: flex_flex.justification,
            });
        } else if self.solution.map.contains_key(&flex_flex.actual.id) {
            self.add_stuck_application_constraint(StuckApplicationConstraint {
                hole: flex_flex.actual,
                arguments: flex_flex.actual_arguments,
                replacement: Expression::new(
                    self.elab.cache(),
                    flex_flex.expected.ty.provenance(self.elab.cache()),
                    ExpressionT::Hole(flex_flex.expected),
                )
                .create_nary_application(
                    self.elab.cache(),
                    flex_flex
                        .expected_arguments
                        .into_iter()
                        .map(|expr| (expr.provenance(self.elab.cache()), expr)),
                ),
                justification: flex_flex.justification,
            });
        } else {
            // We can't solve this constraint immediately.
            // Add it to the solver's list of flex-flex constraints to solve later.
            match self
                .flex_flex
                .get_mut(&(flex_flex.expected.id, flex_flex.actual.id))
            {
                Some(constraints) => {
                    constraints.push(flex_flex);
                }
                None => {
                    self.flex_flex.insert_mut(
                        (flex_flex.expected.id, flex_flex.actual.id),
                        vec![flex_flex],
                    );
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
        #[cfg(feature = "elaborator_diagnostics")]
        tracing::debug!(
            "solving constraints for {} metavariables",
            self.stuck_applications.keys().count() + self.flex_flex.keys().count()
        );
    }
}
