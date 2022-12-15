use fcommon::{Dr, LabelType, Path, ReportKind};
use fexpr::{
    basic::{Name, Provenance, QualifiedName, WithProvenance},
    expr::{largest_unusable_metavariable, Expression, Inst, NaryBinder, Sort},
    inductive::Inductive,
    universe::{Universe, UniverseContents, UniverseVariable},
};

use crate::{
    term::nary_binder_to_pi_expression,
    typeck::{as_sort, check_no_local_or_metavariable, infer_type},
    universe::{is_nonzero, is_zero, normalise_universe},
    Db,
};

use super::get_inductive;

fn largest_unusable_metavariable_in_nary(
    db: &dyn Db,
    nary_binder: NaryBinder<Provenance, Box<Expression>>,
) -> Option<u32> {
    largest_unusable_metavariable(
        db,
        nary_binder_to_pi_expression(Provenance::Synthetic, nary_binder).to_term(db),
    )
}

fn largest_unusable_metavariable_in_inductive(
    db: &dyn Db,
    ind: &Inductive<Provenance, Box<Expression>>,
) -> Option<u32> {
    ind.variants
        .iter()
        .map(|variant| largest_unusable_metavariable_in_nary(db, variant.intro_rule.clone()))
        .chain(std::iter::once(largest_unusable_metavariable_in_nary(
            db,
            ind.ty.clone(),
        )))
        .max()
        .unwrap()
}

/// Some information used when creating things to do with inductives, such as match expressions.
pub(in crate::inductive) struct InductiveTypeInformation<'db> {
    pub inductive: &'db Inductive<Provenance, Box<Expression>>,
    /// The type yielded after all parameters have been applied to the inductive type.
    pub sort: Sort<()>,
    /// An [`Inst`] node which will instantiate the type of the inductive, with the given universe parameters.
    pub inst: Inst<()>,
    /// True if the field `sort` is never the zero universe.
    pub never_zero: bool,
    /// True if we are allowed to perform dependent elimination in match expressions.
    /// This means that the type former can depend on the value of the inductive in question.
    pub dependent_elimination: bool,
}

pub(super) fn check_inductive_type(db: &dyn Db, path: Path) -> Dr<InductiveTypeInformation> {
    get_inductive(db, path).as_ref().bind(|ind| {
        let ind_ty = nary_binder_to_pi_expression(ind.provenance, ind.contents.ty.clone());
        check_no_local_or_metavariable(db, &ind_ty).bind(|()| {
            match infer_type(db, ind_ty.to_term(db)) {
                Ok(_) => {
                    // The type of the inductive is type-correct.
                    if (ind.ty.structures.len() as u32) < ind.global_params {
                        Dr::fail(ind.ty.result.value.provenance
                            .report(ReportKind::Error)
                            .with_message("the amount of declared global parameters is greater than the amount of parameters to the inductive type")
                            .with_label(ind.ty.result.value.provenance.label(LabelType::Error)
                                .with_message(format!(
                                    "the type requires {} global parameters but only {} were supplied",
                                    ind.global_params, ind.ty.structures.len()
                                ))))
                    } else {
                        match as_sort(db, ind.contents.ty.result.to_term(db)) {
                            Ok(sort) => {
                                let sort = Sort(normalise_universe(db, sort.0));
                                let never_zero = is_nonzero(&sort.0);
                                let dependent_elimination = !is_zero(&sort.0);
                                Dr::ok(InductiveTypeInformation {
                                    inductive: ind,
                                    sort,
                                    inst: Inst {
                                        name: QualifiedName::from_path(db, path),
                                        universes: ind.universe_params
                                            .iter()
                                            .map(|univ|
                                                Universe::new(UniverseContents::UniverseVariable(
                                                    UniverseVariable(Name(WithProvenance::new(**univ)))
                                                )))
                                            .collect()
                                    },
                                    never_zero,
                                    dependent_elimination,
                                })
                            },
                            Err(_) => todo!()
                        }
                    }
                }
                Err(_) => todo!(),
            }
        })
    })
}
