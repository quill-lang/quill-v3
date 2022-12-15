use fcommon::{Dr, LabelType, Path, ReportKind};
use fexpr::{
    basic::{Name, Provenance, QualifiedName, WithProvenance},
    expr::{Expression, Inst, Sort},
    inductive::Inductive,
    universe::{Universe, UniverseContents, UniverseVariable},
};

use crate::{
    term::nary_binder_to_pi_expression,
    typeck::{as_sort, check_no_local_or_metavariable, infer_type},
    universe::normalise_universe,
    Db,
};

use super::get_inductive;

/// Some information used when creating things to do with inductives, such as match expressions.
pub(in crate::inductive) struct InductiveTypeInformation<'db> {
    pub inductive: &'db Inductive<Provenance, Box<Expression>>,
    /// The type yielded after all parameters have been applied to the inductive type.
    pub sort: Sort<()>,
    /// An [`Inst`] node which will instantiate the type of the inductive, with the given universe parameters.
    pub inst: Inst<()>,
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
