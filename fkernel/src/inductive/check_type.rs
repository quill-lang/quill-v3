use crate::{
    basic::{Name, QualifiedName, WithProvenance},
    expr::{Expression, ExpressionCache, Inst, Sort},
    inductive::Inductive,
    result::Dr,
    typeck::check_no_local_or_metavariable,
    universe::{Universe, UniverseContents, UniverseVariable},
};
use fcommon::{LabelType, Path, ReportKind};

use crate::typeck::as_sort;

/// Some information used when creating things to do with inductives, such as match expressions.
pub(in crate::inductive) struct InductiveTypeInformation {
    pub inductive: Inductive,
    /// The type yielded after all parameters have been applied to the inductive type.
    pub sort: Sort,
    /// An [`Inst`] node which will instantiate the type of the inductive, with the given universe parameters.
    pub inst: Inst,
}

pub(super) fn check_inductive_type(
    cache: &ExpressionCache<'_>,
    path: Path,
    ind: &Inductive,
) -> Dr<InductiveTypeInformation> {
    let ind_ty =
        Expression::nary_binder_to_pi(cache, ind.provenance, ind.contents.ty.from_heap(cache));
    check_no_local_or_metavariable(cache, ind_ty).bind(|()| {
            match ind_ty.infer_type(cache) {
                Ok(_) => {
                    // The type of the inductive is type-correct.
                    if (ind.ty.structures.len() as u32) < ind.global_params {
                        Dr::fail(ind.ty.result.value.provenance
                            .report(ReportKind::Error)
                            .with_message("the amount of declared global parameters is greater than the amount of parameters to the inductive type".into())
                            .with_label(ind.ty.result.value.provenance.label(LabelType::Error)
                                .with_message(format!(
                                    "the type requires {} global parameters but only {} were supplied",
                                    ind.global_params, ind.ty.structures.len()
                                ).into())))
                    } else {
                        match as_sort(cache, ind.contents.ty.result.from_heap(cache)) {
                            Ok(sort) => {
                                let sort = Sort(sort.0.normalise_universe(cache.db()));
                                Dr::ok(InductiveTypeInformation {
                                    inductive: ind.clone(),
                                    sort,
                                    inst: Inst {
                                        name: QualifiedName::from_path(cache.db(), path),
                                        universes: ind.universe_params
                                            .iter()
                                            .map(|univ|
                                                Universe::new_synthetic(UniverseContents::UniverseVariable(
                                                    UniverseVariable(Name(WithProvenance::new_synthetic(**univ)))
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
}
