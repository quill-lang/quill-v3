use fcommon::Path;

use crate::{
    basic::Provenance,
    expr::{Expression, ExpressionCache, ExpressionT},
    inductive::Inductive,
    result::Dr,
    typeck::{as_sort, Ir},
    Db,
};

use super::check_type::InductiveTypeInformation;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedInductive {
    pub inductive: Inductive,
    /// True if the motive for any match statement must be a proposition.
    pub eliminate_only_into_prop: bool,
}

/// Returns true if the the motive in match expressions can live in `Prop`.
fn eliminate_only_into_prop(
    cache: &ExpressionCache<'_>,
    info: &InductiveTypeInformation,
) -> Ir<bool> {
    if info.sort.0.is_nonzero() {
        // The resultant inductive datatype is never in `Prop`, so the recursor may return any type.
        return Ok(false);
    }

    if info.inductive.variants.len() > 1 {
        // We have multiple variants, so the motive can only map to `Prop`.
        return Ok(true);
    }

    if info.inductive.variants.is_empty() {
        // There are no introduction rules, so we can eliminate to anything.
        // This is the principle of explosion.
        return Ok(false);
    }

    // At this point, we know we have only one introduction rule.
    // We must perform one final check.
    // Each argument that is not a global parameter must either
    // - reside in `Prop`, or
    // - occur in the return type.
    // We can justify the second case by observing that the information that it is part of the type is not a secret.
    // By eliminating to a non-proposition, we would not be revealing anything that is not already known.
    let variant = info.inductive.variants.first().unwrap();
    let mut ty = Expression::nary_binder_to_pi(
        cache,
        Provenance::Synthetic,
        variant.intro_rule.from_heap(cache),
    );
    let mut args_to_check = Vec::new();
    let mut parameter_index = 0;
    while let ExpressionT::Pi(pi) = ty.value(cache) {
        let local = pi.structure.generate_local(cache);
        if parameter_index >= info.inductive.global_params {
            let parameter_ty = as_sort(cache, pi.structure.bound.ty.infer_type(cache)?)?;
            if !parameter_ty.0.is_zero() {
                // The current argument is not in `Prop`.
                // Check it later.
                args_to_check.push(local);
            }
        }
        ty = pi.result.instantiate(
            cache,
            Expression::new(
                cache,
                pi.result.provenance(cache),
                ExpressionT::LocalConstant(local),
            ),
        );
        parameter_index += 1;
    }

    // Every argument in `args_to_check` must occur in `ty_arguments`.
    let ty_arguments = ty.apply_args(cache);
    for arg_to_check in args_to_check {
        if !ty_arguments.iter().any(|arg| {
            *arg == Expression::new(
                cache,
                arg_to_check.structure.bound.name.0.provenance,
                ExpressionT::LocalConstant(arg_to_check),
            )
        }) {
            // The argument did not occur in `ty_arguments`.
            return Ok(true);
        }
    }

    // All arguments are either in `Prop` or occur in `ty_arguments`.
    Ok(false)
}

/// Type checks the inductive with the given name.
/// This function returns a [`CertifiedInductive`], an inductive that has been verified by the type checker.
///
/// # Usage
///
/// Instead of calling this method directly, which takes an [`Inductive`] as well as its [`Path`],
/// in most instances you should call [`crate::DbExt::certify_inductive`] or [`crate::DbExt::get_certified_inductive`].
/// These functions are able to parse and certify both feather and quill definitions of inductives.
pub fn certify_inductive(db: &dyn Db, path: Path, ind: &Inductive) -> Dr<CertifiedInductive> {
    ExpressionCache::with_cache(db, None, None, |cache| {
        super::check_type::check_inductive_type(cache, path, ind).bind(|info| {
            Dr::sequence_unfail(
                info.inductive
                    .variants
                    .iter()
                    .map(|variant| super::check_variant::check_variant(cache, &info, variant)),
            )
            .deny()
            .bind(|_| match eliminate_only_into_prop(cache, &info) {
                Ok(eliminate_only_into_prop) => Dr::ok(CertifiedInductive {
                    inductive: info.inductive.clone(),
                    eliminate_only_into_prop,
                }),
                Err(_) => todo!(),
            })
        })
    })
}
