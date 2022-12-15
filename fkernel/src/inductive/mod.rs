use fcommon::{Dr, Path, Report, ReportKind, Source, SourceType};
use fexpr::{
    basic::Provenance,
    expr::{largest_unusable_metavariable, Expression, ExpressionT, MetavariableGenerator, Term},
    inductive::Inductive,
    queries::module_from_feather_source,
};

use crate::{
    term::{apply_args, instantiate, nary_binder_to_pi},
    typeck::{as_sort, infer_type, Ir},
    universe::{is_nonzero, is_zero},
    Db,
};

use self::check_type::InductiveTypeInformation;

mod check_type;
mod check_variant;

/// Retrieves the inductive with the given name.
/// This inductive will not have been type checked.
#[salsa::tracked(return_ref)]
pub fn get_inductive(db: &dyn Db, path: Path) -> Dr<Inductive<Provenance, Box<Expression>>> {
    let (source, name) = path.split_last(db);
    module_from_feather_source(db, Source::new(db, source, SourceType::Feather))
        .as_ref()
        .map(|module| {
            module.items.iter().find_map(|item| match item {
                fexpr::module::Item::Inductive(ind) => {
                    if *ind.name == name {
                        Some(ind.clone())
                    } else {
                        None
                    }
                }
                _ => None,
            })
        })
        .bind(|ind| match ind {
            Some(ind) => Dr::ok(ind),
            None => Dr::fail(
                Report::new_in_file(
                    ReportKind::Error,
                    Source::new(db, source, SourceType::Feather),
                )
                .with_message(format!("inductive {} could not be found", name.text(db))),
            ),
        })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedInductive {
    pub inductive: Inductive<Provenance, Box<Expression>>,
    /// True if the motive for any match statement must be a proposition.
    pub eliminate_only_into_prop: bool,
}

/// Returns true if the the motive in match expressions can live in `Prop`.
fn eliminate_only_into_prop(db: &dyn Db, info: &InductiveTypeInformation) -> Ir<bool> {
    if is_nonzero(&info.sort.0) {
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
    let mut ty = nary_binder_to_pi(db, variant.intro_rule.without_provenance(db));
    let mut args_to_check = Vec::new();
    let mut parameter_index = 0;
    let mut meta_gen = MetavariableGenerator::new(largest_unusable_metavariable(db, ty));
    while let ExpressionT::Pi(pi) = ty.value(db) {
        let local = pi.structure.generate_local_with_gen(&mut meta_gen);
        if parameter_index >= info.inductive.global_params {
            let parameter_ty = as_sort(db, infer_type(db, pi.structure.bound.ty)?)?;
            if !is_zero(&parameter_ty.0) {
                // The current argument is not in `Prop`.
                // Check it later.
                args_to_check.push(local);
            }
        }
        ty = instantiate(
            db,
            pi.result,
            Term::new(db, ExpressionT::LocalConstant(local)),
        );
        parameter_index += 1;
    }

    // Every argument in `args_to_check` must occur in `ty_arguments`.
    let ty_arguments = apply_args(db, ty);
    for arg_to_check in args_to_check {
        if !ty_arguments
            .iter()
            .any(|arg| *arg == Term::new(db, ExpressionT::LocalConstant(arg_to_check)))
        {
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
/// When certifying a definition or inductive, we may depend on previously certified inductives.
/// These should only be accessed using [`get_certified_inductive`], so that we don't double any error messages emitted.
#[salsa::tracked(return_ref)]
pub fn certify_inductive(db: &dyn Db, path: Path) -> Dr<CertifiedInductive> {
    check_type::check_inductive_type(db, path).bind(|info| {
        Dr::sequence_unfail(
            info.inductive
                .variants
                .iter()
                .map(|variant| check_variant::check_variant(db, &info, variant)),
        )
        .deny()
        .bind(|_| match eliminate_only_into_prop(db, &info) {
            Ok(eliminate_only_into_prop) => Dr::ok(CertifiedInductive {
                inductive: info.inductive.clone(),
                eliminate_only_into_prop,
            }),
            Err(_) => todo!(),
        })
    })
}

/// Type checks the definition with the given name, or retrieves it from the database if it was already type checked.
/// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
/// This function will discard any diagnostic messages produced by type checking the definition.
pub fn get_certified_inductive(db: &dyn Db, path: Path) -> Option<&CertifiedInductive> {
    certify_inductive(db, path).value().as_ref()
}
