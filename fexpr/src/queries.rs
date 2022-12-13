use fcommon::{with_local_database, Dr, Report, ReportKind, Source};

use crate::{basic::Provenance, expr::Expression, module::Module, Db};

#[tracing::instrument(level = "debug")]
#[salsa::tracked(return_ref)]
pub fn module_from_feather_source(
    db: &dyn Db,
    source: Source,
) -> Dr<Module<Provenance, Expression>> {
    fcommon::source(db, source).bind(|file_contents| {
        with_local_database(db, || match ron::from_str(file_contents.contents(db)) {
            Ok(module) => Dr::ok(module),
            Err(err) => Dr::fail(
                Report::new_in_file(ReportKind::Error, source).with_message(err.to_string()),
            ),
        })
    })
}
