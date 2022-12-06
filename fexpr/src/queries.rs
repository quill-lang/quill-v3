use std::{ops::Deref, sync::Arc};

use fcommon::{with_local_database, Dr, FileReader, Intern, Report, ReportKind, Source};
use upcast::{Upcast, UpcastFrom};

use crate::{basic::QualifiedName, module::Module};

#[salsa::query_group(FeatherParserStorage)]
pub trait FeatherParser: FileReader + Upcast<dyn Intern> {
    fn module_from_feather_source(
        &self,
        source: Source,
        file_contents: Arc<String>,
    ) -> Dr<Arc<Module>>;
}

#[tracing::instrument(level = "debug")]
fn module_from_feather_source(
    db: &dyn FeatherParser,
    source: Source,
    file_contents: Arc<String>,
) -> Dr<Arc<Module>> {
    with_local_database(db.up(), || match ron::from_str(&file_contents) {
        Ok(module) => Dr::ok(Arc::new(module)),
        Err(err) => {
            Dr::fail(Report::new_in_file(ReportKind::Error, source).with_message(err.to_string()))
        }
    })
}

pub trait FeatherParserExt: FeatherParser + Upcast<dyn FeatherParser> {
    fn qualified_name_to_path(&self, qn: &QualifiedName) -> fcommon::Path {
        self.intern_path_data(fcommon::PathData(
            qn.iter().map(|name| *name.deref()).collect(),
        ))
    }
}

impl<'a, T: FeatherParser + 'a> UpcastFrom<T> for dyn FeatherParser + 'a {
    fn up_from(value: &T) -> &(dyn FeatherParser + 'a) {
        value
    }
    fn up_from_mut(value: &mut T) -> &mut (dyn FeatherParser + 'a) {
        value
    }
}

impl<T> FeatherParserExt for T where T: FeatherParser + 'static {}
