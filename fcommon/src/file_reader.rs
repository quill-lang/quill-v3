use std::{fmt::Debug, path::PathBuf};

use crate::{Db, Dr, Report, ReportKind, Source};

/// An input file.
#[salsa::input]
pub struct InputFile {
    pub path: PathBuf,
    #[return_ref]
    pub contents: String,
}

#[tracing::instrument(level = "debug")]
#[salsa::tracked]
pub fn source(db: &dyn Db, source: Source) -> Dr<InputFile> {
    let path_buf = source
        .path(db)
        .to_path_buf(db)
        .with_extension(source.ty(db).extension());
    match db.input_file(path_buf.clone()) {
        Ok(value) => Dr::ok(value),
        Err(err) => Dr::fail(
            Report::new_in_file(ReportKind::Error, source).with_message(format!(
                "could not read file '{}': {}",
                path_buf.to_string_lossy(),
                err,
            )),
        ),
    }
}
