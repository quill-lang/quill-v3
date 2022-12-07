mod file_reader;
mod interning;
mod result;

pub use file_reader::*;
pub use interning::*;
pub use result::*;

#[salsa::jar(db = Db)]
pub struct Jar(Str, Path, Source, InputFile, source);

pub trait Db: std::fmt::Debug + salsa::DbWithJar<Jar> {
    /// Loads source code from a file.
    /// This is performed lazily when needed.
    fn input_file(&self, path: std::path::PathBuf) -> std::io::Result<InputFile>;
}
