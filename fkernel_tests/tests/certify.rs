use std::path::PathBuf;

use fcommon::{Path, Source, SourceType, Str};
use fexpr::result::{ConsoleFormatter, Delaborator, Message};
use qdb::QuillDatabase;

// Include the tests automatically generated by the build script.
include!(concat!(env!("OUT_DIR"), "/tests.rs"));

struct DebugDelaborator<'a>(&'a QuillDatabase);

impl<'a> Delaborator for DebugDelaborator<'a> {
    fn delaborate(&self, term: fexpr::expr::Term) -> fexpr::result::Message {
        term.display(self.0).into()
    }
}

fn run_test(file: &str) {
    let (db, _rx) = QuillDatabase::new(PathBuf::from("tests/src"));

    println!("testing {file}");

    let source = Source::new(
        &db,
        Path::new(
            &db,
            file.split('/')
                .map(|segment| Str::new(&db, segment.replace(".ron", "")))
                .collect(),
        ),
        SourceType::Feather,
    );

    println!("source file is {}", source.path(&db).display(&db));

    let formatter = ConsoleFormatter {
        db: &db,
        delaborator: DebugDelaborator(&db),
    };
    let result = fexpr::module::module_from_feather_source(&db, source)
        .as_ref()
        .map_messages(Message::new);
    for report in result.reports() {
        report.render(&db, &formatter, std::io::stdout());
    }
    assert!(result.reports().is_empty());

    if let Some(result) = result.value() {
        for def in &result.items {
            match def {
                fexpr::module::Item::Definition(def) => {
                    let path = Path::new(&db, {
                        let mut segments = source.path(&db).segments(&db).clone();
                        segments.push(*def.name);
                        segments
                    });
                    println!("certifying {}", path.display(&db));
                    let result = fkernel::typeck::certify_definition(&db, path);
                    for report in result.reports() {
                        report.render(&db, &formatter, std::io::stdout());
                    }
                    assert!(result.reports().is_empty());
                }
                fexpr::module::Item::Inductive(ind) => {
                    let path = Path::new(&db, {
                        let mut segments = source.path(&db).segments(&db).clone();
                        segments.push(*ind.name);
                        segments
                    });
                    println!("certifying {}", path.display(&db));
                    let result = fkernel::inductive::certify_inductive(&db, path);
                    for report in result.reports() {
                        report.render(&db, &formatter, std::io::stdout());
                    }
                    assert!(result.reports().is_empty());
                }
            }
        }
    }
}
