use std::path::PathBuf;

use fcommon::{Path, Source, SourceType, Str};
use fkernel::{
    certify_definition,
    result::{ConsoleFormatter, Delaborator},
};
use qdb::QuillDatabase;
use tracing_subscriber::{fmt::format::FmtSpan, FmtSubscriber};

struct DebugDelaborator<'a>(&'a QuillDatabase);

impl<'a> Delaborator for DebugDelaborator<'a> {
    fn delaborate(&self, expr: &fkernel::expr::HeapExpression) -> fkernel::result::Message {
        expr.display(self.0).into()
    }
}

fn main() {
    let log_level = tracing::Level::TRACE;
    let subscriber = FmtSubscriber::builder()
        .with_writer(std::io::stderr)
        .with_max_level(log_level)
        .with_span_events(FmtSpan::CLOSE)
        .with_timer(tracing_subscriber::fmt::time::uptime())
        .pretty()
        .finish();
    tracing::subscriber::set_global_default(subscriber)
        .expect("could not set default tracing subscriber");
    tracing::info!("initialised logging with verbosity level {}", log_level);

    let (db, _rx) = QuillDatabase::new(PathBuf::new());
    let path = Path::new(
        &db,
        vec![
            Str::new(&db, "test".to_string()),
            Str::new(&db, "test".to_string()),
        ],
    );
    let source = Source::new(&db, path, SourceType::Quill);

    let formatter = ConsoleFormatter {
        db: &db,
        delaborator: DebugDelaborator(&db),
    };

    let (result, reports) = qparse::module_from_quill_source(&db, source)
        .as_ref()
        .destructure();
    // Use a locked version of `stderr`, so that reports are not interspersed
    // with other things such as tracing messages from other threads.
    let mut stderr = std::io::stderr().lock();
    for report in reports {
        report.render(&db, &formatter, &mut stderr);
    }

    if let Some(result) = result {
        for def in result {
            let result = certify_definition(&db, path.with(&db, *def.name));
            for report in result.reports() {
                report.render(&db, &formatter, &mut stderr);
            }
        }
    }

    // TODO: <https://github.com/salsa-rs/salsa/blob/master/examples-2022/lazy-input/src/main.rs>
    // This helps us set up the main loop for language servers.
}
