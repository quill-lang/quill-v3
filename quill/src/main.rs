use std::path::PathBuf;

use fcommon::{Path, Source, SourceType, Str};
use qdb::QuillDatabase;
use tracing::info;
use tracing_subscriber::{fmt::format::FmtSpan, FmtSubscriber};

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
    info!("initialised logging with verbosity level {}", log_level);

    let (db, _rx) = QuillDatabase::new(PathBuf::new());
    let path = Path::new(
        &db,
        vec![
            Str::new(&db, "test".to_string()),
            Str::new(&db, "test".to_string()),
        ],
    );
    let source = Source::new(&db, path, SourceType::Quill);

    let result = qparse::module_from_quill_source(&db, source);
    // Use a locked version of `stderr`, so that reports are not interspersed
    // with other things such as tracing messages from other threads.
    let mut stderr = std::io::stderr().lock();
    for report in result.reports() {
        report.render(&db, &mut stderr);
    }

    if let Some(result) = result.value() {
        tracing::info!("success");
        // for def in &result.items {
        //     match def {
        //         fexpr::module::Item::Definition(def) => {
        //             let result = fkernel::typeck::certify_definition(
        //                 &db,
        //                 Path::new(
        //                     &db,
        //                     vec![
        //                         Str::new(&db, "test".to_string()),
        //                         Str::new(&db, "test".to_string()),
        //                         *def.name,
        //                     ],
        //                 ),
        //             );

        //             for report in result.reports() {
        //                 report.render(&db, &mut stderr);
        //             }

        //             if result.value().is_some() {
        //                 tracing::info!(
        //                     "certified {} (has body: {})",
        //                     def.name.text(&db),
        //                     def.contents.expr.is_some()
        //                 );
        //             }
        //         }
        //         fexpr::module::Item::Inductive(ind) => {
        //             let result = fkernel::inductive::certify_inductive(
        //                 &db,
        //                 Path::new(
        //                     &db,
        //                     vec![
        //                         Str::new(&db, "test".to_string()),
        //                         Str::new(&db, "test".to_string()),
        //                         *ind.name,
        //                     ],
        //                 ),
        //             );

        //             for report in result.reports() {
        //                 report.render(&db, &mut stderr);
        //             }

        //             if let Some(result) = result.value() {
        //                 tracing::info!(
        //                     "certified {} (eliminate only into Prop: {})",
        //                     ind.name.text(&db),
        //                     result.eliminate_only_into_prop
        //                 );
        //             }
        //         }
        //     }
        // }
    }

    // TODO: <https://github.com/salsa-rs/salsa/blob/master/examples-2022/lazy-input/src/main.rs>
    // This helps us set up the main loop for language servers.
}
