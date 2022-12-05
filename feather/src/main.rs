use std::{path::PathBuf, sync::Arc};

use fcommon::{FileReader, Intern, PathData, Source, SourceType};
use fnodes::expr::{Expr, ExprContents};
use qdb::QuillDatabase;
use salsa::Durability;
use tracing::info;
use tracing_subscriber::{fmt::format::FmtSpan, FmtSubscriber};
use upcast::Upcast;

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

    let (mut db, _rx) = QuillDatabase::new();
    db.set_project_root_with_durability(Arc::new(PathBuf::new()), Durability::HIGH);
    let path = db.intern_path_data(PathData(vec![
        db.intern_string_data("test".to_string()),
        db.intern_string_data("test".to_string()),
    ]));
    let source = Source {
        path,
        ty: SourceType::Feather,
    };

    let result = db.source(source);
    // Use a locked version of `stderr`, so that reports are not interspersed
    // with other things such as tracing messages from other threads.
    let mut stderr = std::io::stderr().lock();
    for report in result.reports() {
        report.render(&db, &mut stderr);
    }

    if let Some(result) = result.value() {
        println!("{result}");
    }
    /*
    // This is the main loop for language servers, and other things that need regular file updates.
    loop {
        match rx.recv() {
            Ok(event) => {
                println!("caught event {:?}", event);
                if let notify::DebouncedEvent::Write(filepath_buf) = event {
                    // Convert this PathBuf into a rust Path, relativised to the current project directory.
                    if let Ok(path_relativised) = filepath_buf.strip_prefix(&*db.project_root())
                    {
                        // Convert this relativised rust Path into a feather Path.
                        let path = db.intern_path_data(PathData(
                            path_relativised
                                .iter()
                                .map(|component| {
                                    db.intern_string_data(
                                        component.to_string_lossy().to_string(),
                                    )
                                })
                                .collect(),
                        ));
                        // Tell the database that the file got changed.
                        println!("file '{}' changed", filepath_buf.to_string_lossy());
                        db.did_change_file(path);
                    } else {
                        println!(
                            "ignoring file path '{}' outside the project root",
                            filepath_buf.to_string_lossy()
                        );
                    }
                }
            }
            Err(e) => println!("watch error: {:?}", e),
        }
    }
    */
}
