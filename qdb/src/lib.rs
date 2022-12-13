use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::Debug,
    path::PathBuf,
    sync::{mpsc, Arc, Mutex},
    time::Duration,
};

use fcommon::*;
use notify_debouncer_mini::notify::RecursiveMode;
use salsa::Snapshot;

/// The main database that manages all the compiler's queries.
#[salsa::db(fcommon::Jar, fexpr::Jar, fkernel::Jar)]
pub struct QuillDatabase {
    storage: salsa::Storage<Self>,
    project_root: PathBuf,
    files: Arc<Mutex<HashMap<PathBuf, InputFile>>>,
    watcher: Arc<
        Mutex<notify_debouncer_mini::Debouncer<notify_debouncer_mini::notify::RecommendedWatcher>>,
    >,
}

impl Debug for QuillDatabase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<db>")
    }
}

impl fcommon::Db for QuillDatabase {
    fn input_file(&self, path: PathBuf) -> std::io::Result<InputFile> {
        let path = self.project_root.join(&path).canonicalize().map_err(|e| {
            std::io::Error::new(e.kind(), format!("failed to read {}", path.display()))
        })?;
        Ok(match self.files.lock().unwrap().entry(path.clone()) {
            // If the file already exists in our cache then just return it.
            Entry::Occupied(entry) => *entry.get(),
            // If we haven't read this file yet set up the watch, read the
            // contents, store it in the cache, and return it.
            Entry::Vacant(entry) => {
                // Set up the watch before reading the contents to try to avoid
                // race conditions.
                let watcher = &mut *self.watcher.lock().unwrap();
                watcher
                    .watcher()
                    .watch(&path, RecursiveMode::NonRecursive)
                    .unwrap();
                let contents = std::fs::read_to_string(&path).map_err(|e| {
                    std::io::Error::new(e.kind(), format!("failed to read {}", path.display()))
                })?;
                *entry.insert(InputFile::new(self, path, contents))
            }
        })
    }
}

impl salsa::Database for QuillDatabase {}
impl salsa::ParallelDatabase for QuillDatabase {
    fn snapshot(&self) -> Snapshot<Self> {
        Snapshot::new(QuillDatabase {
            storage: self.storage.snapshot(),
            project_root: self.project_root.clone(),
            files: Arc::clone(&self.files),
            watcher: Arc::clone(&self.watcher),
        })
    }
}

impl QuillDatabase {
    /// Returns the database, along with a receiver for file update events.
    /// If running as a language server, this channel should be watched,
    /// and any updated paths should be passed into [`FileWatcher::did_change_file`].
    /// If running as a standalone compiler, the channel may be ignored,
    /// although receiving file update events may still be desirable in certain cases.
    pub fn new(
        project_root: PathBuf,
    ) -> (Self, mpsc::Receiver<notify_debouncer_mini::DebouncedEvent>) {
        let (tx, rx) = mpsc::channel();
        let debouncer = notify_debouncer_mini::new_debouncer(
            Duration::from_secs(1),
            None,
            move |res: notify_debouncer_mini::DebounceEventResult| match res {
                Ok(events) => events.into_iter().for_each(|e| tx.send(e).unwrap()),
                Err(errors) => errors.iter().for_each(|e| panic!("{e:?}")),
            },
        )
        .unwrap();

        let this = Self {
            storage: Default::default(),
            project_root,
            files: Default::default(),
            watcher: Arc::new(Mutex::new(debouncer)),
        };

        (this, rx)
    }
}
