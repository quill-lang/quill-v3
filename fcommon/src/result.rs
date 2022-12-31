use std::{fmt::Debug, ops::Deref};

use crate::{Source, SourceSpan, Span};

/// An message to be displayed to the user, such as an error or warning.
/// Rendered and displayed using the `ariadne` crate if printed to the user,
/// and converted to other diagnostic types if using the LSP protocol.
///
/// This struct is intentionally similar to the `Report` type in `ariadne`,
/// but its fields are accessible, and more closely tied to feather's internals.
/// This allows us to render a report to several different backends, including
/// `ariadne` itself, of course.
///
/// The fields are parametrised by a message type `M`, meant to represent a
/// formattable message, used for things like colouring and highlighting.
/// The formatter can be defined later.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Report<M> {
    /// The severity of the report.
    /// Used to determine colouring of output if rendered using `ariadne`.
    pub kind: ReportKind,
    /// The source file that the diagnostic comes from.
    pub source: Source,
    /// The location in the source file at which the diagnostic originates.
    /// If the span is not specified, then the diagnostic refers to the entire file.
    pub offset: Option<usize>,
    /// The message to display to the user, if present.
    pub message: Option<M>,
    /// A final note to display to the user, if present.
    pub note: Option<M>,
    /// A list of labels with additional information to display to the user.
    pub labels: Vec<Label<M>>,
}

impl<M> Report<M> {
    pub fn new_in_file(kind: ReportKind, source: Source) -> Self {
        Self {
            kind,
            source,
            offset: None,
            message: None,
            note: None,
            labels: Vec::new(),
        }
    }

    pub fn new(kind: ReportKind, source: Source, offset: usize) -> Self {
        Self {
            kind,
            source,
            offset: Some(offset),
            message: None,
            note: None,
            labels: Vec::new(),
        }
    }

    pub fn with_message(mut self, message: M) -> Self {
        self.message = Some(message);
        self
    }

    pub fn with_label(mut self, label: Label<M>) -> Self {
        self.labels.push(label);
        self
    }

    pub fn with_note(mut self, note: M) -> Self {
        self.note = Some(note);
        self
    }

    /// Convert this report into an [`ariadne::Report`] and then
    /// display it to the user.
    #[cfg(feature = "ariadne")]
    pub fn render(
        &self,
        db: &impl crate::Db,
        formatter: &impl MessageFormatter<Message = M>,
        stream: impl std::io::Write,
    ) {
        self.format(formatter)
            .write(
                DbCache {
                    db,
                    files: Default::default(),
                },
                stream,
            )
            .unwrap();
    }
}

/// Holds a database and uses it as a cache for `ariadne`.
#[cfg(feature = "ariadne")]
struct DbCache<'db, T>
where
    T: crate::Db,
{
    db: &'db T,
    files: std::collections::HashMap<Source, ariadne::Source>,
}

#[cfg(feature = "ariadne")]
impl<'db, T> ariadne::Cache<Source> for DbCache<'db, T>
where
    T: crate::Db,
{
    fn fetch(&mut self, id: &Source) -> Result<&ariadne::Source, Box<dyn std::fmt::Debug + '_>> {
        Ok(match self.files.entry(*id) {
            std::collections::hash_map::Entry::Occupied(occupied) => occupied.into_mut(),
            std::collections::hash_map::Entry::Vacant(vacant) => {
                vacant.insert(ariadne::Source::from(
                    crate::source(self.db, *id)
                        .value
                        .as_ref()
                        .map(|x| x.contents(self.db).as_str())
                        .unwrap_or("<could not read file>"),
                ))
            }
        })
    }

    fn display<'a>(&self, id: &'a Source) -> Option<Box<dyn std::fmt::Display + 'a>> {
        Some(Box::new(
            id.path(self.db)
                .to_path_buf(self.db)
                .with_extension(id.ty(self.db).extension())
                .to_string_lossy()
                .to_string(),
        ))
    }
}

/// A formatter, used for converting formattable diagnostic messages into raw strings to be
/// displayed in a terminal. Different formatters can be used for printing messages in a terminal,
/// writing to HTML output, or printing to a machine readable format, for example.
pub trait MessageFormatter {
    type Message;

    fn format(&self, message: &Self::Message) -> String;
}

/// Convert this report into an [`ariadne::Report`] in order
/// to display it to the user.
/// Enabled only when the `ariadne` feature flag is set.
#[cfg(feature = "ariadne")]
impl<M> Report<M> {
    fn format<F>(&self, formatter: &F) -> ariadne::Report<SourceSpan>
    where
        F: MessageFormatter<Message = M>,
    {
        let mut result =
            ariadne::Report::build(self.kind.into(), self.source, self.offset.unwrap_or(0));
        if let Some(message) = &self.message {
            result = result.with_message(formatter.format(message));
        }
        if let Some(note) = &self.note {
            result = result.with_note(formatter.format(note));
        }
        for label in &self.labels {
            result = result.with_label(label.format(formatter));
        }
        result.finish()
    }
}

/// <https://rustc-dev-guide.rust-lang.org/diagnostics.html#diagnostic-levels>
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReportKind {
    Error,
    Warning,
}

#[cfg(feature = "ariadne")]
impl From<ReportKind> for ariadne::ReportKind {
    fn from(kind: ReportKind) -> Self {
        match kind {
            ReportKind::Error => ariadne::ReportKind::Error,
            ReportKind::Warning => ariadne::ReportKind::Warning,
        }
    }
}

/// A localised message in a report.
/// See the `ariadne` crate for more information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Label<M> {
    /// The source file and span at which to render this label.
    pub source_span: SourceSpan,
    pub ty: LabelType,
    pub message: Option<M>,
    pub order: i32,
    pub priority: i32,
}

#[cfg(feature = "ariadne")]
impl<M> Label<M> {
    fn format<F>(&self, formatter: &F) -> ariadne::Label<SourceSpan>
    where
        F: MessageFormatter<Message = M>,
    {
        let mut result = ariadne::Label::new(self.source_span)
            .with_color(self.ty.into())
            .with_order(self.order)
            .with_priority(self.priority);
        if let Some(message) = &self.message {
            result = result.with_message(formatter.format(message));
        }
        result
    }
}

/// Influences the colour used to display this label.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LabelType {
    Error,
    Warning,
    Note,
}

/// Each label type is associated with a particular colour.
#[cfg(feature = "ariadne")]
impl From<LabelType> for ariadne::Color {
    fn from(ty: LabelType) -> Self {
        match ty {
            LabelType::Error => Self::Red,
            LabelType::Warning => Self::Yellow,
            LabelType::Note => Self::Cyan,
        }
    }
}

impl<M> Label<M> {
    pub fn new(source: Source, span: Span, ty: LabelType) -> Self {
        Self {
            source_span: SourceSpan { source, span },
            ty,
            message: None,
            order: 0,
            priority: 0,
        }
    }

    /// See [`ariadne::Label::with_message`].
    pub fn with_message(mut self, message: M) -> Self {
        self.message = Some(message);
        self
    }

    /// See [`ariadne::Label::with_order`].
    pub fn with_order(mut self, order: i32) -> Self {
        self.order = order;
        self
    }

    /// See [`ariadne::Label::with_priority`].
    pub fn with_priority(mut self, priority: i32) -> Self {
        self.priority = priority;
        self
    }
}

/// Short for "diagnostic result".
///
/// Even if warnings or errors are emitted, we may still be able to continue parsing the code.
/// So we need some kind of result type that allows us to raise errors or other messages while still
/// retaining an 'Ok' state, as far as the rest of the code is aware.
///
/// Upon exiting the program, all error messages will be scanned to check the most severe error level.
/// If any errors exist, no warnings will be emitted.
///
/// If no reports are provided, this does not allocate, and has roughly the same cost as a normal `Result`.
/// If using [`std::sync::Arc`] or similar to encapsulate a value together with reports, the [`Dr`] should
/// typically be the outermost container. This is because we are optimising for the path on which no
/// reports are emitted, so the cost is negligible, and it provides for a nicer API since we have direct
/// access to all of [`Dr`]'s methods.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use = "errors must be processed by an ErrorEmitter"]
pub struct ParametricDr<M, T> {
    /// If this is `None`, then the computation failed. Error messages will be contained inside `reports`.
    /// If this is `Some`, then the computation succeeded, but there may still be some messages (e.g. warnings
    /// or errors) inside `messages`.
    value: Option<T>,
    reports: Vec<Report<M>>,
}

impl<M, T> From<T> for ParametricDr<M, T> {
    fn from(value: T) -> Self {
        Self::ok(value)
    }
}

impl<M, T> From<Result<T, Report<M>>> for ParametricDr<M, T> {
    fn from(result: Result<T, Report<M>>) -> Self {
        match result {
            Ok(value) => Self::ok(value),
            Err(error) => Self::fail(error),
        }
    }
}

impl<M, T> From<Result<T, Vec<Report<M>>>> for ParametricDr<M, T> {
    fn from(result: Result<T, Vec<Report<M>>>) -> Self {
        match result {
            Ok(value) => Self::ok(value),
            Err(errors) => Self::fail_many(errors),
        }
    }
}

impl<M, T> ParametricDr<M, T> {
    /// The computation succeeded with no messages.
    /// This is the monadic `return` operation.
    pub fn ok(value: T) -> Self {
        Self {
            value: Some(value),
            reports: Vec::new(),
        }
    }

    /// The computation succeeded, but there was some error or warning message.
    pub fn ok_with(value: T, report: Report<M>) -> Self {
        Self {
            value: Some(value),
            reports: vec![report],
        }
    }

    pub fn ok_with_many(value: T, reports: Vec<Report<M>>) -> Self {
        Self {
            value: Some(value),
            reports,
        }
    }

    /// The computation failed. An error message is mandatory if the computation failed.
    pub fn fail(report: Report<M>) -> Self {
        assert!(report.kind == ReportKind::Error);
        Self {
            value: None,
            reports: vec![report],
        }
    }

    pub fn fail_many(reports: Vec<Report<M>>) -> Self {
        assert!(reports.iter().any(|m| m.kind == ReportKind::Error));
        Self {
            value: None,
            reports,
        }
    }

    /// Apply an infallible operation to the value inside this result. If the operation could fail, use [`Dr::bind`] instead.
    pub fn map<F, U>(self, f: F) -> ParametricDr<M, U>
    where
        F: FnOnce(T) -> U,
    {
        match self.value {
            Some(value) => ParametricDr {
                value: Some(f(value)),
                reports: self.reports,
            },
            None => ParametricDr {
                value: None,
                reports: self.reports,
            },
        }
    }

    /// A monadic bind operation that consumes this diagnostic result and uses the value it contains, if it exists,
    /// to produce a new diagnostic result.
    pub fn bind<F, U>(mut self, f: F) -> ParametricDr<M, U>
    where
        F: FnOnce(T) -> ParametricDr<M, U>,
    {
        match self.value {
            Some(value) => {
                let mut result = f(value);
                self.reports.append(&mut result.reports);
                ParametricDr {
                    value: result.value,
                    reports: self.reports,
                }
            }
            None => ParametricDr {
                value: None,
                reports: self.reports,
            },
        }
    }

    /// Appends a report to this diagnostic result, regardless of whether the result succeeded or failed.
    pub fn with(mut self, report: Report<M>) -> Self {
        self.reports.push(report);
        self
    }

    /// Appends some reports to this diagnostic result, regardless of whether the result succeeded or failed.
    pub fn with_many(mut self, reports: impl IntoIterator<Item = Report<M>>) -> Self {
        self.reports.extend(reports);
        self
    }

    /// Converts a failed diagnostic into a successful diagnostic by wrapping
    /// the contained value in an `Option`.
    pub fn unfail(self) -> ParametricDr<M, Option<T>> {
        ParametricDr {
            value: Some(self.value),
            reports: self.reports,
        }
    }

    /// Converts a successful diagnostic that had one or more `Error` reports into a failed diagnostic (with the same reports).
    /// Diagnostics without `Error` reports are unaffected.
    pub fn deny(self) -> Self {
        if self.reports.iter().any(|m| m.kind == ReportKind::Error) {
            Self {
                value: None,
                reports: self.reports,
            }
        } else {
            self
        }
    }

    /// Combines a list of diagnostic results into a single result by binding them all together.
    pub fn sequence(
        results: impl IntoIterator<Item = ParametricDr<M, T>>,
    ) -> ParametricDr<M, Vec<T>> {
        results
            .into_iter()
            .fold(ParametricDr::ok(Vec::new()), |acc, i| {
                acc.bind(|mut list| {
                    i.bind(|i| {
                        list.push(i);
                        ParametricDr::ok(list)
                    })
                })
            })
    }

    /// Combines a list of diagnostic results into a single result by binding them all together.
    /// Any failed diagnostics will be excluded from the output, but their error messages will remain.
    /// Therefore, this function will never fail - it might just produce an empty list as its output.
    pub fn sequence_unfail(
        results: impl IntoIterator<Item = ParametricDr<M, T>>,
    ) -> ParametricDr<M, Vec<T>> {
        results
            .into_iter()
            .fold(ParametricDr::ok(Vec::new()), |acc, i| {
                acc.bind(|mut list| {
                    i.unfail().bind(|i| {
                        if let Some(i) = i {
                            list.push(i);
                        }
                        ParametricDr::ok(list)
                    })
                })
            })
    }

    /// Returns true if the computation succeeded.
    pub fn succeeded(&self) -> bool {
        self.value.is_some()
    }

    /// Returns true if the computation failed.
    pub fn failed(&self) -> bool {
        self.value.is_none()
    }

    /// Returns true if there was an error report.
    /// If `failed` is true, then `errored` is true.
    pub fn errored(&self) -> bool {
        self.reports
            .iter()
            .any(|report| report.kind == ReportKind::Error)
    }

    /// Splits up this diagnostic result into its value and its error messages.
    /// It is your responsibility to put these error messages back inside another diagnostic result.
    /// Failure to do so will result in errors not being displayed, or invalid programs erroneously
    /// being considered correct.
    pub fn destructure(self) -> (Option<T>, Vec<Report<M>>) {
        (self.value, self.reports)
    }

    /// Retrieves the value for inspection.
    pub fn value(&self) -> &Option<T> {
        &self.value
    }

    /// Retrieves the list of reports.
    pub fn reports(&self) -> &[Report<M>] {
        &self.reports
    }

    /// Returns a diagnostic result with the same reports, but where the value is borrowed.
    pub fn as_ref(&self) -> ParametricDr<M, &T>
    where
        M: Clone,
    {
        ParametricDr {
            value: self.value.as_ref(),
            reports: self.reports.clone(),
        }
    }

    /// Returns a diagnostic result with the same reports, but where the value is dereferenced.
    pub fn as_deref(&self) -> ParametricDr<M, &T::Target>
    where
        M: Clone,
        T: Deref,
    {
        ParametricDr {
            value: self.value.as_deref(),
            reports: self.reports.clone(),
        }
    }

    /// If there were any errors, panic.
    /// Useful for tests.
    pub fn assert_ok(&self)
    where
        M: Debug,
    {
        if self.errored() {
            panic!("diagnostic result contained errors: {:#?}", self.reports);
        }
    }

    /// If there were no errors, return the underlying value.
    /// Useful for tests.
    pub fn unwrap(self) -> T
    where
        M: Debug,
    {
        self.assert_ok();
        self.value.unwrap()
    }

    /// If there were no errors, panic.
    /// Useful for tests.
    pub fn assert_errored(&self)
    where
        M: Debug,
    {
        if !self.errored() {
            panic!(
                "diagnostic result was supposed to contain errors, reports were: {:#?}",
                self.reports
            );
        }
    }

    /// Applies the given function to all reports in this diagnostic result.
    /// This can change the message type.
    pub fn map_reports<N>(self, f: impl Fn(Report<M>) -> Report<N>) -> ParametricDr<N, T> {
        ParametricDr {
            value: self.value,
            reports: self.reports.into_iter().map(f).collect(),
        }
    }

    /// Applies the given function to all messages inside all reports in this diagnostic result.
    /// This can change the message type.
    pub fn map_messages<N>(self, f: impl Clone + Fn(M) -> N) -> ParametricDr<N, T> {
        self.map_reports(|report| Report {
            kind: report.kind,
            source: report.source,
            offset: report.offset,
            message: report.message.map(f.clone()),
            note: report.note.map(f.clone()),
            labels: report
                .labels
                .into_iter()
                .map(|label| Label {
                    source_span: label.source_span,
                    ty: label.ty,
                    message: label.message.map(f.clone()),
                    order: label.order,
                    priority: label.priority,
                })
                .collect(),
        })
    }
}

impl<M, T> FromIterator<ParametricDr<M, T>> for ParametricDr<M, Vec<T>> {
    /// Any failed diagnostics will be excluded from the output, but their error messages will remain.
    /// Therefore, this function will never fail - it might just produce an empty list as its output.
    fn from_iter<U: IntoIterator<Item = ParametricDr<M, T>>>(iter: U) -> Self {
        ParametricDr::sequence_unfail(iter)
    }
}
