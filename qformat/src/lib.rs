#![feature(trait_upcasting)]
#![feature(iter_intersperse)]

use fkernel::{expr::BinderAnnotation, Db};
use pretty_print::Document;
use qparse::expr::{PExpression, PUniverse};

pub mod pretty_print;

pub fn pexpression_to_document(db: &dyn Db, pexpr: &PExpression) -> Document {
    to_doc(db, pexpr, true)
}

/// The main loop for `pexpression_to_document`.
/// `allow_apply` will be converted into a proper binding power tracker later.
fn to_doc(db: &dyn Db, pexpr: &PExpression, allow_apply: bool) -> Document {
    match pexpr {
        PExpression::Variable {
            name,
            universe_ascription,
        } => {
            let body = Document::Text(name.display(db));
            if let Some((_, ascription, _)) = universe_ascription {
                Document::Concat(
                    std::iter::once(body)
                        .chain(std::iter::once(Document::Text("::{".to_owned())))
                        .chain(
                            ascription
                                .iter()
                                .map(|puniverse| puniverse_to_document(db, puniverse))
                                .intersperse_with(|| Document::Text(", ".to_owned())),
                        )
                        .chain(std::iter::once(Document::Text("}".to_owned())))
                        .collect(),
                )
            } else {
                body
            }
        }
        PExpression::Borrow { .. } => todo!(),
        PExpression::Dereference { .. } => todo!(),
        PExpression::Apply { function, argument } => {
            let doc = Document::Concat(vec![
                to_doc(db, function, true),
                Document::Text(" ".to_owned()),
                to_doc(db, argument, false),
            ]);
            if allow_apply {
                doc
            } else {
                Document::Concat(vec![
                    Document::Text("(".to_owned()),
                    doc,
                    Document::Text(")".to_owned()),
                ])
            }
        }
        PExpression::Intro { .. } => todo!(),
        PExpression::Match { .. } => todo!(),
        PExpression::Fix { .. } => todo!(),
        PExpression::Let { .. } => todo!(),
        PExpression::Lambda {
            binders, result, ..
        } => {
            let binders_doc = Document::Concat(
                std::iter::once(Document::Text("fn".to_owned()))
                    .chain(binders.iter().map(|binder| {
                        let binder_doc = if let Some(ty) = &binder.ty {
                            Document::Text(binder.name.text(db).to_owned())
                                .then(Document::Text(": ".to_owned()))
                                .then(to_doc(db, ty, true))
                        } else {
                            Document::Text(binder.name.text(db).to_owned())
                        };

                        let bracketed_binder = if binder.ty.is_some()
                            || binder.annotation != BinderAnnotation::Explicit
                        {
                            Document::Text(
                                match binder.annotation {
                                    BinderAnnotation::Explicit => "(",
                                    BinderAnnotation::ImplicitEager => "{",
                                    BinderAnnotation::ImplicitWeak => "{{",
                                    BinderAnnotation::ImplicitTypeclass => "[",
                                }
                                .to_owned(),
                            )
                            .then(binder_doc)
                            .then(Document::Text(
                                match binder.annotation {
                                    BinderAnnotation::Explicit => ")",
                                    BinderAnnotation::ImplicitEager => "}",
                                    BinderAnnotation::ImplicitWeak => "}}",
                                    BinderAnnotation::ImplicitTypeclass => "]",
                                }
                                .to_owned(),
                            ))
                        } else {
                            binder_doc
                        };

                        Document::Text(" ".to_owned()).then(bracketed_binder)
                    }))
                    .collect(),
            );

            Document::Text("(".to_owned())
                .then(binders_doc)
                .then(Document::Text(" => ".to_owned()))
                .then(to_doc(db, result, true))
                .then(Document::Text(")".to_owned()))
        }
        PExpression::FunctionType { binder, result, .. } => {
            let draw_brackets = binder.name.is_some()
                || binder.annotation != BinderAnnotation::Explicit
                || matches!(&*binder.ty, PExpression::FunctionType { .. });

            let binder_doc = if let Some(name) = binder.name {
                Document::Text(name.text(db).to_owned())
                    .then(Document::Text(": ".to_owned()))
                    .then(to_doc(db, &binder.ty, true))
            } else {
                to_doc(db, &binder.ty, !draw_brackets)
            };

            let bracketed_binder = if draw_brackets {
                Document::Text(
                    match binder.annotation {
                        BinderAnnotation::Explicit => "(",
                        BinderAnnotation::ImplicitEager => "{",
                        BinderAnnotation::ImplicitWeak => "{{",
                        BinderAnnotation::ImplicitTypeclass => "[",
                    }
                    .to_owned(),
                )
                .then(binder_doc)
                .then(Document::Text(
                    match binder.annotation {
                        BinderAnnotation::Explicit => ")",
                        BinderAnnotation::ImplicitEager => "}",
                        BinderAnnotation::ImplicitWeak => "}}",
                        BinderAnnotation::ImplicitTypeclass => "]",
                    }
                    .to_owned(),
                ))
            } else {
                binder_doc
            };

            bracketed_binder
                .then(Document::Text(" -> ".to_owned()))
                .then(to_doc(db, result, true))
        }
        PExpression::Sort { universe, .. } => Document::Concat(vec![
            Document::Text("Sort::{".to_owned()),
            puniverse_to_document(db, universe),
            Document::Text("}".to_owned()),
        ]),
        PExpression::Type { .. } => todo!(),
        PExpression::Prop(_) => todo!(),
        PExpression::StaticRegion(_) => todo!(),
        PExpression::Region(_) => todo!(),
        PExpression::RegionT(_) => todo!(),
        PExpression::Inductive(_) => todo!(),
        PExpression::Metavariable { index, .. } => Document::Text(format!("?{index}")),
    }
}

pub fn puniverse_to_document(db: &dyn Db, puniverse: &PUniverse) -> Document {
    match puniverse {
        PUniverse::Variable(var) => Document::Text(var.text(db).to_owned()),
        PUniverse::Metauniverse { index, .. } => Document::Text(format!("?u{index}")),
    }
}
