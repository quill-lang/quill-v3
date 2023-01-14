#![feature(trait_upcasting)]
#![feature(iter_intersperse)]

use fkernel::{expr::BinderAnnotation, Db};
use pretty_print::Document;
use qparse::{
    expr::{PExpression, PUniverse},
    inductive::PInductive,
};

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
        PExpression::Borrow { value, .. } => Document::Concat(vec![
            Document::Text("&".to_owned()),
            to_doc(db, value, false),
        ]),
        PExpression::Dereference { value, .. } => Document::Concat(vec![
            Document::Text("*".to_owned()),
            to_doc(db, value, false),
        ]),
        PExpression::Delta { region, ty, .. } => Document::Concat(vec![
            Document::Text("Δ[".to_owned()),
            to_doc(db, region, false),
            Document::Text("] ".to_owned()),
            to_doc(db, ty, false),
        ]),
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
        PExpression::Let { binders, body, .. } => Document::Concat(
            std::iter::once(Document::Text("let".to_owned()))
                .chain(
                    binders
                        .iter()
                        .map(|binder| {
                            if let Some(ty) = &binder.ty {
                                vec![
                                    Document::Line,
                                    Document::Text(binder.name.0.text(db).to_owned()),
                                    Document::Text(": ".to_owned()),
                                    to_doc(db, ty, true),
                                    Document::Text(" = ".to_owned()),
                                    to_doc(db, &binder.to_assign, true),
                                ]
                            } else {
                                vec![
                                    Document::Line,
                                    Document::Text(binder.name.0.text(db).to_owned()),
                                    Document::Text(" = ".to_owned()),
                                    to_doc(db, &binder.to_assign, true),
                                ]
                            }
                        })
                        .map(|doc| Document::Indent(Box::new(Document::Concat(doc)))),
                )
                .chain(std::iter::once(Document::Line))
                .chain(std::iter::once(to_doc(db, body, true)))
                .collect(),
        ),
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
        PExpression::FunctionType {
            binder,
            region,
            result,
            ..
        } => {
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

            let region = if let Some(region) = region {
                Document::Text("‹".to_owned())
                    .then(to_doc(db, region, allow_apply))
                    .then(Document::Text("› ".to_owned()))
            } else {
                Document::Empty
            };

            bracketed_binder
                .then(Document::Text(" -> ".to_owned()))
                .then(region)
                .then(to_doc(db, result, true))
        }
        PExpression::Sort { universe, .. } => Document::Concat(vec![
            Document::Text("Sort::{".to_owned()),
            puniverse_to_document(db, universe),
            Document::Text("}".to_owned()),
        ]),
        PExpression::Type { universe, .. } => {
            if let Some(universe) = universe {
                Document::Concat(vec![
                    Document::Text("Type::{".to_owned()),
                    puniverse_to_document(db, &universe.1),
                    Document::Text("}".to_owned()),
                ])
            } else {
                Document::Text("Type".to_owned())
            }
        }

        PExpression::Prop(_) => Document::Text("Prop".to_owned()),
        PExpression::StaticRegion(_) => todo!(),
        PExpression::Region(_) => Document::Text("Region".to_owned()),
        PExpression::RegionT(_) => Document::Text("RegionT".to_owned()),
        PExpression::Inductive(inductive) => pinductive_to_document(db, inductive),
        PExpression::Hole { id, args, .. } => {
            if args.is_empty() {
                Document::Text(id.to_string())
            } else {
                Document::Concat(
                    std::iter::once(Document::Text(format!("{id}[")))
                        .chain(
                            args.iter()
                                .map(|pexpr| pexpression_to_document(db, pexpr))
                                .intersperse(Document::Text(", ".to_owned())),
                        )
                        .chain(std::iter::once(Document::Text("]".to_owned())))
                        .collect(),
                )
            }
        }
    }
}

pub fn puniverse_to_document(db: &dyn Db, puniverse: &PUniverse) -> Document {
    match puniverse {
        PUniverse::Zero(_) => Document::Text("0".to_owned()),
        PUniverse::Variable(var) => Document::Text(var.text(db).to_owned()),
        PUniverse::Succ { value, .. } => {
            puniverse_to_document(db, value).then(Document::Text(" + 1".to_owned()))
        }
        PUniverse::ImpredicativeMax { left, right, .. } => Document::Text("imax (".to_owned())
            .then(puniverse_to_document(db, left))
            .then(Document::Text(") (".to_owned()))
            .then(puniverse_to_document(db, right))
            .then(Document::Text(")".to_owned())),
        PUniverse::Metauniverse { index, .. } => Document::Text(format!("?u{index}")),
    }
}

pub fn pinductive_to_document(db: &dyn Db, pinductive: &PInductive) -> Document {
    Document::Concat(
        std::iter::once(Document::Text("inductive".to_owned()))
            .chain(pinductive.variants.iter().map(|variant| {
                let body = variant.fields.iter().map(|_| todo!());
                Document::Concat(vec![Document::Indent(Box::new(Document::Concat(
                    std::iter::once(Document::Line)
                        .chain(std::iter::once(Document::Text(
                            variant.name.text(db).to_owned(),
                        )))
                        .chain(body)
                        .collect(),
                )))])
            }))
            .collect(),
    )
}
