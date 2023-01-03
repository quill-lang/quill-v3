#![feature(trait_upcasting)]

use fkernel::expr::BinderAnnotation;
use pretty_print::Document;
use qparse::{
    expr::{PExpression, PUniverse},
    Db,
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
            assert!(universe_ascription.is_none(), "deal with this later");
            Document::Text(name.display(db))
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

            binders_doc
                .then(Document::Text(" => ".to_owned()))
                .then(to_doc(db, result, true))
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
        PExpression::Sort { universe, .. } => match universe {
            PUniverse::Variable(name) => Document::Text(format!("Sort::{{{}}}", name.text(db))),
        },
        PExpression::Type { .. } => todo!(),
        PExpression::Prop(_) => todo!(),
        PExpression::StaticRegion(_) => todo!(),
        PExpression::Region(_) => todo!(),
        PExpression::RegionT(_) => todo!(),
        PExpression::Inductive(_) => todo!(),
    }
}
