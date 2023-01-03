#![feature(trait_upcasting)]

use fkernel::expr::BinderAnnotation;
use pretty_print::Document;
use qparse::{
    expr::{PExpression, PUniverse},
    Db,
};

pub mod pretty_print;

pub fn pexpression_to_document(db: &dyn Db, pexpr: &PExpression) -> Document {
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
        PExpression::Apply { .. } => todo!(),
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
                                .then(pexpression_to_document(db, ty))
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
                .then(pexpression_to_document(db, result))
        }
        PExpression::FunctionType { binder, result, .. } => {
            let binder_doc = if let Some(name) = binder.name {
                Document::Text(name.text(db).to_owned())
                    .then(Document::Text(": ".to_owned()))
                    .then(pexpression_to_document(db, &binder.ty))
            } else {
                pexpression_to_document(db, &binder.ty)
            };

            let bracketed_binder =
                if binder.name.is_some() || binder.annotation != BinderAnnotation::Explicit {
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
                .then(pexpression_to_document(db, result))
        }
        PExpression::Sort { universe, .. } => match universe {
            PUniverse::Variable(name) => Document::Text(format!("Sort::{}", name.text(db))),
        },
        PExpression::Type { .. } => todo!(),
        PExpression::Prop(_) => todo!(),
        PExpression::StaticRegion(_) => todo!(),
        PExpression::Region(_) => todo!(),
        PExpression::RegionT(_) => todo!(),
        PExpression::Inductive(_) => todo!(),
    }
}
