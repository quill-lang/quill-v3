//! We parse expressions in two stages.
//! We create an explicit recursive descent parser for expressions themselves,
//! and use a Pratt parser for the "Pratt expressions", a specific kind of sub-expression
//! that deals only with prefix, infix, and postfix operators, as well as function application.

use fcommon::{Label, LabelType, Report, ReportKind, Span, Spanned, Str};
use fexpr::{
    basic::{Name, Provenance, QualifiedName, WithProvenance},
    expr::BinderAnnotation,
    message,
    multiplicity::ParameterOwnership,
    result::Dr,
};

use crate::{
    lex::{ReservedSymbol, TokenTree},
    parser::Parser,
};

/// A parsed lambda binder.
#[derive(Debug)]
pub struct PLambdaBinder {
    /// The name given to the bound variable.
    pub name: Name<Provenance>,
    /// The annotation on the associated lambda abstraction.
    pub annotation: BinderAnnotation,
    /// If brackets were given explicitly, their spans are here.
    pub brackets: Option<(Span, Span)>,
    /// The ownership annotation on the bound variable, if explicitly given.
    /// If absent, it is inferred by the elaborator.
    pub ownership: Option<(ParameterOwnership, Span)>,
    /// The type, if explicitly given.
    /// If it is not given, it must be inferred by the elaborator.
    pub ty: Option<PExpression>,
}

/// A parsed function type.
#[derive(Debug)]
pub struct PFunctionBinder {
    /// The name given to the bound variable, if present.
    pub name: Option<Name<Provenance>>,
    /// The annotation on the associated lambda abstraction.
    pub annotation: BinderAnnotation,
    /// If brackets were given explicitly, their spans are here.
    pub brackets: Option<(Span, Span)>,
    /// The ownership annotation on the bound variable, if explicitly given.
    /// If absent, it is inferred by the elaborator.
    pub ownership: Option<(ParameterOwnership, Span)>,
    /// The type of the bound variable.
    pub ty: Box<PExpression>,
}

/// A parsed expression.
#[derive(Debug)]
pub enum PExpression {
    /// A local variable or an instantiated constant.
    Variable(QualifiedName<Provenance>),
    Apply {
        function: Box<PExpression>,
        argument: Box<PExpression>,
    },
    Lambda {
        fn_token: Span,
        binders: Vec<PLambdaBinder>,
        result: Box<PExpression>,
    },
    FunctionType {
        binder: PFunctionBinder,
        arrow_token: Span,
        result: Box<PExpression>,
    },
}

impl Spanned for PExpression {
    fn span(&self) -> Span {
        todo!()
    }
}

impl<'db, 'a, I> Parser<'db, 'a, I>
where
    I: Iterator<Item = TokenTree>,
{
    /// Parse all token trees that could be part of a Pratt expression.
    fn parse_pratt_expr_terms(&mut self) -> Vec<TokenTree> {
        let mut result = Vec::new();
        loop {
            match self.peek() {
                Some(TokenTree::Lexical { .. }) | Some(TokenTree::Operator { .. }) => {
                    result.push(self.next().unwrap())
                }
                _ => return result,
            }
        }
    }

    /// Parses a Pratt expression.
    /// TODO: Write this complete function. For now, we just parse function applications.
    pub fn parse_pratt_expr(&mut self) -> Dr<PExpression> {
        let terms = self.parse_pratt_expr_terms();
        let result = terms
            .into_iter()
            .map(|token_tree| match token_tree {
                TokenTree::Lexical { text, span } => {
                    let provenance = self.provenance(span);
                    PExpression::Variable(QualifiedName(WithProvenance::new_with_provenance(
                        provenance,
                        vec![Name(WithProvenance::new_with_provenance(
                            provenance,
                            Str::new(self.config().db, text),
                        ))],
                    )))
                }
                _ => todo!(),
            })
            .reduce(|acc, expr| PExpression::Apply {
                function: Box::new(acc),
                argument: Box::new(expr),
            });

        let source = self.config().source;
        match result {
            Some(result) => Dr::ok(result),
            None => match self.peek() {
                Some(tt) => Dr::fail(
                    Report::new(ReportKind::Error, source, tt.span().start)
                        .with_message("expected an expression".into())
                        .with_label(
                            Label::new(source, tt.span(), LabelType::Error)
                                .with_message(message!["expected an expression but found ", tt]),
                        ),
                ),
                None => match self.block_brackets() {
                    Some((open, close)) => Dr::fail(
                        Report::new(ReportKind::Error, source, close.start)
                            .with_message("expected an expression".into())
                            .with_label(Label::new(source, close, LabelType::Error).with_message(
                                "expected an expression before the end of this block".into(),
                            ))
                            .with_label(
                                Label::new(source, open, LabelType::Note)
                                    .with_message("the block started here".into()),
                            ),
                    ),
                    None => todo!(),
                },
            },
        }
    }

    /// If the next token was an ownership label (`erased`, `owned`, `copyable`), consume and return it.
    fn parse_ownership(&mut self) -> Option<(ParameterOwnership, Span)> {
        match self.peek() {
            Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Erased,
                span,
            }) => {
                let span = *span;
                self.next();
                Some((ParameterOwnership::PZero, span))
            }
            Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Owned,
                span,
            }) => {
                let span = *span;
                self.next();
                Some((ParameterOwnership::POwned, span))
            }
            Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Copyable,
                span,
            }) => {
                let span = *span;
                self.next();
                Some((ParameterOwnership::PCopyable, span))
            }
            _ => None,
        }
    }

    /// Parses a single lambda abstraction binder.
    fn parse_lambda_binder(&mut self, fn_token: Span) -> Dr<PLambdaBinder> {
        match self.next() {
            // A single lexical token is interpreted as a binder with no explicit type, using
            // the explicit binder annotation.
            Some(TokenTree::Lexical { text, span }) => Dr::ok(PLambdaBinder {
                name: Name(WithProvenance::new_with_provenance(
                    self.provenance(span),
                    Str::new(self.config().db, text),
                )),
                annotation: BinderAnnotation::Explicit,
                brackets: None,
                ownership: None,
                ty: None,
            }),
            Some(TokenTree::Block {
                bracket,
                open,
                close,
                contents,
            }) => {
                // This is either a binder of the form `(ownership? name)`, using any bracket style, or
                // `(ownership? name : type)`, again using any bracket style.
                let mut inner = self.with_vec(open, close, contents);
                // First, parse all of the ownership symbols.
                let ownership = inner.parse_ownership();
                if inner.one_tree_left() {
                    // This is a binder which does not explicitly declare the type of the parameter.
                    match inner.next() {
                        Some(TokenTree::Lexical { text, span }) => Dr::ok(PLambdaBinder {
                            name: Name(WithProvenance::new_with_provenance(
                                inner.provenance(span),
                                Str::new(inner.config().db, text),
                            )),
                            annotation: bracket.into(),
                            brackets: Some((open, close)),
                            ownership,
                            ty: None,
                        }),
                        _ => todo!(),
                    }
                } else {
                    // This is a binder which explicitly declares its type.
                    // The form is `name : type`.
                    let name = if let Some(TokenTree::Lexical { text, span }) = inner.next() {
                        Name(WithProvenance::new_with_provenance(
                            inner.provenance(span),
                            Str::new(inner.config().db, text),
                        ))
                    } else {
                        todo!()
                    };
                    inner
                        .require_reserved(ReservedSymbol::Colon)
                        .bind(|_| inner.parse_expr())
                        .bind(|ty| {
                            inner.assert_end().map(|()| PLambdaBinder {
                                name,
                                annotation: bracket.into(),
                                brackets: Some((open, close)),
                                ownership,
                                ty: Some(ty),
                            })
                        })
                }
            }
            Some(tt) => Dr::fail(
                Report::new(ReportKind::Error, self.config().source, tt.span().start)
                    .with_message(message!["expected a parameter name, but found ", &tt])
                    .with_label(
                        Label::new(self.config().source, tt.span(), LabelType::Error)
                            .with_message("expected a parameter name".into()),
                    )
                    .with_label(
                        Label::new(self.config().source, fn_token, LabelType::Note)
                            .with_message("while parsing this function".into()),
                    )
                    .with_note(
                        "use '=>' to end the sequence of parameters and begin the function body"
                            .into(),
                    ),
            ),
            None => todo!(),
        }
    }

    /// Assuming that the next token is a `fn`, parse a `fn <binders> => e` expression.
    fn parse_fn_expr(&mut self) -> Dr<PExpression> {
        let fn_token = self.next().unwrap().span();

        // Parse one or more binders.
        let mut binders = Vec::new();
        loop {
            match self.peek() {
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::DoubleArrow,
                    ..
                }) => {
                    self.next();
                    break;
                }
                _ => {
                    let binder = self.parse_lambda_binder(fn_token);
                    let errored = binder.errored();
                    binders.push(binder);
                    if errored {
                        break;
                    }
                }
            }
        }

        Dr::sequence(binders).bind(|binders| {
            // TODO: Check that there is at least one binder?
            self.parse_expr().map(|result| PExpression::Lambda {
                fn_token,
                binders,
                result: Box::new(result),
            })
        })
    }

    /// Parses syntax of the form `ownership? name : type` or `ownership? type`.
    fn parse_function_binder(
        &mut self,
        annotation: BinderAnnotation,
        brackets: Option<(Span, Span)>,
    ) -> Dr<PFunctionBinder> {
        // Parse an ownership token if one exists.
        let ownership = self.parse_ownership();

        // Look ahead two token trees to check if it is a `:` token.
        let tt = if let Some(tt) = self.next() {
            tt
        } else {
            todo!("binders should be nonempty")
        };

        if let Some(TokenTree::Reserved {
            symbol: ReservedSymbol::Colon,
            ..
        }) = self.peek()
        {
            // This is syntax of the form `name : type`.
            // `tt` is a lexical token, representing the name of the function.
            // Consume the token.
            self.next();
            if let TokenTree::Lexical { text, span } = tt {
                // Parse the type of the parameter.
                self.parse_expr().bind(|ty| {
                    self.assert_end().map(|()| PFunctionBinder {
                        name: Some(Name(WithProvenance::new_with_provenance(
                            self.provenance(span),
                            Str::new(self.config().db, text),
                        ))),
                        annotation,
                        brackets,
                        ownership,
                        ty: Box::new(ty),
                    })
                })
            } else {
                todo!()
            }
        } else {
            // This is syntax of the form `type`.
            self.push(tt);
            self.parse_expr().bind(|ty| {
                self.assert_end().map(|()| PFunctionBinder {
                    name: None,
                    annotation,
                    brackets,
                    ownership,
                    ty: Box::new(ty),
                })
            })
        }
    }

    /// An expression is:
    /// - a lambda, written `fn <binders> => e`;
    /// - a function type, written `<binder> -> e`; or
    /// - a Pratt expression.
    pub fn parse_expr(&mut self) -> Dr<PExpression> {
        let result = match self.peek() {
            Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Fn,
                ..
            }) => self.parse_fn_expr(),
            Some(TokenTree::Block { .. }) => {
                // We can check if this is a function type by peeking at the token tree after this block.
                let block = self.next().unwrap();

                if let Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Arrow,
                    span,
                }) = self.peek()
                {
                    let arrow_token = *span;
                    // This is a function type.
                    // Consume the arrow token.
                    self.next();
                    if let TokenTree::Block {
                        bracket,
                        open,
                        close,
                        contents,
                    } = block
                    {
                        let mut inner = self.with_vec(open, close, contents);
                        inner
                            .parse_function_binder(bracket.into(), Some((open, close)))
                            .bind(|binder| {
                                self.parse_expr().map(|result| PExpression::FunctionType {
                                    binder,
                                    arrow_token,
                                    result: Box::new(result),
                                })
                            })
                    } else {
                        unreachable!()
                    }
                } else {
                    // This wasn't a function type.
                    // Push the block back, and fall back to the Pratt expression parser.
                    self.push(block);
                    self.parse_pratt_expr()
                }
            }
            _ => self.parse_pratt_expr(),
        };

        // After we parse the initial expression, it's possible that we have an arrow token `->`
        // defining a function type.
        result.bind(|expr| {
            if let Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Arrow,
                span,
            }) = self.peek()
            {
                let arrow_token = *span;
                self.next();
                self.parse_expr().map(|result| PExpression::FunctionType {
                    binder: PFunctionBinder {
                        name: None,
                        annotation: BinderAnnotation::Explicit,
                        brackets: None,
                        ownership: None,
                        ty: Box::new(expr),
                    },
                    arrow_token,
                    result: Box::new(result),
                })
            } else {
                Dr::ok(expr)
            }
        })
    }
}
