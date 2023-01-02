use super::*;

impl<'cache> Expression<'cache> {
    pub fn to_heap(&self, cache: &ExpressionCache<'cache>) -> HeapExpression {
        match self.value(cache) {
            ExpressionT::Local(e) => {
                HeapExpression::new(self.provenance(cache), ExpressionT::Local(e))
            }
            ExpressionT::Borrow(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::Borrow(Borrow {
                    region: (e.region.to_heap(cache)),
                    value: (e.value.to_heap(cache)),
                }),
            ),
            ExpressionT::Dereference(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::Dereference(Dereference {
                    value: (e.value.to_heap(cache)),
                }),
            ),
            ExpressionT::Delta(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::Delta(Delta {
                    region: (e.region.to_heap(cache)),
                    ty: (e.ty.to_heap(cache)),
                }),
            ),
            ExpressionT::Inst(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::Inst(Inst {
                    name: e.name.clone(),
                    universes: e.universes,
                }),
            ),
            ExpressionT::Let(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::Let(Let {
                    bound: e.bound.to_heap(cache),
                    to_assign: (e.to_assign.to_heap(cache)),
                    body: (e.body.to_heap(cache)),
                }),
            ),
            ExpressionT::Lambda(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::Lambda(Binder {
                    structure: e.structure.to_heap(cache),
                    result: (e.result.to_heap(cache)),
                }),
            ),
            ExpressionT::Pi(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::Pi(Binder {
                    structure: e.structure.to_heap(cache),
                    result: (e.result.to_heap(cache)),
                }),
            ),
            ExpressionT::RegionLambda(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::RegionLambda(RegionBinder {
                    region_name: e.region_name,
                    body: (e.body.to_heap(cache)),
                }),
            ),
            ExpressionT::RegionPi(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::RegionPi(RegionBinder {
                    region_name: e.region_name,
                    body: (e.body.to_heap(cache)),
                }),
            ),
            ExpressionT::Apply(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::Apply(Apply {
                    function: (e.function.to_heap(cache)),
                    argument: (e.argument.to_heap(cache)),
                }),
            ),
            ExpressionT::Intro(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::Intro(Intro {
                    inductive: e.inductive.clone(),
                    universes: e.universes.clone(),
                    variant: e.variant,
                    parameters: e
                        .parameters
                        .iter()
                        .map(|param| param.to_heap(cache))
                        .collect(),
                }),
            ),
            ExpressionT::Match(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::Match(Match {
                    major_premise: (e.major_premise.to_heap(cache)),
                    index_params: e.index_params,
                    motive: (e.motive.to_heap(cache)),
                    minor_premises: e
                        .minor_premises
                        .iter()
                        .map(|premise| MinorPremise {
                            variant: premise.variant,
                            fields: premise.fields,
                            result: premise.result.to_heap(cache),
                        })
                        .collect(),
                }),
            ),
            ExpressionT::Fix(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::Fix(Fix {
                    argument: (e.argument.to_heap(cache)),
                    argument_name: e.argument_name,
                    fixpoint: e.fixpoint.to_heap(cache),
                    body: (e.body.to_heap(cache)),
                }),
            ),
            ExpressionT::Sort(e) => {
                HeapExpression::new(self.provenance(cache), ExpressionT::Sort(e))
            }
            ExpressionT::Region => HeapExpression::new(self.provenance(cache), ExpressionT::Region),
            ExpressionT::RegionT => {
                HeapExpression::new(self.provenance(cache), ExpressionT::RegionT)
            }
            ExpressionT::StaticRegion => {
                HeapExpression::new(self.provenance(cache), ExpressionT::StaticRegion)
            }
            ExpressionT::Lifespan(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::Lifespan(Lifespan {
                    ty: (e.ty.to_heap(cache)),
                }),
            ),
            ExpressionT::Metavariable(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::Metavariable(Metavariable {
                    index: e.index,
                    ty: (e.ty.to_heap(cache)),
                }),
            ),
            ExpressionT::LocalConstant(e) => HeapExpression::new(
                self.provenance(cache),
                ExpressionT::LocalConstant(LocalConstant {
                    metavariable: Metavariable {
                        index: e.metavariable.index,
                        ty: (e.metavariable.ty.to_heap(cache)),
                    },
                    structure: e.structure.to_heap(cache),
                }),
            ),
        }
    }
}

impl HeapExpression {
    pub fn from_heap<'cache>(&self, cache: &ExpressionCache<'cache>) -> Expression<'cache> {
        let body = match &*self.value.contents {
            ExpressionT::Local(e) => ExpressionT::Local(*e),
            ExpressionT::Borrow(e) => ExpressionT::Borrow(Borrow {
                region: e.region.from_heap(cache),
                value: e.value.from_heap(cache),
            }),

            ExpressionT::Dereference(e) => ExpressionT::Dereference(Dereference {
                value: e.value.from_heap(cache),
            }),

            ExpressionT::Delta(e) => ExpressionT::Delta(Delta {
                region: e.region.from_heap(cache),
                ty: e.ty.from_heap(cache),
            }),
            ExpressionT::Inst(e) => ExpressionT::Inst(Inst {
                name: e.name.clone(),
                universes: e.universes.clone(),
            }),

            ExpressionT::Let(e) => ExpressionT::Let(Let {
                bound: e.bound.from_heap(cache),
                to_assign: e.to_assign.from_heap(cache),
                body: e.body.from_heap(cache),
            }),

            ExpressionT::Lambda(e) => ExpressionT::Lambda(Binder {
                structure: e.structure.from_heap(cache),
                result: e.result.from_heap(cache),
            }),

            ExpressionT::Pi(e) => ExpressionT::Pi(Binder {
                structure: e.structure.from_heap(cache),
                result: e.result.from_heap(cache),
            }),

            ExpressionT::RegionLambda(e) => ExpressionT::RegionLambda(RegionBinder {
                region_name: e.region_name,
                body: e.body.from_heap(cache),
            }),

            ExpressionT::RegionPi(e) => ExpressionT::RegionPi(RegionBinder {
                region_name: e.region_name,
                body: e.body.from_heap(cache),
            }),

            ExpressionT::Apply(e) => ExpressionT::Apply(Apply {
                function: e.function.from_heap(cache),
                argument: e.argument.from_heap(cache),
            }),

            ExpressionT::Intro(e) => ExpressionT::Intro(Intro {
                inductive: e.inductive.clone(),
                universes: e.universes.clone(),
                variant: e.variant,
                parameters: e.parameters.iter().map(|e| e.from_heap(cache)).collect(),
            }),
            ExpressionT::Match(e) => ExpressionT::Match(Match {
                major_premise: e.major_premise.from_heap(cache),
                index_params: e.index_params,
                motive: e.motive.from_heap(cache),
                minor_premises: e
                    .minor_premises
                    .iter()
                    .map(|premise| MinorPremise {
                        variant: premise.variant,
                        fields: premise.fields,
                        result: premise.result.from_heap(cache),
                    })
                    .collect(),
            }),

            ExpressionT::Fix(e) => ExpressionT::Fix(Fix {
                argument: e.argument.from_heap(cache),
                argument_name: e.argument_name,
                fixpoint: e.fixpoint.from_heap(cache),
                body: e.body.from_heap(cache),
            }),
            ExpressionT::Sort(e) => ExpressionT::Sort(e.clone()),
            ExpressionT::Region => ExpressionT::Region,
            ExpressionT::RegionT => ExpressionT::RegionT,
            ExpressionT::StaticRegion => ExpressionT::StaticRegion,
            ExpressionT::Lifespan(e) => ExpressionT::Lifespan(Lifespan {
                ty: e.ty.from_heap(cache),
            }),

            ExpressionT::Metavariable(e) => ExpressionT::Metavariable(Metavariable {
                index: e.index,
                ty: e.ty.from_heap(cache),
            }),

            ExpressionT::LocalConstant(e) => ExpressionT::LocalConstant(LocalConstant {
                metavariable: Metavariable {
                    index: e.metavariable.index,
                    ty: e.metavariable.ty.from_heap(cache),
                },
                structure: e.structure.from_heap(cache),
            }),
        };

        Expression::new(cache, self.value.provenance, body)
    }
}
