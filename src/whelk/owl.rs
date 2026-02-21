use crate::whelk::model::{
    ConceptData, ConceptId, ConceptInclusion, HashSet, Interner, RoleComposition, RoleInclusion,
    TranslatedOntology, COMPOSITION_ROLE_PREFIX,
};
use horned_owl::model as hm;
use horned_owl::model::ForIRI;
use horned_owl::ontology::set::SetOntology;
use itertools::Itertools;

struct AxiomSet {
    concept_inclusions: HashSet<ConceptInclusion>,
    role_inclusions: HashSet<RoleInclusion>,
    role_compositions: HashSet<RoleComposition>,
}

impl AxiomSet {
    fn new() -> Self {
        AxiomSet {
            concept_inclusions: Default::default(),
            role_inclusions: Default::default(),
            role_compositions: Default::default(),
        }
    }

    fn ci(ci: ConceptInclusion) -> Self {
        AxiomSet {
            concept_inclusions: std::iter::once(ci).collect(),
            role_inclusions: Default::default(),
            role_compositions: Default::default(),
        }
    }

    fn union(self, other: Self) -> Self {
        AxiomSet {
            concept_inclusions: self.concept_inclusions.union(other.concept_inclusions),
            role_inclusions: self.role_inclusions.union(other.role_inclusions),
            role_compositions: self.role_compositions.union(other.role_compositions),
        }
    }
}

pub fn translate_ontology<A: ForIRI>(ontology: &SetOntology<A>) -> TranslatedOntology {
    let mut interner = Interner::new();
    let mut result = AxiomSet::new();
    for ann_axiom in ontology.iter() {
        let axioms = translate_axiom_internal(&ann_axiom.axiom, &mut interner);
        result = result.union(axioms);
    }
    TranslatedOntology {
        interner,
        concept_inclusions: result.concept_inclusions,
        role_inclusions: result.role_inclusions,
        role_compositions: result.role_compositions,
    }
}

fn translate_axiom_internal<A: ForIRI>(axiom: &hm::Axiom<A>, interner: &mut Interner) -> AxiomSet {
    let thing = interner.top();
    let nothing = interner.bottom();
    match axiom {
        hm::Axiom::DeclareClass(hm::DeclareClass(hm::Class(iri))) => {
            let subclass = interner.intern_concept(ConceptData::AtomicConcept(iri.to_string()));
            AxiomSet::ci(ConceptInclusion { subclass, superclass: thing })
        }
        hm::Axiom::DeclareNamedIndividual(hm::DeclareNamedIndividual(hm::NamedIndividual(iri))) => {
            let ind = interner.intern_individual(iri.as_ref());
            let subclass = interner.intern_concept(ConceptData::Nominal(ind));
            AxiomSet::ci(ConceptInclusion { subclass, superclass: thing })
        }
        hm::Axiom::SubClassOf(ax) => {
            match (convert_expression(&ax.sub, interner), convert_expression(&ax.sup, interner)) {
                (Some(subclass), Some(superclass)) => AxiomSet::ci(ConceptInclusion { subclass, superclass }),
                _ => AxiomSet::new(),
            }
        }
        hm::Axiom::EquivalentClasses(hm::EquivalentClasses(expressions)) => {
            let converted: Vec<ConceptId> = expressions.iter().filter_map(|c| convert_expression(c, interner)).collect();
            let mut result = AxiomSet::new();
            for pair in converted.iter().combinations(2) {
                let first = *pair[0];
                let second = *pair[1];
                if first != nothing {
                    result.concept_inclusions.insert(ConceptInclusion { subclass: first, superclass: second });
                }
                if second != nothing {
                    result.concept_inclusions.insert(ConceptInclusion { subclass: second, superclass: first });
                }
            }
            result
        }
        hm::Axiom::DisjointClasses(hm::DisjointClasses(operands)) => {
            let converted: Vec<ConceptId> = operands.iter().filter_map(|c| convert_expression(c, interner)).collect();
            let mut result = AxiomSet::new();
            for pair in converted.iter().combinations(2) {
                let first = *pair[0];
                let second = *pair[1];
                let conjunction = interner.intern_concept(ConceptData::Conjunction { left: first, right: second });
                result.concept_inclusions.insert(ConceptInclusion { subclass: conjunction, superclass: nothing });
            }
            result
        }
        hm::Axiom::DisjointUnion(hm::DisjointUnion(cls, expressions)) => {
            let union = hm::ClassExpression::ObjectUnionOf(expressions.clone());
            let equivalence = hm::Axiom::EquivalentClasses(hm::EquivalentClasses(vec![hm::ClassExpression::Class(cls.clone()), union]));
            let disjointness = hm::Axiom::DisjointClasses(hm::DisjointClasses(expressions.clone()));
            translate_axiom_internal(&equivalence, interner).union(translate_axiom_internal(&disjointness, interner))
        }
        hm::Axiom::SubObjectPropertyOf(hm::SubObjectPropertyOf {
            sub: hm::SubObjectPropertyExpression::ObjectPropertyExpression(hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(sub))),
            sup: hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(sup)),
        }) => {
            let subproperty = interner.intern_role(sub.as_ref());
            let superproperty = interner.intern_role(sup.as_ref());
            AxiomSet {
                concept_inclusions: Default::default(),
                role_inclusions: std::iter::once(RoleInclusion { subproperty, superproperty }).collect(),
                role_compositions: Default::default(),
            }
        }
        hm::Axiom::SubObjectPropertyOf(hm::SubObjectPropertyOf {
            sub: hm::SubObjectPropertyExpression::ObjectPropertyChain(props),
            sup: hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(sup)),
        }) => {
            if props.iter().all(|p| matches!(p, hm::ObjectPropertyExpression::ObjectProperty(_))) {
                let props_len = props.len();
                match props_len {
                    0 => AxiomSet::new(),
                    1 => {
                        let sub = props.first().unwrap().clone();
                        let axiom = hm::Axiom::SubObjectPropertyOf(hm::SubObjectPropertyOf {
                            sub: hm::SubObjectPropertyExpression::ObjectPropertyExpression(sub),
                            sup: hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(sup.clone())),
                        });
                        translate_axiom_internal(&axiom, interner)
                    }
                    _ => match (props.first(), props.get(1)) {
                        (
                            Some(hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(first_id))),
                            Some(hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(second_id))),
                        ) => {
                            if props_len < 3 {
                                let first = interner.intern_role(first_id.as_ref());
                                let second = interner.intern_role(second_id.as_ref());
                                let superproperty = interner.intern_role(sup.as_ref());
                                AxiomSet {
                                    concept_inclusions: Default::default(),
                                    role_inclusions: Default::default(),
                                    role_compositions: std::iter::once(RoleComposition { first, second, superproperty }).collect(),
                                }
                            } else {
                                let composition_property_id = format!("{}{}:{}", COMPOSITION_ROLE_PREFIX, first_id, second_id);
                                let comp_iri = hm::Build::new().iri(composition_property_id);
                                let composition_property = hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(comp_iri));
                                let beginning_chain = translate_axiom_internal(
                                    &hm::Axiom::SubObjectPropertyOf(hm::SubObjectPropertyOf {
                                        sub: hm::SubObjectPropertyExpression::ObjectPropertyChain(vec![
                                            hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(first_id.clone())),
                                            hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(second_id.clone())),
                                        ]),
                                        sup: composition_property.clone(),
                                    }),
                                    interner,
                                );
                                let mut new_chain = props.clone();
                                new_chain.remove(0);
                                new_chain.remove(0);
                                new_chain.insert(0, composition_property);
                                let rest_of_chain = translate_axiom_internal(
                                    &hm::Axiom::SubObjectPropertyOf(hm::SubObjectPropertyOf {
                                        sub: hm::SubObjectPropertyExpression::ObjectPropertyChain(new_chain),
                                        sup: hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(sup.clone())),
                                    }),
                                    interner,
                                );
                                beginning_chain.union(rest_of_chain)
                            }
                        }
                        _ => AxiomSet::new(),
                    },
                }
            } else {
                AxiomSet::new()
            }
        }
        hm::Axiom::EquivalentObjectProperties(hm::EquivalentObjectProperties(props)) => {
            let mut result = AxiomSet::new();
            for pair in props.iter().combinations(2) {
                let first_second = hm::Axiom::SubObjectPropertyOf(hm::SubObjectPropertyOf {
                    sub: hm::SubObjectPropertyExpression::ObjectPropertyExpression(pair[0].clone()),
                    sup: pair[1].clone(),
                });
                let second_first = hm::Axiom::SubObjectPropertyOf(hm::SubObjectPropertyOf {
                    sub: hm::SubObjectPropertyExpression::ObjectPropertyExpression(pair[1].clone()),
                    sup: pair[0].clone(),
                });
                result = result
                    .union(translate_axiom_internal(&first_second, interner))
                    .union(translate_axiom_internal(&second_first, interner));
            }
            result
        }
        hm::Axiom::ObjectPropertyDomain(hm::ObjectPropertyDomain {
            ope: hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(prop)),
            ce: cls,
        }) => {
            if let Some(superclass) = convert_expression(cls, interner) {
                let role = interner.intern_role(prop.as_ref());
                let restriction = interner.intern_concept(ConceptData::ExistentialRestriction { role, concept: thing });
                AxiomSet::ci(ConceptInclusion { subclass: restriction, superclass })
            } else {
                AxiomSet::new()
            }
        }
        hm::Axiom::TransitiveObjectProperty(hm::TransitiveObjectProperty(prop)) => translate_axiom_internal(
            &hm::Axiom::SubObjectPropertyOf(hm::SubObjectPropertyOf {
                sub: hm::SubObjectPropertyExpression::ObjectPropertyChain(vec![prop.clone(), prop.clone()]),
                sup: prop.clone(),
            }),
            interner,
        ),
        hm::Axiom::ClassAssertion(hm::ClassAssertion {
            ce: cls,
            i: hm::Individual::Named(hm::NamedIndividual(ind)),
        }) => {
            if let Some(superclass) = convert_expression(cls, interner) {
                let individual = interner.intern_individual(ind.as_ref());
                let subclass = interner.intern_concept(ConceptData::Nominal(individual));
                AxiomSet::ci(ConceptInclusion { subclass, superclass })
            } else {
                AxiomSet::new()
            }
        }
        hm::Axiom::ObjectPropertyAssertion(hm::ObjectPropertyAssertion {
            ope: property_expression,
            from: hm::Individual::Named(hm::NamedIndividual(axiom_subject)),
            to: hm::Individual::Named(hm::NamedIndividual(axiom_target)),
        }) => {
            let (subject, prop, target) = match property_expression {
                hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(prop)) => (axiom_subject, prop, axiom_target),
                hm::ObjectPropertyExpression::InverseObjectProperty(hm::ObjectProperty(prop)) => (axiom_target, prop, axiom_subject),
            };
            let subject_ind = interner.intern_individual(subject.as_ref());
            let target_ind = interner.intern_individual(target.as_ref());
            let subclass = interner.intern_concept(ConceptData::Nominal(subject_ind));
            let target_nominal = interner.intern_concept(ConceptData::Nominal(target_ind));
            let role = interner.intern_role(prop.as_ref());
            let superclass = interner.intern_concept(ConceptData::ExistentialRestriction { role, concept: target_nominal });
            AxiomSet::ci(ConceptInclusion { subclass, superclass })
        }
        _ => AxiomSet::new(),
    }
}

pub fn convert_expression<A: ForIRI>(expression: &hm::ClassExpression<A>, interner: &mut Interner) -> Option<ConceptId> {
    match expression {
        hm::ClassExpression::Class(hm::Class(iri)) => {
            Some(interner.intern_concept(ConceptData::AtomicConcept(iri.to_string())))
        }
        hm::ClassExpression::ObjectSomeValuesFrom {
            ope: hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(prop)),
            bce: cls,
        } => {
            convert_expression(cls, interner).map(|concept| {
                let role = interner.intern_role(prop.as_ref());
                interner.intern_concept(ConceptData::ExistentialRestriction { role, concept })
            })
        }
        hm::ClassExpression::ObjectIntersectionOf(expressions) => {
            let mut expressions = expressions.clone();
            expressions.sort_by(|a, b| b.cmp(a));
            let converted: Option<Vec<ConceptId>> = expressions.iter().map(|cls| convert_expression(cls, interner)).collect();
            converted.and_then(|operands| expand_conjunction(operands, interner))
        }
        hm::ClassExpression::ObjectComplementOf(cls) => {
            convert_expression(cls, interner).map(|concept| interner.intern_concept(ConceptData::Complement(concept)))
        }
        _ => None,
    }
}

fn expand_conjunction(mut operands: Vec<ConceptId>, interner: &mut Interner) -> Option<ConceptId> {
    match operands.len() {
        0 => None,
        1 => operands.pop(),
        2 => {
            let left = operands.pop().unwrap();
            let right = operands.pop().unwrap();
            Some(interner.intern_concept(ConceptData::Conjunction { left, right }))
        }
        _ => {
            let left = operands.pop().unwrap();
            expand_conjunction(operands, interner).map(|right| {
                interner.intern_concept(ConceptData::Conjunction { left, right })
            })
        }
    }
}
