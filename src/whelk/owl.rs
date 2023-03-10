use crate::whelk::model as wm;
use horned_owl::model as hm;
use horned_owl::model::ForIRI;
use horned_owl::ontology::set::SetOntology;
use im::HashSet;
use itertools::Itertools;
use std::rc::Rc;

struct OWLGlobals {
    thing: Rc<wm::Concept>,
    nothing: Rc<wm::Concept>,
}

pub fn translate_ontology<A: ForIRI>(ontology: &SetOntology<A>) -> HashSet<wm::Axiom> {
    let globals = make_globals();
    ontology.iter().flat_map(|ann_axiom| translate_axiom_internal(&ann_axiom.axiom, &globals)).collect()
}

fn make_globals() -> OWLGlobals {
    OWLGlobals {
        thing: Rc::new(wm::Concept::AtomicConcept(Rc::new(wm::AtomicConcept { id: wm::TOP.to_string() }))),
        nothing: Rc::new(wm::Concept::AtomicConcept(Rc::new(wm::AtomicConcept { id: wm::BOTTOM.to_string() }))),
    }
}

pub fn translate_axiom<A: ForIRI>(axiom: &hm::Axiom<A>) -> HashSet<wm::Axiom> {
    translate_axiom_internal(axiom, &make_globals())
}

fn translate_axiom_internal<A: ForIRI>(axiom: &hm::Axiom<A>, globals: &OWLGlobals) -> HashSet<wm::Axiom> {
    match axiom {
        hm::Axiom::DeclareClass(hm::DeclareClass(hm::Class(iri))) => {
            let subclass = Rc::new(wm::Concept::AtomicConcept(Rc::new(wm::AtomicConcept { id: iri.to_string() })));
            HashSet::unit(concept_inclusion(&subclass, &globals.thing))
        }
        hm::Axiom::DeclareNamedIndividual(hm::DeclareNamedIndividual(hm::NamedIndividual(iri))) => {
            let individual = Rc::new(wm::Individual { id: iri.to_string() });
            let subclass = Rc::new(wm::Concept::Nominal(Rc::new(wm::Nominal { individual })));
            HashSet::unit(concept_inclusion(&subclass, &globals.thing))
        }
        hm::Axiom::SubClassOf(ax) => match (convert_expression(&ax.sub), convert_expression(&ax.sup)) {
            (Some(subclass), Some(superclass)) => HashSet::unit(concept_inclusion(&subclass, &superclass)),
            _ => Default::default(),
        },
        hm::Axiom::EquivalentClasses(hm::EquivalentClasses(expressions)) => expressions
            .iter()
            .filter_map(|c| convert_expression(&c))
            .combinations(2)
            .flat_map(|pair| {
                let first_opt = pair.get(0);
                let second_opt = pair.get(1);
                match (first_opt, second_opt) {
                    (Some(first), Some(second)) => {
                        let mut axioms = HashSet::new();
                        if first != &globals.nothing {
                            axioms.insert(concept_inclusion(first, second));
                        }
                        if second != &globals.nothing {
                            axioms.insert(concept_inclusion(second, first));
                        }
                        axioms
                    }
                    _ => Default::default(),
                }
            })
            .collect(),
        hm::Axiom::DisjointClasses(hm::DisjointClasses(operands)) => operands
            .iter()
            .map(|c| convert_expression(c))
            .filter_map(|opt| opt)
            .combinations(2)
            .flat_map(|pair| {
                let first_opt = pair.get(0);
                let second_opt = pair.get(1);
                match (first_opt, second_opt) {
                    (Some(first), Some(second)) => {
                        let conjunction = Rc::new(wm::Concept::Conjunction(Rc::new(wm::Conjunction { left: Rc::clone(first), right: Rc::clone(second) })));
                        HashSet::unit(concept_inclusion(&conjunction, &globals.nothing))
                    }
                    _ => Default::default(),
                }
            })
            .collect(),
        hm::Axiom::DisjointUnion(hm::DisjointUnion(cls, expressions)) => {
            let union = hm::ClassExpression::ObjectUnionOf(expressions.clone());
            let equivalence = hm::Axiom::EquivalentClasses(hm::EquivalentClasses(vec![hm::ClassExpression::Class(cls.clone()), union]));
            let disjointness = hm::Axiom::DisjointClasses(hm::DisjointClasses(expressions.clone()));
            translate_axiom_internal(&equivalence, globals).union(translate_axiom_internal(&disjointness, globals))
        }
        hm::Axiom::SubObjectPropertyOf(hm::SubObjectPropertyOf {
            sub: hm::SubObjectPropertyExpression::ObjectPropertyExpression(hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(sub))),
            sup: hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(sup)),
        }) => {
            let sub_role = Rc::new(wm::Role { id: sub.to_string() });
            let sup_role = Rc::new(wm::Role { id: sup.to_string() });
            HashSet::unit(wm::Axiom::RoleInclusion(Rc::new(wm::RoleInclusion { subproperty: sub_role, superproperty: sup_role })))
        }
        hm::Axiom::SubObjectPropertyOf(hm::SubObjectPropertyOf {
            sub: hm::SubObjectPropertyExpression::ObjectPropertyChain(props),
            sup: hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(sup)),
        }) => {
            if props.iter().all(|p| match p {
                hm::ObjectPropertyExpression::ObjectProperty(_) => true,
                hm::ObjectPropertyExpression::InverseObjectProperty(_) => false,
            }) {
                let props_len = props.len();
                match props_len {
                    0 => Default::default(),
                    1 => {
                        let sub = props.get(0).unwrap().clone();
                        let axiom = hm::Axiom::SubObjectPropertyOf(hm::SubObjectPropertyOf {
                            sub: hm::SubObjectPropertyExpression::ObjectPropertyExpression(sub),
                            sup: hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(sup.clone())),
                        });
                        translate_axiom_internal(&axiom, globals)
                    }
                    _ => match (props.get(0), props.get(1)) {
                        (
                            Some(hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(first_id))),
                            Some(hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(second_id))),
                        ) => {
                            if props_len < 3 {
                                HashSet::unit(wm::Axiom::RoleComposition(Rc::new(wm::RoleComposition {
                                    first: Rc::new(wm::Role { id: first_id.to_string() }),
                                    second: Rc::new(wm::Role { id: second_id.to_string() }),
                                    superproperty: Rc::new(wm::Role { id: sup.to_string() }),
                                })))
                            } else {
                                let composition_property_id = format!("{}{}:{}", wm::Role::composition_role_prefix(), first_id, second_id);
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
                                    globals,
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
                                    globals,
                                );
                                beginning_chain.union(rest_of_chain)
                            }
                        }
                        _ => Default::default(),
                    },
                }
            } else {
                Default::default()
            }
        }
        hm::Axiom::EquivalentObjectProperties(hm::EquivalentObjectProperties(props)) => props
            .iter()
            .combinations(2)
            .flat_map(|pair| {
                let first_opt = pair.get(0);
                let second_opt = pair.get(1);
                match (first_opt, second_opt) {
                    (Some(first), Some(second)) => {
                        let first_second = hm::Axiom::SubObjectPropertyOf(hm::SubObjectPropertyOf {
                            sub: hm::SubObjectPropertyExpression::ObjectPropertyExpression(first.clone().clone()),
                            sup: second.clone().clone(),
                        });
                        let second_first = hm::Axiom::SubObjectPropertyOf(hm::SubObjectPropertyOf {
                            sub: hm::SubObjectPropertyExpression::ObjectPropertyExpression(second.clone().clone()),
                            sup: first.clone().clone(),
                        });
                        translate_axiom_internal(&first_second, globals).union(translate_axiom_internal(&second_first, globals))
                    }
                    _ => Default::default(),
                }
            })
            .collect(),
        hm::Axiom::ObjectPropertyDomain(hm::ObjectPropertyDomain { ope: hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(prop)), ce: cls }) => {
            convert_expression(cls)
                .iter()
                .map(|c| {
                    let restriction = Rc::new(wm::Concept::ExistentialRestriction(Rc::new(wm::ExistentialRestriction {
                        role: Rc::new(wm::Role { id: prop.to_string() }),
                        concept: Rc::clone(&globals.thing),
                    })));
                    concept_inclusion(&restriction, &c)
                })
                .collect()
        }
        // hm::Axiom::ObjectPropertyRange(_) => {} //TODO
        // hm::Axiom::DisjointObjectProperties(_) => {}
        // hm::Axiom::InverseObjectProperties(_) => {}
        // hm::Axiom::FunctionalObjectProperty(_) => {}
        // hm::Axiom::InverseFunctionalObjectProperty(_) => {}
        // hm::Axiom::ReflexiveObjectProperty(_) => {}
        // hm::Axiom::IrreflexiveObjectProperty(_) => {}
        // hm::Axiom::SymmetricObjectProperty(_) => {}
        // hm::Axiom::AsymmetricObjectProperty(_) => {}
        hm::Axiom::TransitiveObjectProperty(hm::TransitiveObjectProperty(prop)) => translate_axiom_internal(
            &hm::Axiom::SubObjectPropertyOf(hm::SubObjectPropertyOf {
                sub: hm::SubObjectPropertyExpression::ObjectPropertyChain(vec![prop.clone(), prop.clone()]),
                sup: prop.clone(),
            }),
            globals,
        ),
        // hm::Axiom::SameIndividual(_) => {} //TODO
        // hm::Axiom::DifferentIndividuals(_) => {} //TODO
        hm::Axiom::ClassAssertion(hm::ClassAssertion { ce: cls, i: hm::Individual::Named(hm::NamedIndividual(ind)) }) => convert_expression(cls)
            .iter()
            .flat_map(|superclass| {
                let individual = Rc::new(wm::Individual { id: ind.to_string() });
                let subclass = Rc::new(wm::Concept::Nominal(Rc::new(wm::Nominal { individual })));
                HashSet::unit(concept_inclusion(&subclass, superclass))
            })
            .collect(),
        hm::Axiom::ObjectPropertyAssertion(hm::ObjectPropertyAssertion {
            ope: property_expression,
            from: hm::Individual::Named(hm::NamedIndividual(axiom_subject)),
            to: hm::Individual::Named(hm::NamedIndividual(axiom_target)),
        }) => {
            let (subject, prop, target) = match property_expression {
                hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(prop)) => (axiom_subject, prop, axiom_target),
                hm::ObjectPropertyExpression::InverseObjectProperty(hm::ObjectProperty(prop)) => (axiom_target, prop, axiom_subject),
            };
            let subclass = Rc::new(wm::Concept::Nominal(Rc::new(wm::Nominal { individual: Rc::new(wm::Individual { id: subject.to_string() }) })));
            let target_nominal = Rc::new(wm::Concept::Nominal(Rc::new(wm::Nominal { individual: Rc::new(wm::Individual { id: target.to_string() }) })));
            let superclass =
                Rc::new(wm::Concept::ExistentialRestriction(Rc::new(wm::ExistentialRestriction { role: Rc::new(wm::Role { id: prop.to_string() }), concept: target_nominal })));
            HashSet::unit(concept_inclusion(&subclass, &superclass))
        }
        // hm::Axiom::NegativeObjectPropertyAssertion(_) => {} //TODO
        // hm::Axiom::SubDataPropertyOf(_) => {}
        // hm::Axiom::EquivalentDataProperties(_) => {}
        // hm::Axiom::DisjointDataProperties(_) => {}
        // hm::Axiom::DataPropertyDomain(_) => {}
        // hm::Axiom::DataPropertyRange(_) => {}
        // hm::Axiom::FunctionalDataProperty(_) => {}
        // hm::Axiom::DatatypeDefinition(_) => {}
        // hm::Axiom::HasKey(_) => {}
        // hm::Axiom::DataPropertyAssertion(_) => {}
        // hm::Axiom::NegativeDataPropertyAssertion(_) => {}
        _ => Default::default(),
    }
}

fn concept_inclusion(subclass: &Rc<wm::Concept>, superclass: &Rc<wm::Concept>) -> wm::Axiom {
    wm::Axiom::ConceptInclusion(Rc::new(wm::ConceptInclusion { subclass: Rc::clone(subclass), superclass: Rc::clone(superclass) }))
}

//       case ObjectHasSelf(ObjectProperty(prop))                        => Some(SelfRestriction(Role(prop.toString)))
//       case ObjectUnionOf(operands)                                    =>
//         operands.toList.map(convertExpression).sequence.map(_.toSet).map(Disjunction)
//       case ObjectOneOf(individuals) if individuals.size == 1          => individuals.collectFirst { case NamedIndividual(iri) => Nominal(WIndividual(iri.toString)) }
//       case ObjectHasValue(ObjectProperty(prop), NamedIndividual(ind)) => Some(ExistentialRestriction(Role(prop.toString), Nominal(WIndividual(ind.toString))))
//       case DataSomeValuesFrom(DataProperty(prop), range)              => Some(DataRestriction(DataRole(prop.toString), DataRange(range)))
//       //scowl is missing DataHasValue
//       case dhv: OWLDataHasValue => Some(DataHasValue(DataRole(dhv.getProperty.asOWLDataProperty.getIRI.toString), dhv.getFiller))

pub fn convert_expression<A: ForIRI>(expression: &hm::ClassExpression<A>) -> Option<Rc<wm::Concept>> {
    match expression {
        hm::ClassExpression::Class(hm::Class(iri)) => {
            let id = iri.to_string();
            Some(Rc::new(wm::Concept::AtomicConcept(Rc::new(wm::AtomicConcept { id }))))
        }
        hm::ClassExpression::ObjectSomeValuesFrom { ope: hm::ObjectPropertyExpression::ObjectProperty(hm::ObjectProperty(prop)), bce: cls } => {
            let concept = convert_expression(cls);
            concept.map(|c| {
                let role = wm::Role { id: prop.to_string() };
                Rc::new(wm::Concept::ExistentialRestriction(Rc::new(wm::ExistentialRestriction { role: Rc::new(role), concept: c })))
            })
        }
        hm::ClassExpression::ObjectIntersectionOf(expressions) => {
            let mut expressions = expressions.clone();
            expressions.sort_by(|a, b| b.cmp(a));
            let converted_opt: Option<Vec<Rc<wm::Concept>>> = expressions.iter().map(|cls| convert_expression(cls)).collect();
            converted_opt.map(|converted| expand_conjunction(converted)).flatten()
        }
        // ClassExpression::ObjectUnionOf(_) => Default::default(),
        hm::ClassExpression::ObjectComplementOf(cls) => convert_expression(cls).map(|concept| Rc::new(wm::Concept::Complement(Rc::new(wm::Complement { concept })))),
        // ClassExpression::ObjectOneOf(_) => Default::default(),
        // ClassExpression::ObjectAllValuesFrom { .. } => Default::default(),
        // ClassExpression::ObjectHasValue { .. } => Default::default(),
        // ClassExpression::ObjectHasSelf(_) => Default::default(),
        // ClassExpression::ObjectMinCardinality { .. } => Default::default(),
        // ClassExpression::ObjectMaxCardinality { .. } => Default::default(),
        // ClassExpression::ObjectExactCardinality { .. } => Default::default(),
        // ClassExpression::DataSomeValuesFrom { .. } => Default::default(),
        // ClassExpression::DataAllValuesFrom { .. } => Default::default(),
        // ClassExpression::DataHasValue { .. } => Default::default(),
        // ClassExpression::DataMinCardinality { .. } => Default::default(),
        // ClassExpression::DataMaxCardinality { .. } => Default::default(),
        // ClassExpression::DataExactCardinality { .. } => Default::default(),
        _ => Default::default(), //FIXME return placeholder identity class expression
    }
}

fn expand_conjunction(mut operands: Vec<Rc<wm::Concept>>) -> Option<Rc<wm::Concept>> {
    match operands.len() {
        0 => None,
        1 => operands.pop(),
        2 => operands.pop().map(|left| operands.pop().map(|right| Rc::new(wm::Concept::Conjunction(Rc::new(wm::Conjunction { left, right }))))).flatten(),
        _ => operands.pop().map(|left| expand_conjunction(operands).map(|right| Rc::new(wm::Concept::Conjunction(Rc::new(wm::Conjunction { left, right }))))).flatten(),
    }
}
