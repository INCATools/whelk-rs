use std::rc::Rc;

use horned_owl::model::{Axiom as OWLAxiom, Build, Class, ClassAssertion, ClassExpression, DeclareClass, DeclareNamedIndividual, DisjointClasses, DisjointUnion, EquivalentClasses, EquivalentObjectProperties, NamedIndividual, ObjectProperty, ObjectPropertyDomain, ObjectPropertyExpression, SubObjectPropertyExpression, SubObjectPropertyOf, TransitiveObjectProperty, Individual as OWLIndividual, ObjectPropertyAssertion};
use horned_owl::model::ClassExpression::ObjectUnionOf;
use horned_owl::ontology::set::SetOntology;
use im::{HashSet, hashset};
use itertools::Itertools;

use crate::whelk::model::{AtomicConcept, Axiom, BOTTOM, Complement, Concept, ConceptInclusion, Conjunction, ExistentialRestriction, Individual, Nominal, Role, RoleComposition, RoleInclusion, TOP};

struct OWLGlobals {
    thing: Rc<Concept>,
    nothing: Rc<Concept>,
}

pub fn translate_ontology(ontology: &SetOntology) -> HashSet<Rc<Axiom>> {
    let globals = make_globals();
    ontology.iter()
        .flat_map(|ann_axiom| translate_axiom_internal(&ann_axiom.axiom, &globals))
        .collect()
}

fn make_globals() -> OWLGlobals {
    OWLGlobals {
        thing: Rc::new(Concept::AtomicConcept(Rc::new(AtomicConcept { id: TOP.to_string() }))),
        nothing: Rc::new(Concept::AtomicConcept(Rc::new(AtomicConcept { id: BOTTOM.to_string() }))),
    }
}

pub fn translate_axiom(axiom: &OWLAxiom) -> HashSet<Rc<Axiom>> {
    translate_axiom_internal(axiom, &make_globals())
}

fn translate_axiom_internal(axiom: &OWLAxiom, globals: &OWLGlobals) -> HashSet<Rc<Axiom>> {
    match axiom {
        OWLAxiom::DeclareClass(DeclareClass(Class(iri))) => {
            let subclass = Rc::new(Concept::AtomicConcept(Rc::new(AtomicConcept { id: iri.to_string() })));
            HashSet::unit(concept_inclusion(&subclass, &globals.thing))
        }
        OWLAxiom::DeclareNamedIndividual(DeclareNamedIndividual(NamedIndividual(iri))) => {
            let individual = Rc::new(Individual { id: iri.to_string() });
            let subclass = Rc::new(Concept::Nominal(Rc::new(Nominal { individual })));
            HashSet::unit(concept_inclusion(&subclass, &globals.thing))
        }
        OWLAxiom::SubClassOf(ax) =>
            match (convert_expression(&ax.sub), convert_expression(&ax.sup)) {
                (Some(subclass), Some(superclass)) =>
                    HashSet::unit(concept_inclusion(&subclass, &superclass)),
                _ => Default::default(),
            },
        OWLAxiom::EquivalentClasses(EquivalentClasses(expressions)) => {
            expressions.iter()
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
                }
                ).collect()
        }
        OWLAxiom::DisjointClasses(DisjointClasses(operands)) => {
            operands.iter()
                .map(|c| convert_expression(c))
                .filter_map(|opt| opt)
                .combinations(2)
                .flat_map(|pair| {
                    let first_opt = pair.get(0);
                    let second_opt = pair.get(1);
                    match (first_opt, second_opt) {
                        (Some(first), Some(second)) => {
                            let conjunction = Rc::new(Concept::Conjunction(Rc::new(
                                Conjunction {
                                    left: Rc::clone(first),
                                    right: Rc::clone(second),
                                })));
                            HashSet::unit(concept_inclusion(&conjunction, &globals.nothing))
                        }
                        _ => Default::default(),
                    }
                }).collect()
        }
        OWLAxiom::DisjointUnion(DisjointUnion(cls, expressions)) => {
            let union = ObjectUnionOf(expressions.clone());
            let equivalence = OWLAxiom::EquivalentClasses(EquivalentClasses(vec![ClassExpression::Class(cls.clone()), union]));
            let disjointness = OWLAxiom::DisjointClasses(DisjointClasses(expressions.clone()));
            translate_axiom_internal(&equivalence, globals).union(translate_axiom_internal(&disjointness, globals))
        }
        OWLAxiom::SubObjectPropertyOf(SubObjectPropertyOf {
                                          sub: SubObjectPropertyExpression::ObjectPropertyExpression(ObjectPropertyExpression::ObjectProperty(ObjectProperty(sub))),
                                          sup: ObjectPropertyExpression::ObjectProperty(ObjectProperty(sup))
                                      }) => {
            let sub_role = Rc::new(Role { id: sub.to_string() });
            let sup_role = Rc::new(Role { id: sup.to_string() });
            HashSet::unit(Rc::new(Axiom::RoleInclusion(Rc::new(
                RoleInclusion {
                    subproperty: sub_role,
                    superproperty: sup_role,
                }))))
        }
        OWLAxiom::SubObjectPropertyOf(SubObjectPropertyOf {
                                          sub: SubObjectPropertyExpression::ObjectPropertyChain(props),
                                          sup: ObjectPropertyExpression::ObjectProperty(ObjectProperty(sup))
                                      }) => {
            if props.iter().all(|p| match p {
                ObjectPropertyExpression::ObjectProperty(_) => true,
                ObjectPropertyExpression::InverseObjectProperty(_) => false,
            }) {
                let props_len = props.len();
                match props_len {
                    0 => Default::default(),
                    1 => {
                        let sub = props.get(0).unwrap().clone();
                        let axiom = OWLAxiom::SubObjectPropertyOf(SubObjectPropertyOf {
                            sub: SubObjectPropertyExpression::ObjectPropertyExpression(sub),
                            sup: ObjectPropertyExpression::ObjectProperty(ObjectProperty(sup.clone())),
                        });
                        translate_axiom_internal(&axiom, globals)
                    }
                    _ => {
                        match (props.get(0), props.get(1)) {
                            (Some(ObjectPropertyExpression::ObjectProperty(ObjectProperty(first_id))),
                                Some(ObjectPropertyExpression::ObjectProperty(ObjectProperty(second_id)))) => {
                                if props_len < 3 {
                                    HashSet::unit(Rc::new(Axiom::RoleComposition(Rc::new(
                                        RoleComposition {
                                            first: Rc::new(Role { id: first_id.to_string() }),
                                            second: Rc::new(Role { id: second_id.to_string() }),
                                            superproperty: Rc::new(Role { id: sup.to_string() }),
                                        }
                                    ))))
                                } else {
                                    let composition_property_id = format!("{}{}:{}", Role::composition_role_prefix(), first_id, second_id);
                                    let comp_iri = Build::new().iri(composition_property_id);
                                    let composition_property = ObjectPropertyExpression::ObjectProperty(ObjectProperty(comp_iri));
                                    let beginning_chain = translate_axiom_internal(&OWLAxiom::SubObjectPropertyOf(SubObjectPropertyOf {
                                        sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![
                                            ObjectPropertyExpression::ObjectProperty(ObjectProperty(first_id.clone())),
                                            ObjectPropertyExpression::ObjectProperty(ObjectProperty(second_id.clone())),
                                        ]),
                                        sup: composition_property.clone(),
                                    }), globals);
                                    let mut new_chain = props.clone();
                                    new_chain.remove(0);
                                    new_chain.remove(0);
                                    new_chain.insert(0, composition_property);
                                    let rest_of_chain = translate_axiom_internal(&OWLAxiom::SubObjectPropertyOf(SubObjectPropertyOf {
                                        sub: SubObjectPropertyExpression::ObjectPropertyChain(new_chain),
                                        sup: ObjectPropertyExpression::ObjectProperty(ObjectProperty(sup.clone())),
                                    }), globals);
                                    beginning_chain.union(rest_of_chain)
                                }
                            }
                            _ => Default::default(),
                        }
                    }
                }
            } else {
                Default::default()
            }
        }
        OWLAxiom::EquivalentObjectProperties(EquivalentObjectProperties(props)) => {
            props.iter()
                .combinations(2)
                .flat_map(|pair| {
                    let first_opt = pair.get(0);
                    let second_opt = pair.get(1);
                    match (first_opt, second_opt) {
                        (Some(first), Some(second)) => {
                            let first_second = OWLAxiom::SubObjectPropertyOf(SubObjectPropertyOf {
                                sub: SubObjectPropertyExpression::ObjectPropertyExpression(first.clone().clone()),
                                sup: second.clone().clone(),
                            });
                            let second_first = OWLAxiom::SubObjectPropertyOf(SubObjectPropertyOf {
                                sub: SubObjectPropertyExpression::ObjectPropertyExpression(second.clone().clone()),
                                sup: first.clone().clone(),
                            });
                            translate_axiom_internal(&first_second, globals).union(translate_axiom_internal(&second_first, globals))
                        }
                        _ => Default::default(),
                    }
                }).collect()
        }
        OWLAxiom::ObjectPropertyDomain(ObjectPropertyDomain { ope: ObjectPropertyExpression::ObjectProperty(ObjectProperty(prop)), ce: cls }) => {
            convert_expression(cls).iter().map(|c| {
                let restriction = Rc::new(Concept::ExistentialRestriction(Rc::new(
                    ExistentialRestriction {
                        role: Rc::new(Role { id: prop.to_string() }),
                        concept: Rc::clone(&globals.thing),
                    })));
                concept_inclusion(&restriction, &c)
            }).collect()
        }
        // OWLAxiom::ObjectPropertyRange(_) => {} //TODO
        // OWLAxiom::DisjointObjectProperties(_) => {}
        // OWLAxiom::InverseObjectProperties(_) => {}
        // OWLAxiom::FunctionalObjectProperty(_) => {}
        // OWLAxiom::InverseFunctionalObjectProperty(_) => {}
        // OWLAxiom::ReflexiveObjectProperty(_) => {}
        // OWLAxiom::IrreflexiveObjectProperty(_) => {}
        // OWLAxiom::SymmetricObjectProperty(_) => {}
        // OWLAxiom::AsymmetricObjectProperty(_) => {}
        OWLAxiom::TransitiveObjectProperty(TransitiveObjectProperty(prop)) => {
            translate_axiom_internal(&OWLAxiom::SubObjectPropertyOf(SubObjectPropertyOf {
                sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![prop.clone(), prop.clone()]),
                sup: prop.clone(),
            }), globals)
        }
        // OWLAxiom::SameIndividual(_) => {} //TODO
        // OWLAxiom::DifferentIndividuals(_) => {} //TODO
        OWLAxiom::ClassAssertion(ClassAssertion { ce: cls, i: OWLIndividual::Named(NamedIndividual(ind)) }) => {
            convert_expression(cls).iter().flat_map(|superclass| {
                let individual = Rc::new(Individual { id: ind.to_string() });
                let subclass = Rc::new(Concept::Nominal(Rc::new(Nominal { individual })));
                HashSet::unit(concept_inclusion(&subclass, superclass))
            }).collect()
        }
        OWLAxiom::ObjectPropertyAssertion(ObjectPropertyAssertion {
                                              ope: property_expression,
                                              from: OWLIndividual::Named(NamedIndividual(axiom_subject)),
                                              to: OWLIndividual::Named(NamedIndividual(axiom_target))
                                          }) => {
            let (subject, prop, target) = match property_expression {
                ObjectPropertyExpression::ObjectProperty(ObjectProperty(prop)) => (axiom_subject, prop, axiom_target),
                ObjectPropertyExpression::InverseObjectProperty(ObjectProperty(prop)) => (axiom_target, prop, axiom_subject),
            };
            let subclass = Rc::new(Concept::Nominal(Rc::new(Nominal { individual: Rc::new(Individual { id: subject.to_string() }) })));
            let target_nominal = Rc::new(Concept::Nominal(Rc::new(Nominal { individual: Rc::new(Individual { id: target.to_string() }) })));
            let superclass = Rc::new(Concept::ExistentialRestriction(Rc::new(ExistentialRestriction { role: Rc::new(Role { id: prop.to_string() }), concept: target_nominal })));
            HashSet::unit(concept_inclusion(&subclass, &superclass))
        }
        // OWLAxiom::NegativeObjectPropertyAssertion(_) => {} //TODO
        // OWLAxiom::SubDataPropertyOf(_) => {}
        // OWLAxiom::EquivalentDataProperties(_) => {}
        // OWLAxiom::DisjointDataProperties(_) => {}
        // OWLAxiom::DataPropertyDomain(_) => {}
        // OWLAxiom::DataPropertyRange(_) => {}
        // OWLAxiom::FunctionalDataProperty(_) => {}
        // OWLAxiom::DatatypeDefinition(_) => {}
        // OWLAxiom::HasKey(_) => {}
        // OWLAxiom::DataPropertyAssertion(_) => {}
        // OWLAxiom::NegativeDataPropertyAssertion(_) => {}
        _ => Default::default(),
    }
}

fn concept_inclusion(subclass: &Rc<Concept>, superclass: &Rc<Concept>) -> Rc<Axiom> {
    Rc::new(Axiom::ConceptInclusion(
        Rc::new(ConceptInclusion {
            subclass: Rc::clone(subclass),
            superclass: Rc::clone(superclass),
        })))
}

//       case ObjectHasSelf(ObjectProperty(prop))                        => Some(SelfRestriction(Role(prop.toString)))
//       case ObjectUnionOf(operands)                                    =>
//         operands.toList.map(convertExpression).sequence.map(_.toSet).map(Disjunction)
//       case ObjectOneOf(individuals) if individuals.size == 1          => individuals.collectFirst { case NamedIndividual(iri) => Nominal(WIndividual(iri.toString)) }
//       case ObjectHasValue(ObjectProperty(prop), NamedIndividual(ind)) => Some(ExistentialRestriction(Role(prop.toString), Nominal(WIndividual(ind.toString))))
//       case DataSomeValuesFrom(DataProperty(prop), range)              => Some(DataRestriction(DataRole(prop.toString), DataRange(range)))
//       //scowl is missing DataHasValue
//       case dhv: OWLDataHasValue => Some(DataHasValue(DataRole(dhv.getProperty.asOWLDataProperty.getIRI.toString), dhv.getFiller))

fn convert_expression(expression: &ClassExpression) -> Option<Rc<Concept>> {
    match expression {
        ClassExpression::Class(Class(iri)) => {
            let id = iri.to_string();
            Some(Rc::new(Concept::AtomicConcept(Rc::new(AtomicConcept { id }))))
        }
        ClassExpression::ObjectSomeValuesFrom {
            ope: ObjectPropertyExpression::ObjectProperty(ObjectProperty(prop)),
            bce: cls
        } => {
            let concept = convert_expression(cls);
            concept.map(|c| {
                let role = Role { id: prop.to_string() };
                Rc::new(
                    Concept::ExistentialRestriction(
                        Rc::new(
                            ExistentialRestriction { role: Rc::new(role), concept: c }
                        )
                    )
                )
            })
        }
        ClassExpression::ObjectIntersectionOf(expressions) => {
            let mut expressions = expressions.clone();
            expressions.sort_by(|a, b| b.cmp(a));
            let converted_opt: Option<Vec<Rc<Concept>>> = expressions.iter()
                .map(|cls| convert_expression(cls))
                .collect();
            converted_opt.map(|converted| expand_conjunction(converted)).flatten()
        }
        // ClassExpression::ObjectUnionOf(_) => Default::default(),
        ClassExpression::ObjectComplementOf(cls) => {
            convert_expression(cls).map(|concept| {
                Rc::new(Concept::Complement(Rc::new(Complement { concept })))
            })
        }
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

fn expand_conjunction(mut operands: Vec<Rc<Concept>>) -> Option<Rc<Concept>> {
    match operands.len() {
        0 => None,
        1 => operands.pop(),
        2 => operands.pop().map(|left| {
            operands.pop().map(|right| {
                Rc::new(Concept::Conjunction(Rc::new(Conjunction { left, right })))
            })
        }).flatten(),
        _ => operands.pop().map(|left| {
            expand_conjunction(operands).map(|right| {
                Rc::new(Concept::Conjunction(Rc::new(Conjunction { left, right })))
            })
        }).flatten()
    }
}
