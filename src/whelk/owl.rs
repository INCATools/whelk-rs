use std::rc::Rc;

use horned_owl::model::{Axiom as OWLAxiom, Build, Class, ClassExpression, DeclareClass, EquivalentClasses, ObjectProperty, ObjectPropertyExpression, SubObjectPropertyExpression, SubObjectPropertyOf, TransitiveObjectProperty};
use horned_owl::ontology::set::SetOntology;
use im::{HashSet, hashset};
use itertools::Itertools;

use crate::whelk::model::{AtomicConcept, Axiom, BOTTOM, Complement, Concept, ConceptInclusion, Conjunction, ExistentialRestriction, Role, RoleComposition, RoleInclusion, TOP};

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
            let superclass = Rc::clone(&globals.thing);
            HashSet::unit(Rc::new(Axiom::ConceptInclusion(Rc::new(ConceptInclusion { subclass, superclass }))))
        }
        OWLAxiom::DeclareNamedIndividual(_) => Default::default(), //FIXME add nominal subclassOf Thing
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
                            let first_second = concept_inclusion(first, second);
                            let second_first = concept_inclusion(second, first);
                            hashset![first_second, second_first]
                        }
                        _ => Default::default(),
                    }
                }
                ).collect()
        }
        // OWLAxiom::DisjointClasses(_) => {}
        // OWLAxiom::DisjointUnion(_) => {}
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
                        translate_axiom(&axiom)
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
                                    let beginning_chain = translate_axiom(&OWLAxiom::SubObjectPropertyOf(SubObjectPropertyOf {
                                        sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![
                                            ObjectPropertyExpression::ObjectProperty(ObjectProperty(first_id.clone())),
                                            ObjectPropertyExpression::ObjectProperty(ObjectProperty(second_id.clone())),
                                        ]),
                                        sup: composition_property.clone(),
                                    }));
                                    let mut new_chain = props.clone();
                                    new_chain.remove(0);
                                    new_chain.remove(0);
                                    new_chain.insert(0, composition_property);
                                    let rest_of_chain = translate_axiom(&OWLAxiom::SubObjectPropertyOf(SubObjectPropertyOf {
                                        sub: SubObjectPropertyExpression::ObjectPropertyChain(new_chain),
                                        sup: ObjectPropertyExpression::ObjectProperty(ObjectProperty(sup.clone())),
                                    }));
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
        // OWLAxiom::EquivalentObjectProperties(_) => {}
        // OWLAxiom::DisjointObjectProperties(_) => {}
        // OWLAxiom::InverseObjectProperties(_) => {}
        // OWLAxiom::ObjectPropertyDomain(_) => {}
        // OWLAxiom::ObjectPropertyRange(_) => {}
        // OWLAxiom::FunctionalObjectProperty(_) => {}
        // OWLAxiom::InverseFunctionalObjectProperty(_) => {}
        // OWLAxiom::ReflexiveObjectProperty(_) => {}
        // OWLAxiom::IrreflexiveObjectProperty(_) => {}
        // OWLAxiom::SymmetricObjectProperty(_) => {}
        // OWLAxiom::AsymmetricObjectProperty(_) => {}
        OWLAxiom::TransitiveObjectProperty(TransitiveObjectProperty(prop)) => {
            translate_axiom(&OWLAxiom::SubObjectPropertyOf(SubObjectPropertyOf {
                sub: SubObjectPropertyExpression::ObjectPropertyChain(vec![prop.clone(), prop.clone()]),
                sup: prop.clone(),
            }))
        }
        // OWLAxiom::SubDataPropertyOf(_) => {}
        // OWLAxiom::EquivalentDataProperties(_) => {}
        // OWLAxiom::DisjointDataProperties(_) => {}
        // OWLAxiom::DataPropertyDomain(_) => {}
        // OWLAxiom::DataPropertyRange(_) => {}
        // OWLAxiom::FunctionalDataProperty(_) => {}
        // OWLAxiom::DatatypeDefinition(_) => {}
        // OWLAxiom::HasKey(_) => {}
        // OWLAxiom::SameIndividual(_) => {}
        // OWLAxiom::DifferentIndividuals(_) => {}
        // OWLAxiom::ClassAssertion(_) => {}
        // OWLAxiom::ObjectPropertyAssertion(_) => {}
        // OWLAxiom::NegativeObjectPropertyAssertion(_) => {}
        // OWLAxiom::DataPropertyAssertion(_) => {}
        // OWLAxiom::NegativeDataPropertyAssertion(_) => {}
        // OWLAxiom::AnnotationAssertion(_) => {}
        // OWLAxiom::SubAnnotationPropertyOf(_) => {}
        // OWLAxiom::AnnotationPropertyDomain(_) => {}
        // OWLAxiom::AnnotationPropertyRange(_) => {}
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
        0 => Default::default(),
        1 => Some(operands.pop().unwrap()),
        2 => {
            let left = operands.pop().unwrap();
            let right = operands.pop().unwrap();
            Some(Rc::new(Concept::Conjunction(Rc::new(Conjunction { left, right }))))
        }
        _ => {
            let left = operands.pop().unwrap();
            let right = expand_conjunction(operands).unwrap();
            Some(Rc::new(Concept::Conjunction(Rc::new(Conjunction { left, right }))))
        }
    }
}
