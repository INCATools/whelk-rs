use std::rc::Rc;

use horned_owl::model::{Axiom as OWLAxiom, Class, ClassExpression, DeclareClass, EquivalentClasses, ObjectProperty, ObjectPropertyExpression};
use horned_owl::model::AnnotationSubject::IRI;
use horned_owl::ontology::set::SetOntology;
use im::{HashSet, hashset};
use itertools::Itertools;

use crate::whelk::model::{AtomicConcept, Axiom, BOTTOM, Concept, ConceptInclusion, Conjunction, ExistentialRestriction, Role, TOP};

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
        // OWLAxiom::SubObjectPropertyOf(_) => {}
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
        // OWLAxiom::TransitiveObjectProperty(_) => {}
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
//       case ObjectComplementOf(concept)                                => convertExpression(concept).map(Complement)
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
            let converted: Vec<Rc<Concept>> = expressions.iter()
                .filter_map(|cls| convert_expression(cls)).collect();
            expand_conjunction(converted)
        }
        // ClassExpression::ObjectUnionOf(_) => Default::default(),
        // ClassExpression::ObjectComplementOf(_) => Default::default(),
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
