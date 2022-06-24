use std::rc::Rc;
use horned_owl::model::{Axiom as OWLAxiom, ClassExpression, EquivalentClasses};
use crate::whelk::model::{Axiom, Concept, ConceptInclusion};
use im::{HashSet, hashset};
use itertools::Itertools;

pub fn translate_axiom(axiom: &OWLAxiom) -> HashSet<Rc<Axiom>> {
    match axiom {
        OWLAxiom::DeclareClass(_) => Default::default(), //FIXME add subclassOf Thing?
        OWLAxiom::DeclareNamedIndividual(_) => Default::default(), //FIXME add subclassOf Thing?
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

fn convert_expression(expression: &ClassExpression) -> Option<Rc<Concept>> {
    match expression {
        ClassExpression::Class(_) => {}
        ClassExpression::ObjectIntersectionOf(_) => {}
        ClassExpression::ObjectUnionOf(_) => {}
        ClassExpression::ObjectComplementOf(_) => {}
        ClassExpression::ObjectOneOf(_) => {}
        ClassExpression::ObjectSomeValuesFrom { .. } => {}
        ClassExpression::ObjectAllValuesFrom { .. } => {}
        ClassExpression::ObjectHasValue { .. } => {}
        ClassExpression::ObjectHasSelf(_) => {}
        ClassExpression::ObjectMinCardinality { .. } => {}
        ClassExpression::ObjectMaxCardinality { .. } => {}
        ClassExpression::ObjectExactCardinality { .. } => {}
        ClassExpression::DataSomeValuesFrom { .. } => {}
        ClassExpression::DataAllValuesFrom { .. } => {}
        ClassExpression::DataHasValue { .. } => {}
        ClassExpression::DataMinCardinality { .. } => {}
        ClassExpression::DataMaxCardinality { .. } => {}
        ClassExpression::DataExactCardinality { .. } => {}
    }
    todo!();
}