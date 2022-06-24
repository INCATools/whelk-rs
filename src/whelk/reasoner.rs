use std::ops::Deref;
use std::rc::Rc;

use im::{HashMap, hashmap, HashSet, hashset, Vector};

use crate::whelk::model::{AtomicConcept, Axiom, Complement, Concept, ConceptInclusion, Conjunction, Disjunction, Entity, ExistentialRestriction, HasSignature, QueueExpression, Role, RoleComposition, RoleInclusion, SelfRestriction};

pub struct ReasonerState {
    hier: HashMap<Rc<Role>, HashSet<Rc<Role>>>,
    hier_comps: HashMap<Rc<Role>, HashMap<Rc<Role>, Vector<Rc<Role>>>>,
    inits: HashSet<Rc<Concept>>,
    asserted_concept_inclusions_by_subclass: HashMap<Rc<Concept>, Vector<Rc<ConceptInclusion>>>,
    closure_subs_by_superclass: HashMap<Rc<Concept>, HashSet<Rc<Concept>>>,
    closure_subs_by_subclass: HashMap<Rc<Concept>, HashSet<Rc<Concept>>>,
    asserted_negative_conjunctions: HashSet<Rc<Conjunction>>,
    asserted_negative_conjunctions_by_right_operand: HashMap<Rc<Concept>, HashMap<Rc<Concept>, Rc<Conjunction>>>,
    asserted_negative_conjunctions_by_left_operand: HashMap<Rc<Concept>, HashMap<Rc<Concept>, Rc<Conjunction>>>,
    asserted_unions: HashSet<Rc<Disjunction>>,
    unions_by_operand: HashMap<Rc<Concept>, Vector<Rc<Disjunction>>>,
    links_by_subject: HashMap<Rc<Concept>, HashMap<Rc<Role>, HashSet<Rc<Concept>>>>,
    links_by_target: HashMap<Rc<Concept>, HashMap<Rc<Role>, Vector<Rc<Concept>>>>,
    negative_existential_restrictions_by_concept: HashMap<Rc<Concept>, HashSet<Rc<ExistentialRestriction>>>,
    propagations: HashMap<Rc<Concept>, HashMap<Rc<Role>, Vector<Rc<ExistentialRestriction>>>>,
    asserted_negative_self_restrictions_by_role: HashMap<Rc<Role>, Rc<SelfRestriction>>,
}

impl ReasonerState {
    fn empty() -> ReasonerState {
        ReasonerState {
            hier: Default::default(),
            hier_comps: Default::default(),
            inits: Default::default(),
            asserted_concept_inclusions_by_subclass: Default::default(),
            closure_subs_by_superclass: hashmap! {Rc::new(Concept::bottom()) => HashSet::new()},
            closure_subs_by_subclass: hashmap! {Rc::new(Concept::top()) => HashSet::new()},
            asserted_negative_conjunctions: Default::default(),
            asserted_negative_conjunctions_by_right_operand: Default::default(),
            asserted_negative_conjunctions_by_left_operand: Default::default(),
            asserted_unions: Default::default(),
            unions_by_operand: Default::default(),
            links_by_subject: Default::default(),
            links_by_target: Default::default(),
            negative_existential_restrictions_by_concept: Default::default(),
            propagations: Default::default(),
            asserted_negative_self_restrictions_by_role: Default::default(),
        }
    }
}

pub fn assert(axioms: &HashSet<Rc<Axiom>>) -> Rc<ReasonerState> {
    let all_roles: HashSet<Rc<Role>> = axioms.iter()
        .flat_map(|ax| ax.signature())
        .filter_map(|entity| match entity.deref() {
            Entity::Role(role) => Some(Rc::clone(role)),
            _ => None
        }).collect();
    let all_role_inclusions = axioms.iter()
        .filter_map(|ax| match ax.deref() {
            Axiom::RoleInclusion(ri) => Some(Rc::clone(&ri)),
            _ => None,
        }).collect();
    let hier = saturate_roles(all_role_inclusions, &all_roles);
    let chains = axioms.iter()
        .filter_map(|ax| match ax.deref() {
            Axiom::RoleComposition(rc) => Some(Rc::clone(&rc)),
            _ => None,
        }).collect();
    let hier_comps = index_role_compositions(&hier, &chains);
    let concept_inclusions = axioms.iter()
        .filter_map(|ax| match ax.deref() {
            Axiom::ConceptInclusion(ci) => Some(Rc::clone(&ci)),
            _ => None,
        }).collect();
    let empty = ReasonerState::empty();
    let initial_state = Rc::new(ReasonerState {
        hier,
        hier_comps,
        ..empty
    });
    assert_append(&concept_inclusions, &initial_state)
}

pub fn assert_append(axioms: &HashSet<Rc<ConceptInclusion>>, state: &Rc<ReasonerState>) -> Rc<ReasonerState> {
    let distinct_concepts: HashSet<Rc<Concept>> = axioms.iter()
        .flat_map(|ci| ci.subclass.concept_signature().union(ci.superclass.concept_signature()))
        .collect();
    let atomic_concepts: HashSet<Rc<AtomicConcept>> = distinct_concepts.iter()
        .filter_map(|c| match c.deref() {
            Concept::AtomicConcept(ac) => Some(Rc::clone(&ac)),
            _ => None,
        }).collect();
    let additional_axioms: HashSet<Rc<ConceptInclusion>> = distinct_concepts.iter()
        .flat_map(|c| match c.deref() {
            Concept::Disjunction(disjunction) => rule_union(disjunction),
            Concept::Complement(complement) => rule_complement(complement),
            _ => HashSet::new(),
        }).collect();
    //TODO negative_self_restrictions
    let mut assertions_queue: Vec<Rc<ConceptInclusion>> = vec![];
    let mut todo: Vec<QueueExpression> = vec![];
    for ax in axioms {
        assertions_queue.push(Rc::clone(ax));
        todo.push(QueueExpression::ConceptInclusion(Rc::clone(ax)));
    }
    for ax in additional_axioms {
        assertions_queue.push(Rc::clone(&ax));
        todo.push(QueueExpression::ConceptInclusion(Rc::clone(&ax)));
    }
    for ac in atomic_concepts {
        todo.push(QueueExpression::Concept(Rc::new(Concept::AtomicConcept(ac))));
    }
    compute_closure(state, assertions_queue, todo)
}

fn compute_closure(state: &Rc<ReasonerState>, assertions_queue: Vec<Rc<ConceptInclusion>>, mut todo: Vec<QueueExpression>) -> Rc<ReasonerState> {
    let mut state = Rc::clone(state);
    for ci in assertions_queue {
        state = process_asserted_concept_inclusion(ci.deref(), state, &todo);
    }
    while !todo.is_empty() {
        if let Some(item) = todo.pop() {
            state = process(item, state, &todo);
        }
    }
    state
}

fn process_asserted_concept_inclusion(ci: &ConceptInclusion, state: Rc<ReasonerState>, mut todo: &Vec<QueueExpression>) -> Rc<ReasonerState> {
    !todo!();
}

fn process(item: QueueExpression, state: Rc<ReasonerState>, mut todo: &Vec<QueueExpression>) -> Rc<ReasonerState> {
    !todo!();
}

fn rule_union(disjunction: &Rc<Disjunction>) -> HashSet<Rc<ConceptInclusion>> {
    disjunction.operands.iter().map(|o|
        ConceptInclusion {
            subclass: Rc::clone(o),
            // should the Disjunction Concept be passed in to be reused instead of creating new??
            superclass: Rc::new(Concept::Disjunction(Rc::clone(disjunction))),
        }).collect()
}

fn rule_complement(complement: &Complement) -> HashSet<Rc<ConceptInclusion>> {
    HashSet::unit(Rc::new(
        ConceptInclusion {
            subclass: Rc::clone(&complement.concept),
            superclass: Rc::new(Concept::bottom()),
        }
    ))
}

fn saturate_roles(role_inclusions: HashSet<Rc<RoleInclusion>>, all_roles: &HashSet<Rc<Role>>) -> HashMap<Rc<Role>, HashSet<Rc<Role>>> {
    let reflexive_role_inclusions = all_roles.iter()
        .map(|r| RoleInclusion { subproperty: Rc::clone(r), superproperty: Rc::clone(r) })
        .collect();
    let all_role_inclusions = role_inclusions.union(reflexive_role_inclusions);
    todo!()
}

fn index_role_compositions(hier: &HashMap<Rc<Role>, HashSet<Rc<Role>>>, chains: &HashSet<Rc<RoleComposition>>)
                           -> HashMap<Rc<Role>, HashMap<Rc<Role>, Vector<Rc<Role>>>> {
    todo!()
}
