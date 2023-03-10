use std::ops::Deref;
use std::rc::Rc;

use im::{hashmap, hashset, vector, HashMap, HashSet, Vector};
use itertools::Itertools;

use crate::whelk::model::{
    AtomicConcept, Axiom, Complement, Concept, ConceptInclusion, Conjunction, Disjunction, Entity, ExistentialRestriction, HasSignature, QueueExpression, Role, RoleComposition,
    RoleInclusion, SelfRestriction, BOTTOM, TOP,
};

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub struct ReasonerState {
    hier: HashMap<Role, HashSet<Role>>,
    hier_comps: HashMap<Role, HashMap<Role, Vector<Role>>>,
    inits: HashSet<Concept>,
    asserted_concept_inclusions_by_subclass: HashMap<Concept, Vector<ConceptInclusion>>,
    closure_subs_by_superclass: HashMap<Concept, HashSet<Concept>>,
    closure_subs_by_subclass: HashMap<Concept, HashSet<Concept>>,
    asserted_negative_conjunctions: HashSet<Conjunction>,
    asserted_negative_conjunctions_by_right_operand: HashMap<Concept, HashMap<Concept, Conjunction>>,
    asserted_negative_conjunctions_by_left_operand: HashMap<Concept, HashMap<Concept, Conjunction>>,
    asserted_unions: HashSet<Disjunction>,
    unions_by_operand: HashMap<Concept, Vector<Disjunction>>,
    links_by_subject: HashMap<Concept, HashMap<Role, HashSet<Concept>>>,
    links_by_target: HashMap<Concept, HashMap<Role, Vector<Concept>>>,
    negative_existential_restrictions_by_concept: HashMap<Concept, HashSet<ExistentialRestriction>>,
    propagations: HashMap<Concept, HashMap<Role, Vector<ExistentialRestriction>>>,
    asserted_negative_self_restrictions_by_role: HashMap<Role, SelfRestriction>,
    top: Concept,
    bottom: Concept,
}

impl ReasonerState {
    fn empty() -> ReasonerState {
        ReasonerState {
            hier: Default::default(),
            hier_comps: Default::default(),
            inits: Default::default(),
            asserted_concept_inclusions_by_subclass: Default::default(),
            closure_subs_by_superclass: hashmap! {Concept::bottom() => HashSet::new()},
            closure_subs_by_subclass: hashmap! {Concept::top() => HashSet::new()},
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
            top: Concept::AtomicConcept(Rc::new(AtomicConcept { id: TOP.to_string() })),
            bottom: Concept::AtomicConcept(Rc::new(AtomicConcept { id: BOTTOM.to_string() })),
        }
    }

    pub fn named_subsumptions(&self) -> Vector<(AtomicConcept, AtomicConcept)> {
        self.closure_subs_by_subclass
            .iter()
            .filter_map(|(sub, supers)| match sub {
                Concept::AtomicConcept(ac) => Some((ac.deref().clone(), supers)),
                _ => None,
            })
            .flat_map(|(sub, supers)| {
                supers.iter().filter_map(move |sup| match sup {
                    Concept::AtomicConcept(ac) => Some((sub.clone(), ac.deref().clone())),
                    _ => None,
                })
            })
            .collect()
    }
}

pub fn assert(axioms: &HashSet<Axiom>) -> ReasonerState {
    let all_roles: HashSet<Role> = axioms
        .iter()
        .flat_map(|ax| ax.signature())
        .filter_map(|entity| match entity.deref() {
            Entity::Role(role) => Some(role.deref().clone()),
            _ => None,
        })
        .collect();
    let all_role_inclusions = axioms
        .iter()
        .filter_map(|ax| match ax {
            Axiom::RoleInclusion(ri) => Some(ri.deref().clone()),
            _ => None,
        })
        .collect();
    let hier = saturate_roles(all_role_inclusions, &all_roles);
    let chains = axioms
        .iter()
        .filter_map(|ax| match ax {
            Axiom::RoleComposition(rc) => Some(rc.deref().clone()),
            _ => None,
        })
        .collect();
    let hier_comps = index_role_compositions(&hier, &chains);
    let concept_inclusions = axioms
        .iter()
        .filter_map(|ax| match ax.deref() {
            Axiom::ConceptInclusion(ci) => Some(ci.deref().clone()),
            _ => None,
        })
        .collect();
    let empty = ReasonerState::empty();
    let initial_state = ReasonerState { hier, hier_comps, ..empty };
    assert_append(&concept_inclusions, &initial_state)
}

pub fn assert_append(axioms: &HashSet<ConceptInclusion>, state: &ReasonerState) -> ReasonerState {
    let distinct_concepts: HashSet<Concept> = axioms.iter().flat_map(|ci| ci.subclass.concept_signature().union(ci.superclass.concept_signature())).collect();
    let atomic_concepts: HashSet<AtomicConcept> = distinct_concepts
        .iter()
        .filter_map(|c| match c {
            Concept::AtomicConcept(ac) => Some(ac.deref().clone()),
            _ => None,
        })
        .collect();
    let additional_axioms: HashSet<ConceptInclusion> = distinct_concepts
        .iter()
        .flat_map(|c| match c {
            Concept::Disjunction(disjunction) => rule_union(disjunction),
            Concept::Complement(complement) => rule_complement(complement),
            _ => HashSet::new(),
        })
        .collect();
    //TODO negative_self_restrictions
    let mut assertions_queue: Vec<ConceptInclusion> = vec![];
    let mut todo: Vec<QueueExpression> = vec![];
    for ax in axioms {
        assertions_queue.push(ax.clone());
        todo.push(QueueExpression::ConceptInclusion(ax.clone()));
    }
    for ax in additional_axioms {
        assertions_queue.push(ax.clone());
        todo.push(QueueExpression::ConceptInclusion(ax.clone()));
    }
    for ac in atomic_concepts {
        todo.push(QueueExpression::Concept(Concept::AtomicConcept(Rc::new(ac))));
    }
    let mut new_state = state.clone();
    compute_closure(&mut new_state, assertions_queue, todo);
    new_state
}

fn compute_closure(state: &mut ReasonerState, assertions_queue: Vec<ConceptInclusion>, mut todo: Vec<QueueExpression>) {
    for ci in assertions_queue {
        process_asserted_concept_inclusion(&ci, state, &mut todo);
    }
    while !todo.is_empty() {
        if let Some(item) = todo.pop() {
            process(item, state, &mut todo);
        }
    }
}

fn process_asserted_concept_inclusion(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    match state.asserted_concept_inclusions_by_subclass.get_mut(&ci.subclass) {
        None => {
            state.asserted_concept_inclusions_by_subclass.insert(ci.subclass.deref().clone(), vector![ci.clone()]);
        }
        Some(vec) => {
            vec.push_back(ci.clone());
        }
    }
    rule_subclass_left(ci, state, todo);
    rule_plus_and_a(ci, state, todo);
    rule_plus_some_a(ci, state, todo);
    //rule_or_a_left()
}

fn process(item: QueueExpression, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    match item {
        QueueExpression::Link { subject, role, target } => process_link(&subject, &role, &target, state, todo),
        QueueExpression::ConceptInclusion(ci) => {
            let seen = process_concept_inclusion(&ci, state, todo);
            if !seen {
                process_concept_inclusion_minus(&ci, state, todo);
            }
        }
        QueueExpression::SubPlus(ci) => {
            process_concept_inclusion(&ci, state, todo);
        }
        QueueExpression::Concept(concept) => process_concept(&concept, state, todo),
    }
}

fn process_concept(concept: &Concept, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    if !state.inits.contains(concept) {
        match state.closure_subs_by_subclass.get_mut(&state.bottom) {
            None => {
                let new_super_classes_of_bottom = hashset![concept.clone()];
                state.closure_subs_by_subclass.insert(state.bottom.clone(), new_super_classes_of_bottom);
            }
            Some(super_classes_of_bottom) => {
                super_classes_of_bottom.insert(concept.clone());
            }
        }
        //TODO maybe this can be done in one step with the contains check
        state.inits.insert(concept.clone());
        rule_0(concept, state, todo);
        rule_top(concept, state, todo);
    }
}

fn process_concept_inclusion(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) -> bool {
    let seen = match state.closure_subs_by_superclass.get_mut(&ci.superclass) {
        None => {
            state.closure_subs_by_superclass.insert(ci.superclass.deref().clone(), hashset![ci.subclass.deref().clone()]);
            false
        }
        Some(subs) => match subs.insert(ci.subclass.deref().clone()) {
            None => false,
            Some(_) => true,
        },
    };
    if !seen {
        match state.closure_subs_by_subclass.get_mut(&ci.subclass) {
            None => {
                state.closure_subs_by_subclass.insert(ci.subclass.deref().clone(), hashset![ci.superclass.deref().clone()]);
            }
            Some(supers) => {
                supers.insert(ci.superclass.deref().clone());
            }
        }
        rule_bottom_left(ci, state, todo);
        rule_subclass_right(ci, state, todo);
        //TODO
        rule_plus_and_right(ci, state, todo);
        rule_plus_and_left(ci, state, todo);
        rule_plus_some_b_right(ci, state, todo);
        //rule_minus_self()
        //rule_plus_self()
        //rule_or_right()
    }
    seen
}

fn process_concept_inclusion_minus(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    rule_minus_some(ci, state, todo);
    rule_minus_and(ci, state, todo);
}

fn process_link(subject: &Concept, role: &Role, target: &Concept, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let seen = match state.links_by_subject.get_mut(subject) {
        Some(roles_to_targets) => match roles_to_targets.get_mut(role) {
            Some(targets) => match targets.insert(target.clone()) {
                None => false,
                Some(_) => true,
            },
            None => {
                roles_to_targets.insert(role.clone(), hashset![target.clone()]);
                false
            }
        },
        None => {
            let targets = hashset![target.clone()];
            let roles_to_targets = hashmap! {role.clone() => targets};
            state.links_by_subject.insert(subject.clone(), roles_to_targets);
            false
        }
    };
    if !seen {
        match state.links_by_target.get_mut(target) {
            Some(role_to_subjects) => match role_to_subjects.get_mut(role) {
                Some(subjects) => {
                    subjects.push_back(subject.clone());
                }
                None => {
                    role_to_subjects.insert(role.clone(), vector![subject.clone()]);
                }
            },
            None => {
                let subjects = vector![subject.clone()];
                let roles_to_subjects = hashmap! {role.clone() => subjects};
                state.links_by_target.insert(target.clone(), roles_to_subjects);
            }
        }
        rule_bottom_right(subject, role, target, state, todo);
        rule_plus_some_right(subject, role, target, state, todo);
        rule_ring_right(subject, role, target, state, todo);
        rule_ring_left(subject, role, target, state, todo);
        rule_squiggle(subject, role, target, state, todo);
        //rule_plus_self_nominal() //TODO
    }
}

fn rule_bottom_left(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    if ci.subclass.deref() == &state.bottom {
        if let Some(roles_to_subjects) = state.links_by_target.get(&ci.subclass) {
            for subjects in roles_to_subjects.values() {
                for subject in subjects {
                    todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: Rc::new(subject.clone()), superclass: Rc::new(state.bottom.clone()) }));
                }
            }
        }
    }
}

fn rule_bottom_right(subject: &Concept, _: &Role, target: &Concept, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(subs) = state.closure_subs_by_superclass.get(&state.bottom) {
        if subs.contains(target) {
            todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: Rc::new(subject.clone()), superclass: Rc::new(state.bottom.clone()) }));
        }
    }
}

fn rule_subclass_left(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(others) = state.closure_subs_by_superclass.get(&ci.subclass) {
        for other in others {
            todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: Rc::new(other.clone()), superclass: Rc::clone(&ci.superclass) }));
        }
    }
}

fn rule_subclass_right(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(others) = state.asserted_concept_inclusions_by_subclass.get(&ci.superclass) {
        for other in others {
            todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: Rc::clone(&ci.subclass), superclass: Rc::clone(&other.superclass) }));
        }
    }
}

fn rule_0(concept: &Concept, _: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: Rc::new(concept.clone()), superclass: Rc::new(concept.clone()) }));
}

fn rule_top(concept: &Concept, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: Rc::new(concept.clone()), superclass: Rc::new(state.top.clone()) }));
}

fn rule_minus_and(ci: &ConceptInclusion, _: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Concept::Conjunction(conjunction) = ci.superclass.deref() {
        todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: Rc::clone(&ci.subclass), superclass: Rc::clone(&conjunction.left) }));
        todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: Rc::clone(&ci.subclass), superclass: Rc::clone(&conjunction.right) }));
    }
}

fn rule_plus_and_a(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let new_negative_conjunctions = ci
        .subclass
        .concept_signature()
        .iter()
        .filter_map(|c| match c {
            Concept::Conjunction(conjunction) => {
                state.asserted_negative_conjunctions.insert(conjunction.deref().clone());
                match state.asserted_negative_conjunctions_by_left_operand.get_mut(&conjunction.left) {
                    None => {
                        let by_right_for_left = hashmap! {conjunction.right.deref().clone() => conjunction.deref().clone()};
                        state.asserted_negative_conjunctions_by_left_operand.insert(conjunction.left.deref().clone(), by_right_for_left);
                    }
                    Some(by_right_for_left) => {
                        by_right_for_left.insert(conjunction.right.deref().clone(), conjunction.deref().clone());
                    }
                };
                match state.asserted_negative_conjunctions_by_right_operand.get_mut(&conjunction.right) {
                    None => {
                        let by_left_for_right = hashmap! {conjunction.left.deref().clone() => conjunction.deref().clone()};
                        state.asserted_negative_conjunctions_by_right_operand.insert(conjunction.right.deref().clone(), by_left_for_right);
                    }
                    Some(by_left_for_right) => {
                        by_left_for_right.insert(conjunction.left.deref().clone(), conjunction.deref().clone());
                    }
                }
                Some(conjunction.deref().clone())
            }
            _ => None,
        })
        .collect();
    rule_plus_and_b(new_negative_conjunctions, state, todo);
}

fn rule_plus_and_b(new_negative_conjunctions: Vec<Conjunction>, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    for conjunction in new_negative_conjunctions {
        if let Some(left_subclasses) = state.closure_subs_by_superclass.get(&conjunction.left) {
            if let Some(right_subclasses) = state.closure_subs_by_superclass.get(&conjunction.right) {
                let common = left_subclasses.clone().intersection(right_subclasses.clone());
                for c in common {
                    todo.push(QueueExpression::SubPlus(ConceptInclusion { subclass: Rc::new(c.clone()), superclass: Rc::new(Concept::Conjunction(Rc::new(conjunction.clone()))) }));
                }
            }
        }
    }
}

fn rule_plus_and_left(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    let d1 = &ci.superclass;
    let c = &ci.subclass;
    if let Some(d2s) = state.closure_subs_by_subclass.get(c) {
        if let Some(conjunctions_matching_left) = state.asserted_negative_conjunctions_by_left_operand.get(d1) {
            // choose a join order: can make a massive performance difference
            if d2s.len() < conjunctions_matching_left.len() {
                for d2 in d2s {
                    if let Some(conjunction) = conjunctions_matching_left.get(d2) {
                        todo.push(QueueExpression::SubPlus(ConceptInclusion { subclass: Rc::clone(c), superclass: Rc::new(Concept::Conjunction(Rc::new(conjunction.clone()))) }));
                    }
                }
            } else {
                for (right, conjunction) in conjunctions_matching_left {
                    if d2s.contains(right) {
                        todo.push(QueueExpression::SubPlus(ConceptInclusion { subclass: Rc::clone(c), superclass: Rc::new(Concept::Conjunction(Rc::new(conjunction.clone()))) }));
                    }
                }
            }
        }
    }
}

fn rule_plus_and_right(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    let d2 = &ci.superclass;
    let c = &ci.subclass;
    if let Some(d1s) = state.closure_subs_by_subclass.get(c) {
        if let Some(conjunctions_matching_right) = state.asserted_negative_conjunctions_by_right_operand.get(d2) {
            // choose a join order: can make a massive performance difference
            if d1s.len() < conjunctions_matching_right.len() {
                for d1 in d1s {
                    if let Some(conjunction) = conjunctions_matching_right.get(d1) {
                        todo.push(QueueExpression::SubPlus(ConceptInclusion { subclass: Rc::clone(c), superclass: Rc::new(Concept::Conjunction(Rc::new(conjunction.clone()))) }));
                    }
                }
            } else {
                for (left, conjunction) in conjunctions_matching_right {
                    if d1s.contains(left) {
                        todo.push(QueueExpression::SubPlus(ConceptInclusion { subclass: Rc::clone(c), superclass: Rc::new(Concept::Conjunction(Rc::new(conjunction.clone()))) }));
                    }
                }
            }
        }
    }
}

fn rule_minus_some(ci: &ConceptInclusion, _: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Concept::ExistentialRestriction(er) = ci.superclass.deref() {
        todo.push(QueueExpression::Link { subject: ci.subclass.deref().clone(), role: er.role.deref().clone(), target: er.concept.deref().clone() })
    }
}

fn rule_plus_some_a(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let new_negative_existentials = ci
        .subclass
        .concept_signature()
        .iter()
        .filter_map(|c| match c {
            Concept::ExistentialRestriction(er) => {
                match state.negative_existential_restrictions_by_concept.get_mut(&er.concept) {
                    Some(ers) => {
                        ers.insert(er.deref().clone());
                    }
                    None => {
                        state.negative_existential_restrictions_by_concept.insert(er.concept.deref().clone(), hashset![er.deref().clone()]);
                    }
                }
                Some(er.deref().clone())
            }
            _ => None,
        })
        .collect();
    rule_plus_some_b_left(new_negative_existentials, state, todo);
}

fn rule_plus_some_b_left(new_negative_existentials: Vec<ExistentialRestriction>, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let mut new_propagations = vec![];
    for er in new_negative_existentials {
        if let Some(subclasses) = state.closure_subs_by_superclass.get(&er.concept) {
            for subclass in subclasses {
                new_propagations.push((subclass.clone(), er.clone()));
                match state.propagations.get_mut(subclass) {
                    Some(roles_to_ers) => match roles_to_ers.get_mut(&er.role) {
                        Some(ers) => {
                            ers.push_back(er.clone());
                        }
                        None => {
                            roles_to_ers.insert(er.role.deref().clone(), vector![er.clone()]);
                        }
                    },
                    None => {
                        state.propagations.insert(subclass.clone(), hashmap! {er.role.deref().clone() => vector![er.clone()]});
                    }
                }
            }
        }
    }
    rule_plus_some_left(new_propagations, state, todo);
}

fn rule_plus_some_b_right(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let mut new_propagations = vec![];
    if let Some(ers) = state.negative_existential_restrictions_by_concept.get(&ci.superclass) {
        for er in ers {
            new_propagations.push((ci.subclass.deref().clone(), er.clone()));
            match state.propagations.get_mut(&ci.subclass) {
                Some(roles_to_ers) => match roles_to_ers.get_mut(&er.role) {
                    Some(ers) => {
                        ers.push_back(er.clone());
                    }
                    None => {
                        roles_to_ers.insert(er.role.deref().clone(), vector![er.clone()]);
                    }
                },
                None => {
                    state.propagations.insert(ci.subclass.deref().clone(), hashmap! {er.role.deref().clone() => vector![er.clone()]});
                }
            }
        }
    };
    rule_plus_some_left(new_propagations, state, todo);
}

fn rule_plus_some_left(new_propagations: Vec<(Concept, ExistentialRestriction)>, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    for (concept, er) in new_propagations {
        if let Some(links_with_target) = state.links_by_target.get(&concept) {
            for (role, subjects) in links_with_target {
                if let Some(super_roles) = state.hier.get(role) {
                    if super_roles.contains(&er.role) {
                        for subject in subjects {
                            todo.push(QueueExpression::SubPlus(ConceptInclusion {
                                subclass: Rc::new(subject.clone()),
                                superclass: Rc::new(Concept::ExistentialRestriction(Rc::new(er.clone()))),
                            }));
                        }
                    }
                }
            }
        }
    }
}

fn rule_plus_some_right(subject: &Concept, role: &Role, target: &Concept, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(role_to_er) = state.propagations.get(target) {
        if let Some(ss) = state.hier.get(role) {
            for s in ss {
                if let Some(fs) = role_to_er.get(s) {
                    for f in fs {
                        todo.push(QueueExpression::SubPlus(ConceptInclusion {
                            subclass: Rc::new(subject.clone()),
                            superclass: Rc::new(Concept::ExistentialRestriction(Rc::new(f.clone()))),
                        }));
                    }
                }
            }
        }
    }
}

fn rule_ring_left(subject: &Concept, role: &Role, target: &Concept, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(links_by_target_for_subject) = state.links_by_target.get(subject) {
        for (r1, es) in links_by_target_for_subject {
            if let Some(r1s) = state.hier_comps.get(r1) {
                if let Some(ss) = r1s.get(role) {
                    for s in ss {
                        for e in es {
                            todo.push(QueueExpression::Link { subject: e.clone(), role: s.clone(), target: target.clone() });
                        }
                    }
                }
            }
        }
    }
}

fn rule_ring_right(subject: &Concept, role: &Role, target: &Concept, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let links_by_link_subject = state.links_by_subject.get(subject);
    if let Some(r2s) = state.hier_comps.get(role) {
        if let Some(r2_to_targets) = state.links_by_subject.get(target) {
            for (r2, targets) in r2_to_targets {
                if let Some(ss) = r2s.get(r2) {
                    for s in ss {
                        let links_with_s = links_by_link_subject.map(|x| x.get(s)).flatten();
                        for d in targets {
                            // This is just an optimization to reduce the number of redundant links put on the queue, which can be very large for this rule
                            let create_link = match links_with_s {
                                None => true,
                                Some(l) => !l.contains(d),
                            };
                            if create_link {
                                todo.push(QueueExpression::Link { subject: subject.clone(), role: s.clone(), target: d.clone() });
                            }
                        }
                    }
                }
            }
        }
    }
}

fn rule_squiggle(_: &Concept, _: &Role, target: &Concept, _: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    todo.push(QueueExpression::Concept(target.clone()));
}

fn rule_union(disjunction: &Rc<Disjunction>) -> HashSet<ConceptInclusion> {
    disjunction.operands.iter().map(|o| ConceptInclusion { subclass: Rc::clone(o), superclass: Rc::new(Concept::Disjunction(Rc::clone(disjunction))) }).collect()
}

fn rule_complement(complement: &Complement) -> HashSet<ConceptInclusion> {
    HashSet::unit(ConceptInclusion { subclass: Rc::clone(&complement.concept), superclass: Rc::new(Concept::bottom()) })
}

fn saturate_roles(role_inclusions: HashSet<RoleInclusion>, all_roles: &HashSet<Role>) -> HashMap<Role, HashSet<Role>> {
    // this can replace the following 6 lines:
    // let sub_to_super: HashMap<Rc<Role>, HashSet<Rc<Role>>> =
    //     role_inclusions.iter().map(|a| (a.subproperty.clone(), a.superproperty.clone())).into_grouping_map().collect::<HashSet<_>>().into();
    let grouped = role_inclusions.iter().into_group_map_by(|ri| ri.subproperty.deref().clone());
    let mut sub_to_super: HashMap<Role, HashSet<Role>> = HashMap::new();
    for (sub, ris) in &grouped {
        let supers = ris.iter().map(|ri| ri.superproperty.deref().clone()).collect();
        sub_to_super.insert(sub.deref().clone(), supers);
    }
    let mut result = HashMap::new();
    for role in sub_to_super.keys() {
        let all_supers = all_super_roles(role, &HashSet::new(), &sub_to_super);
        result.insert(role.clone(), all_supers);
    }
    // add reflexive role inclusions
    for role in all_roles {
        match result.get_mut(role) {
            None => {
                result.insert(role.clone(), hashset![role.clone()]);
            }
            Some(supers) => {
                supers.insert(role.clone());
            }
        }
    }
    result
}

fn all_super_roles(role: &Role, exclude: &HashSet<Role>, sub_to_super: &HashMap<Role, HashSet<Role>>) -> HashSet<Role> {
    let current_exclude = exclude.update(role.clone());
    let mut result = HashSet::new();
    for super_prop in sub_to_super.get(role).unwrap_or(&HashSet::default()).iter().filter(|super_prop| !current_exclude.contains(&super_prop)) {
        let all_supers_reflexive = all_super_roles(super_prop, &current_exclude, sub_to_super).update(super_prop.clone());
        for super_super_prop in all_supers_reflexive {
            result.insert(super_super_prop);
        }
    }
    result
}

fn index_role_compositions(hier: &HashMap<Role, HashSet<Role>>, chains: &HashSet<RoleComposition>) -> HashMap<Role, HashMap<Role, Vector<Role>>> {
    let role_comps_groups = chains.iter().group_by(|rc| (&rc.first, &rc.second));
    let mut role_comps: HashMap<(Rc<Role>, Rc<Role>), HashSet<Rc<Role>>> = HashMap::new();
    for (chain, group) in &role_comps_groups {
        let supers = group.map(|rc| Rc::clone(&rc.superproperty)).collect();
        role_comps.insert((Rc::clone(chain.0), Rc::clone(chain.1)), supers);
    }
    let hier_comps_tuples: HashSet<(Rc<Role>, Rc<Role>, Rc<Role>)> = hier
        .iter()
        .flat_map(|(r1, s1s)| {
            s1s.iter().flat_map(|s1| {
                hier.iter().flat_map(|(r2, s2s)| {
                    s2s.iter().flat_map(|s2| match role_comps.get(&(Rc::new(s1.clone()), Rc::new(s2.clone()))) {
                        Some(ss) => ss.iter().flat_map(|s| hashset![(Rc::new(r1.clone()), Rc::new(r2.clone()), Rc::clone(s))]).collect(),
                        None => HashSet::new(),
                    })
                })
            })
        })
        .collect();
    let hier_comps_remove: HashSet<(Rc<Role>, Rc<Role>, Rc<Role>)> = hier_comps_tuples
        .iter()
        .flat_map(|(r1, r2, s)| {
            hier.get(s)
                .unwrap()
                .iter()
                .filter(|super_s| super_s.deref() != s.deref())
                .filter(|super_s| hier_comps_tuples.contains(&(Rc::clone(r1), Rc::clone(r2), Rc::new(super_s.deref().clone()))))
                .flat_map(|super_s| hashset![(Rc::clone(r1), Rc::clone(r2), Rc::new(super_s.deref().clone()))])
                .collect::<HashSet<(Rc<Role>, Rc<Role>, Rc<Role>)>>()
        })
        .collect();
    let hier_comps_tuples_filtered = hier_comps_tuples.relative_complement(hier_comps_remove);
    let mut hier_comps: HashMap<Role, HashMap<Role, Vector<Role>>> = HashMap::new();
    for (r1, r2, s) in hier_comps_tuples_filtered {
        match hier_comps.get_mut(&r1) {
            Some(r2_map) => match r2_map.get_mut(&r2) {
                Some(ss) => {
                    ss.push_back(s.deref().clone());
                }
                None => {
                    let ss = vector![s.deref().clone()];
                    r2_map.insert(r2.deref().clone(), ss);
                }
            },
            None => {
                let r2_map = hashmap! {r2.deref().clone() => vector![s.deref().clone()]};
                hier_comps.insert(r1.deref().clone(), r2_map);
            }
        }
    }
    hier_comps
}

#[cfg(test)]
mod test {
    use crate::read_input;
    use crate::whelk::model as wm;
    use crate::whelk::model::TOP;
    use crate::whelk::owl::translate_ontology;
    use crate::whelk::reasoner::assert;
    use horned_owl::model::RcStr;
    use horned_owl::ontology::set::SetOntology;
    use im::{HashMap, HashSet};
    use std::ops::Deref;
    use std::rc::Rc;
    use std::{error, fs, path};

    fn load_test_ontologies(parent_path: &path::PathBuf) -> Result<(Option<SetOntology<RcStr>>, Option<SetOntology<RcStr>>, Option<SetOntology<RcStr>>), Box<dyn error::Error>> {
        let parent_name = parent_path.file_name().unwrap();
        let asserted_path = parent_path.clone().join(format!("{}-asserted.owx", parent_name.to_string_lossy()));
        let entailed_path = parent_path.clone().join(format!("{}-entailed.owx", parent_name.to_string_lossy()));
        let invalid_path = parent_path.clone().join(format!("{}-invalid.owx", parent_name.to_string_lossy()));

        let asserted_ontology = read_input(&asserted_path).expect("failed to read asserted ontology file");

        let ret = match (entailed_path.exists(), invalid_path.exists()) {
            (true, true) => {
                let entailed_ontology = read_input(&entailed_path).expect("failed to read entailed ontology file");
                let invalid_ontology = read_input(&invalid_path).expect("failed to read invalid ontology file");
                (Some(asserted_ontology), Some(entailed_ontology), Some(invalid_ontology))
            }
            (true, false) => {
                let entailed_ontology = read_input(&entailed_path).expect("failed to read entailed ontology file");
                (Some(asserted_ontology), Some(entailed_ontology), None)
            }
            (false, true) => {
                let invalid_ontology = read_input(&invalid_path).expect("failed to read invalid ontology file");
                (Some(asserted_ontology), None, Some(invalid_ontology))
            }
            _ => (None, None, None),
        };

        Ok(ret)
    }

    #[test]
    fn test_for_subclassof() {
        let data_inference_tests_dir = path::PathBuf::from("./src/data/inference-tests");
        let read_dir_results = fs::read_dir(data_inference_tests_dir).expect("no such directory?");

        let assert_entailed_whelk_axioms_exist_in_map = |whelk_subs_by_subclass: &HashMap<wm::Concept, HashSet<wm::Concept>>, whelk_axioms: &HashSet<wm::Axiom>| -> () {
            whelk_axioms.iter().for_each(|a| match a {
                wm::Axiom::ConceptInclusion(ci) => match (Rc::deref(&ci.subclass), Rc::deref(&ci.superclass)) {
                    (wm::Concept::AtomicConcept(sub), wm::Concept::AtomicConcept(sup)) => {
                        let subclass_deref = ci.subclass.deref();
                        let supclass_deref = ci.superclass.deref();
                        let values_by_subclass = whelk_subs_by_subclass.get(subclass_deref);
                        assert!(values_by_subclass.is_some(), "{}", format!("values by subclass key is not found: {:?}", subclass_deref));
                        assert!(
                            values_by_subclass.unwrap().contains(supclass_deref),
                            "{}",
                            format!("{:?} should be contained in subclass set with key {:?}", supclass_deref, subclass_deref)
                        );
                    }
                    _ => {}
                },
                _ => {}
            });
        };

        let assert_invalid_whelk_axioms_exist_in_map = |whelk_subs_by_subclass: &HashMap<wm::Concept, HashSet<wm::Concept>>, whelk_axioms: &HashSet<wm::Axiom>| -> () {
            whelk_axioms.iter().for_each(|a| match a {
                wm::Axiom::ConceptInclusion(ci) => match (Rc::deref(&ci.subclass), Rc::deref(&ci.superclass)) {
                    (wm::Concept::AtomicConcept(sub), wm::Concept::AtomicConcept(sup)) if sup.id != TOP.to_string() => {
                        let subclass_deref = ci.subclass.deref();
                        let supclass_deref = ci.superclass.deref();
                        if let Some(values_by_subclass) = whelk_subs_by_subclass.get(subclass_deref) {
                            assert!(
                                !values_by_subclass.contains(supclass_deref),
                                "{}",
                                format!("{:?} should not be contained in subclass set with key {:?}", supclass_deref, subclass_deref)
                            );
                        }
                    }
                    _ => {}
                },
                _ => {}
            });
        };

        let test_directories: Vec<path::PathBuf> = read_dir_results
            .flat_map(|a| a.map(|b| b.path()))
            .filter_map(|a| {
                let path = a.as_path();
                if path.is_dir() {
                    Some(path.to_path_buf())
                } else {
                    None
                }
            })
            .collect();

        test_directories.iter().for_each(|test_dir| {
            println!("testing directory: {:?}", test_dir);
            let (asserted_ontology, entailed_ontology, invalid_ontology) = load_test_ontologies(&test_dir).expect("could not get test ontologies");

            match (asserted_ontology, entailed_ontology, invalid_ontology) {
                (Some(ao), Some(eo), Some(io)) => {
                    let asserted_whelk_axioms = translate_ontology(&ao);

                    let whelk = assert(&asserted_whelk_axioms);
                    let whelk_subs_by_subclass = whelk.closure_subs_by_subclass;
                    // whelk_subs_by_subclass.iter().for_each(|a| println!("subclass: {:?}", a));

                    let entailed_whelk_axioms = translate_ontology(&eo);
                    assert_entailed_whelk_axioms_exist_in_map(&whelk_subs_by_subclass, &entailed_whelk_axioms);

                    let invalid_whelk_axioms = translate_ontology(&io);
                    assert_invalid_whelk_axioms_exist_in_map(&whelk_subs_by_subclass, &invalid_whelk_axioms);
                }
                (Some(ao), Some(eo), None) => {
                    let asserted_whelk_axioms = translate_ontology(&ao);

                    let whelk = assert(&asserted_whelk_axioms);
                    let whelk_subs_by_subclass = whelk.closure_subs_by_subclass;

                    let entailed_whelk_axioms = translate_ontology(&eo);
                    assert_entailed_whelk_axioms_exist_in_map(&whelk_subs_by_subclass, &entailed_whelk_axioms);
                }
                (Some(ao), None, Some(io)) => {
                    let asserted_whelk_axioms = translate_ontology(&ao);

                    let whelk = assert(&asserted_whelk_axioms);
                    let whelk_subs_by_subclass = whelk.closure_subs_by_subclass;

                    let invalid_whelk_axioms = translate_ontology(&io);
                    assert_invalid_whelk_axioms_exist_in_map(&whelk_subs_by_subclass, &invalid_whelk_axioms);
                }
                _ => {}
            }
        });
    }
}
