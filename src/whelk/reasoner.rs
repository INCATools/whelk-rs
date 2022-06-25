use std::ops::{Add, Deref};
use std::rc::Rc;

use im::{HashMap, hashmap, HashSet, hashset, Vector, vector};
use itertools::Itertools;

use crate::whelk::model::{AtomicConcept, Axiom, BOTTOM, Complement, Concept, ConceptInclusion, Conjunction, Disjunction, Entity, ExistentialRestriction, HasSignature, QueueExpression, Role, RoleComposition, RoleInclusion, SelfRestriction, TOP};

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
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
    top: Rc<Concept>,
    bottom: Rc<Concept>,
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
            top: Rc::new(Concept::AtomicConcept(Rc::new(AtomicConcept { id: TOP.to_string() }))),
            bottom: Rc::new(Concept::AtomicConcept(Rc::new(AtomicConcept { id: BOTTOM.to_string() }))),
        }
    }
}

pub fn assert(axioms: &HashSet<Rc<Axiom>>) -> ReasonerState {
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
    let initial_state = ReasonerState {
        hier,
        hier_comps,
        ..empty
    };
    assert_append(&concept_inclusions, &initial_state)
}

pub fn assert_append(axioms: &HashSet<Rc<ConceptInclusion>>, state: &ReasonerState) -> ReasonerState {
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
    let mut new_state = state.clone();
    compute_closure(&mut new_state, assertions_queue, todo);
    new_state
}

fn compute_closure(state: &mut ReasonerState, assertions_queue: Vec<Rc<ConceptInclusion>>, mut todo: Vec<QueueExpression>) {
    for ci in assertions_queue {
        process_asserted_concept_inclusion(&ci, state, &mut todo);
    }
    while !todo.is_empty() {
        if let Some(item) = todo.pop() {
            process(item, state, &mut todo);
        }
    }
}

//val updated = reasoner.assertedConceptInclusionsBySubclass.updated(ci.subclass, ci :: reasoner.assertedConceptInclusionsBySubclass.getOrElse(ci.subclass, Nil))
//     `R⊔aleft`(ci, `R⊑left`(ci, `R+∃a`(ci, `R+⨅a`(ci, reasoner.copy(assertedConceptInclusionsBySubclass = updated)))))
fn process_asserted_concept_inclusion(ci: &Rc<ConceptInclusion>, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    match state.asserted_concept_inclusions_by_subclass.get_mut(&ci.subclass) {
        None => {
            let new_vector = vector![Rc::clone(ci)];
            state.asserted_concept_inclusions_by_subclass.insert(Rc::clone(&ci.subclass), new_vector);
        }
        Some(vec) => {
            vec.push_back(Rc::clone(ci));
        }
    }
    rule_subclass_left(ci, state, todo);
    //rule_plus_and_a()
    //rule_plus_some_a()
    //rule_or_a_left()
}

fn process(item: QueueExpression, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    match item {
        QueueExpression::Link { subject, role, target } =>
            process_link(&subject, &role, &target, state, todo),
        QueueExpression::ConceptInclusion(ci) => {
            process_concept_inclusion(&ci, state, todo);
            process_concept_inclusion_minus(&ci, state, todo);
        }
        QueueExpression::SubPlus(ci) => process_concept_inclusion(&ci, state, todo),
        QueueExpression::Concept(concept) => process_concept(&concept, state, todo),
    }
}

fn process_concept(concept: &Rc<Concept>, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    if !state.inits.contains(concept) {
        match state.closure_subs_by_subclass.get_mut(&state.bottom) {
            None => {
                let new_super_classes_of_bottom = hashset![Rc::clone(concept)];
                state.closure_subs_by_subclass.insert(Rc::clone(&state.bottom), new_super_classes_of_bottom);
            }
            Some(super_classes_of_bottom) => {
                super_classes_of_bottom.insert(Rc::clone(concept));
            }
        }
        //TODO maybe this can be done in one step with the contains check
        state.inits.insert(Rc::clone(concept));
        rule_0(concept, state, todo);
        rule_top(concept, state, todo);
    }
}

fn process_concept_inclusion(ci: &Rc<ConceptInclusion>, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let seen = match state.closure_subs_by_superclass.get_mut(&ci.superclass) {
        None => {
            state.closure_subs_by_superclass.insert(Rc::clone(&ci.superclass), hashset![Rc::clone(&ci.subclass)]);
            false
        }
        Some(subs) => {
            match subs.insert(Rc::clone(&ci.subclass)) {
                None => false,
                Some(_) => true,
            }
        }
    };
    if !seen {
        match state.closure_subs_by_subclass.get_mut(&ci.subclass) {
            None => {
                state.closure_subs_by_subclass.insert(Rc::clone(&ci.subclass), hashset![Rc::clone(&ci.superclass)]);
            }
            Some(supers) => {
                supers.insert(Rc::clone(&ci.superclass));
            }
        }
        rule_bottom_left(ci, state, todo);
        rule_subclass_right(ci, state, todo);
        //rule_plus_and_right()
        //rule_plus_and_left()
        //rule_plus_some_b_right()
        //rule_minus_self()
        //rule_plus_self()
        //rule_or_right()
    }
}

fn process_concept_inclusion_minus(ci: &Rc<ConceptInclusion>, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    //TODO
    //rule_minus_some()
    //rule_minus_and()
}

//private[this] def processLink(link: Link, reasoner: ReasonerState): ReasonerState = {
//     val Link(subject, role, target) = link
//     val rolesToTargets = reasoner.linksBySubject.getOrElse(subject, Map.empty)
//     val targetsSet = rolesToTargets.getOrElse(role, Set.empty[Concept])
//     if (targetsSet(target)) reasoner else {
//       val updatedTargetsSet = targetsSet + target
//       val updatedRolesToTargets = rolesToTargets.updated(role, updatedTargetsSet)
//       val linksBySubject = reasoner.linksBySubject.updated(subject, updatedRolesToTargets)
//       val rolesToSubjects = reasoner.linksByTarget.getOrElse(target, Map.empty)
//       val subjects = rolesToSubjects.getOrElse(role, Nil)
//       val updatedSubjects = subject :: subjects
//       val updatedRolesToSubjects = rolesToSubjects.updated(role, updatedSubjects)
//       val linksByTarget = reasoner.linksByTarget.updated(target, updatedRolesToSubjects)
//       val updatedReasoner = `R+⟲𝒪`(link, `R⤳`(link, `R∘left`(link, `R∘right`(link, `R+∃right`(link, `R⊥right`(link, reasoner.copy(linksBySubject = linksBySubject, linksByTarget = linksByTarget)))))))
//       val newState = link match {
//         case Link(Nominal(subjectInd), aRole, Nominal(targetInd)) => updatedReasoner.ruleEngine.processRoleAssertion(RoleAssertion(aRole, subjectInd, targetInd), updatedReasoner)
//         case _                                                    => updatedReasoner
//       }
//       newState.queueDelegates.keysIterator.foldLeft(newState) { (state, delegateKey) =>
//         state.queueDelegates(delegateKey).processLink(link, state)
//       }
//     }
//   }
fn process_link(subject: &Rc<Concept>, role: &Rc<Role>, target: &Rc<Concept>, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
//TODO index link
    //`R+⟲𝒪`(link, `R⤳`(link, `R∘left`(link, `R∘right`(link, `R+∃right`(link, `R⊥right`
    rule_bottom_right(subject, role, target, state, todo);
    //rule_plus_some_right()
    //rule_ring_right()
    //rule_ring_left()
    //rule_squiggle()
    //rule_plus_self_nominal()
}

fn rule_bottom_left(ci: &Rc<ConceptInclusion>, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    if ci.subclass == state.bottom {
        if let Some(roles_to_subjects) = state.links_by_target.get(&ci.subclass) {
            for subjects in roles_to_subjects.values() {
                for subject in subjects {
                    todo.push(QueueExpression::ConceptInclusion(Rc::new(
                        ConceptInclusion {
                            subclass: Rc::clone(subject),
                            superclass: Rc::clone(&state.bottom),
                        })));
                }
            }
        }
    }
}

fn rule_bottom_right(subject: &Rc<Concept>, role: &Rc<Role>, target: &Rc<Concept>, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(subs) = state.closure_subs_by_superclass.get(&state.bottom) {
        if subs.contains(target) {
            todo.push(QueueExpression::ConceptInclusion(Rc::new(
                ConceptInclusion {
                    subclass: Rc::clone(subject),
                    superclass: Rc::clone(&state.bottom),
                })));
        }
    }
}

fn rule_subclass_left(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(others) = state.closure_subs_by_superclass.get(&ci.subclass) {
        for other in others {
            todo.push(QueueExpression::ConceptInclusion(Rc::new(
                ConceptInclusion {
                    subclass: Rc::clone(other),
                    superclass: Rc::clone(&ci.superclass),
                })));
        }
    }
}

fn rule_subclass_right(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(others) = state.asserted_concept_inclusions_by_subclass.get(&ci.superclass) {
        for other in others {
            todo.push(QueueExpression::ConceptInclusion(Rc::new(
                ConceptInclusion {
                    subclass: Rc::clone(&ci.subclass),
                    superclass: Rc::clone(&other.superclass),
                })));
        }
    }
}

fn rule_0(concept: &Rc<Concept>, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    todo.push(QueueExpression::ConceptInclusion(Rc::new(
        ConceptInclusion {
            subclass: Rc::clone(concept),
            superclass: Rc::clone(concept),
        })));
}

fn rule_top(concept: &Rc<Concept>, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    todo.push(QueueExpression::ConceptInclusion(Rc::new(
        ConceptInclusion {
            subclass: Rc::clone(concept),
            superclass: Rc::clone(&state.top),
        })));
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
    let grouped = all_role_inclusions.iter()
        .group_by(|ri| &ri.subproperty);
    let mut sub_to_super: HashMap<Rc<Role>, HashSet<Rc<Role>>> = HashMap::new();
    for (sub, ris) in &grouped {
        let supers = ris.map(|ri| Rc::clone(&ri.superproperty)).collect();
        sub_to_super.insert(Rc::clone(sub), supers);
    }
    let mut result = HashMap::new();
    for role in sub_to_super.keys() {
        let all_supers = all_super_roles(role, &HashSet::new(), &sub_to_super);
        result.insert(Rc::clone(role), all_supers);
    }
    result
}

fn all_super_roles(role: &Rc<Role>, exclude: &HashSet<Rc<Role>>, sub_to_super: &HashMap<Rc<Role>, HashSet<Rc<Role>>>)
                   -> HashSet<Rc<Role>> {
    let current_exclude = exclude.update(Rc::clone(role));
    let mut result = HashSet::new();
    for super_prop in sub_to_super.get(role).unwrap_or(&HashSet::default()).iter()
        .filter(|super_prop| !current_exclude.contains(&Rc::clone(super_prop))) {
        let all_supers_reflexive = all_super_roles(super_prop, &current_exclude, sub_to_super)
            .update(Rc::clone(super_prop));
        for super_super_prop in all_supers_reflexive {
            result.insert(super_super_prop);
        }
    }
    result
}

fn index_role_compositions(hier: &HashMap<Rc<Role>, HashSet<Rc<Role>>>, chains: &HashSet<Rc<RoleComposition>>)
                           -> HashMap<Rc<Role>, HashMap<Rc<Role>, Vector<Rc<Role>>>> {

    //FIXME
    Default::default()
}
