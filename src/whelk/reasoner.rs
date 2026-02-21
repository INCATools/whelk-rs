use im::{hashmap, hashset, vector, HashMap, HashSet, Vector};
use itertools::Itertools;

use crate::whelk::model::{
    ConceptData, ConceptId, ConceptInclusion, Interner, QueueExpression, RoleComposition,
    RoleId, RoleInclusion, TranslatedOntology,
};

#[derive(Clone, Debug)]
pub struct ReasonerState {
    pub interner: Interner,
    hier: HashMap<RoleId, HashSet<RoleId>>,
    hier_comps: HashMap<RoleId, HashMap<RoleId, Vector<RoleId>>>,
    inits: HashSet<ConceptId>,
    asserted_concept_inclusions_by_subclass: HashMap<ConceptId, Vector<ConceptInclusion>>,
    pub closure_subs_by_superclass: HashMap<ConceptId, HashSet<ConceptId>>,
    pub closure_subs_by_subclass: HashMap<ConceptId, HashSet<ConceptId>>,
    // conjunction ConceptIds indexed by left/right operand
    asserted_negative_conjunctions: HashSet<ConceptId>,
    asserted_negative_conjunctions_by_right_operand: HashMap<ConceptId, HashMap<ConceptId, ConceptId>>,
    asserted_negative_conjunctions_by_left_operand: HashMap<ConceptId, HashMap<ConceptId, ConceptId>>,
    asserted_unions: HashSet<ConceptId>,
    unions_by_operand: HashMap<ConceptId, Vector<ConceptId>>,
    links_by_subject: HashMap<ConceptId, HashMap<RoleId, HashSet<ConceptId>>>,
    links_by_target: HashMap<ConceptId, HashMap<RoleId, Vector<ConceptId>>>,
    // ER ConceptIds indexed by filler concept
    negative_existential_restrictions_by_concept: HashMap<ConceptId, HashSet<ConceptId>>,
    // ER ConceptIds indexed by (concept, role)
    propagations: HashMap<ConceptId, HashMap<RoleId, Vector<ConceptId>>>,
    asserted_negative_self_restrictions_by_role: HashMap<RoleId, ConceptId>,
    top: ConceptId,
    bottom: ConceptId,
}

impl ReasonerState {
    fn new(interner: Interner) -> ReasonerState {
        let top = interner.top();
        let bottom = interner.bottom();
        ReasonerState {
            interner,
            hier: Default::default(),
            hier_comps: Default::default(),
            inits: Default::default(),
            asserted_concept_inclusions_by_subclass: Default::default(),
            closure_subs_by_superclass: hashmap! {bottom => HashSet::new()},
            closure_subs_by_subclass: hashmap! {top => HashSet::new()},
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
            top,
            bottom,
        }
    }

    pub fn named_subsumptions(&self) -> Vec<(&str, &str)> {
        self.closure_subs_by_subclass
            .iter()
            .filter_map(|(&sub, supers)| {
                if let ConceptData::AtomicConcept(sub_name) = self.interner.concept_data(sub) {
                    Some((sub_name.as_str(), supers))
                } else {
                    None
                }
            })
            .flat_map(|(sub_name, supers)| {
                supers.iter().filter_map(move |&sup| {
                    if let ConceptData::AtomicConcept(sup_name) = self.interner.concept_data(sup) {
                        Some((sub_name, sup_name.as_str()))
                    } else {
                        None
                    }
                })
            })
            .collect()
    }

    pub fn is_subclass_of(&self, sub: ConceptId, sup: ConceptId) -> bool {
        self.closure_subs_by_subclass
            .get(&sub)
            .is_some_and(|supers| supers.contains(&sup))
    }
}

pub fn assert(ontology: &TranslatedOntology) -> ReasonerState {
    let interner = ontology.interner.clone();

    // Collect all roles from role inclusions, compositions, and concept signatures
    let mut all_roles: HashSet<RoleId> = HashSet::new();
    for ri in &ontology.role_inclusions {
        all_roles.insert(ri.subproperty);
        all_roles.insert(ri.superproperty);
    }
    for rc in &ontology.role_compositions {
        all_roles.insert(rc.first);
        all_roles.insert(rc.second);
        all_roles.insert(rc.superproperty);
    }
    for ci in &ontology.concept_inclusions {
        for role in interner.all_roles_in_concept(ci.subclass) {
            all_roles.insert(role);
        }
        for role in interner.all_roles_in_concept(ci.superclass) {
            all_roles.insert(role);
        }
    }

    let hier = saturate_roles(&ontology.role_inclusions, &all_roles);
    let hier_comps = index_role_compositions(&hier, &ontology.role_compositions);
    let mut initial_state = ReasonerState::new(interner);
    initial_state.hier = hier;
    initial_state.hier_comps = hier_comps;
    assert_append(&ontology.concept_inclusions, &initial_state)
}

pub fn assert_append(axioms: &HashSet<ConceptInclusion>, state: &ReasonerState) -> ReasonerState {
    let mut new_state = state.clone();

    let distinct_concepts: HashSet<ConceptId> = axioms
        .iter()
        .flat_map(|ci| {
            new_state.interner.concept_signature(ci.subclass)
                .union(new_state.interner.concept_signature(ci.superclass))
        })
        .collect();

    let atomic_concepts: Vec<ConceptId> = distinct_concepts
        .iter()
        .filter(|&&c| matches!(new_state.interner.concept_data(c), ConceptData::AtomicConcept(_)))
        .copied()
        .collect();

    let mut additional_axioms: HashSet<ConceptInclusion> = HashSet::new();
    for &c in &distinct_concepts {
        match new_state.interner.concept_data(c).clone() {
            ConceptData::Disjunction(operands) => {
                for ci in rule_union(c, &operands) {
                    additional_axioms.insert(ci);
                }
            }
            ConceptData::Complement(inner) => {
                additional_axioms.insert(rule_complement(inner, new_state.bottom));
            }
            _ => {}
        }
    }

    let mut assertions_queue: Vec<ConceptInclusion> = vec![];
    let mut todo: Vec<QueueExpression> = vec![];
    for &ax in axioms {
        assertions_queue.push(ax);
        todo.push(QueueExpression::ConceptInclusion(ax));
    }
    for ax in additional_axioms {
        assertions_queue.push(ax);
        todo.push(QueueExpression::ConceptInclusion(ax));
    }
    for ac in atomic_concepts {
        todo.push(QueueExpression::Concept(ac));
    }
    compute_closure(&mut new_state, assertions_queue, todo);
    new_state
}

fn compute_closure(state: &mut ReasonerState, assertions_queue: Vec<ConceptInclusion>, mut todo: Vec<QueueExpression>) {
    for ci in assertions_queue {
        process_asserted_concept_inclusion(ci, state, &mut todo);
    }
    while let Some(item) = todo.pop() {
        process(item, state, &mut todo);
    }
}

fn process_asserted_concept_inclusion(ci: ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    match state.asserted_concept_inclusions_by_subclass.get_mut(&ci.subclass) {
        None => {
            state.asserted_concept_inclusions_by_subclass.insert(ci.subclass, vector![ci]);
        }
        Some(vec) => {
            vec.push_back(ci);
        }
    }
    rule_subclass_left(&ci, state, todo);
    rule_plus_and_a(&ci, state, todo);
    rule_plus_some_a(&ci, state, todo);
}

fn process(item: QueueExpression, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    match item {
        QueueExpression::Link { subject, role, target } => process_link(subject, role, target, state, todo),
        QueueExpression::ConceptInclusion(ci) => {
            let seen = process_concept_inclusion(&ci, state, todo);
            if !seen {
                process_concept_inclusion_minus(&ci, state, todo);
            }
        }
        QueueExpression::SubPlus(ci) => {
            process_concept_inclusion(&ci, state, todo);
        }
        QueueExpression::Concept(concept) => process_concept(concept, state, todo),
    }
}

fn process_concept(concept: ConceptId, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    if !state.inits.contains(&concept) {
        match state.closure_subs_by_subclass.get_mut(&state.bottom) {
            None => {
                state.closure_subs_by_subclass.insert(state.bottom, hashset![concept]);
            }
            Some(super_classes_of_bottom) => {
                super_classes_of_bottom.insert(concept);
            }
        }
        state.inits.insert(concept);
        rule_0(concept, todo);
        rule_top(concept, state, todo);
    }
}

fn process_concept_inclusion(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) -> bool {
    let seen = match state.closure_subs_by_superclass.get_mut(&ci.superclass) {
        None => {
            state.closure_subs_by_superclass.insert(ci.superclass, hashset![ci.subclass]);
            false
        }
        Some(subs) => subs.insert(ci.subclass).is_some(),
    };
    if !seen {
        match state.closure_subs_by_subclass.get_mut(&ci.subclass) {
            None => {
                state.closure_subs_by_subclass.insert(ci.subclass, hashset![ci.superclass]);
            }
            Some(supers) => {
                supers.insert(ci.superclass);
            }
        }
        rule_bottom_left(ci, state, todo);
        rule_subclass_right(ci, state, todo);
        rule_plus_and_right(ci, state, todo);
        rule_plus_and_left(ci, state, todo);
        rule_plus_some_b_right(ci, state, todo);
    }
    seen
}

fn process_concept_inclusion_minus(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    rule_minus_some(ci, state, todo);
    rule_minus_and(ci, state, todo);
}

fn process_link(subject: ConceptId, role: RoleId, target: ConceptId, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let seen = match state.links_by_subject.get_mut(&subject) {
        Some(roles_to_targets) => match roles_to_targets.get_mut(&role) {
            Some(targets) => targets.insert(target).is_some(),
            None => {
                roles_to_targets.insert(role, hashset![target]);
                false
            }
        },
        None => {
            state.links_by_subject.insert(subject, hashmap! {role => hashset![target]});
            false
        }
    };
    if !seen {
        match state.links_by_target.get_mut(&target) {
            Some(role_to_subjects) => match role_to_subjects.get_mut(&role) {
                Some(subjects) => {
                    subjects.push_back(subject);
                }
                None => {
                    role_to_subjects.insert(role, vector![subject]);
                }
            },
            None => {
                state.links_by_target.insert(target, hashmap! {role => vector![subject]});
            }
        }
        rule_bottom_right(subject, target, state, todo);
        rule_plus_some_right(subject, role, target, state, todo);
        rule_ring_right(subject, role, target, state, todo);
        rule_ring_left(subject, role, target, state, todo);
        rule_squiggle(target, todo);
    }
}

fn rule_bottom_left(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if ci.subclass == state.bottom {
        if let Some(roles_to_subjects) = state.links_by_target.get(&ci.subclass) {
            for subjects in roles_to_subjects.values() {
                for &subject in subjects {
                    todo.push(QueueExpression::ConceptInclusion(ConceptInclusion {
                        subclass: subject,
                        superclass: state.bottom,
                    }));
                }
            }
        }
    }
}

fn rule_bottom_right(subject: ConceptId, target: ConceptId, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(subs) = state.closure_subs_by_superclass.get(&state.bottom) {
        if subs.contains(&target) {
            todo.push(QueueExpression::ConceptInclusion(ConceptInclusion {
                subclass: subject,
                superclass: state.bottom,
            }));
        }
    }
}

fn rule_subclass_left(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(others) = state.closure_subs_by_superclass.get(&ci.subclass) {
        for &other in others {
            todo.push(QueueExpression::ConceptInclusion(ConceptInclusion {
                subclass: other,
                superclass: ci.superclass,
            }));
        }
    }
}

fn rule_subclass_right(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(others) = state.asserted_concept_inclusions_by_subclass.get(&ci.superclass) {
        for other in others {
            todo.push(QueueExpression::ConceptInclusion(ConceptInclusion {
                subclass: ci.subclass,
                superclass: other.superclass,
            }));
        }
    }
}

fn rule_0(concept: ConceptId, todo: &mut Vec<QueueExpression>) {
    todo.push(QueueExpression::ConceptInclusion(ConceptInclusion {
        subclass: concept,
        superclass: concept,
    }));
}

fn rule_top(concept: ConceptId, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    todo.push(QueueExpression::ConceptInclusion(ConceptInclusion {
        subclass: concept,
        superclass: state.top,
    }));
}

fn rule_minus_and(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let ConceptData::Conjunction { left, right } = state.interner.concept_data(ci.superclass) {
        let left = *left;
        let right = *right;
        todo.push(QueueExpression::ConceptInclusion(ConceptInclusion {
            subclass: ci.subclass,
            superclass: left,
        }));
        todo.push(QueueExpression::ConceptInclusion(ConceptInclusion {
            subclass: ci.subclass,
            superclass: right,
        }));
    }
}

fn rule_plus_and_a(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let sig = state.interner.concept_signature(ci.subclass);
    let new_negative_conjunctions: Vec<ConceptId> = sig
        .iter()
        .filter_map(|&c| {
            if let ConceptData::Conjunction { left, right } = state.interner.concept_data(c) {
                let left = *left;
                let right = *right;
                state.asserted_negative_conjunctions.insert(c);
                match state.asserted_negative_conjunctions_by_left_operand.get_mut(&left) {
                    None => {
                        state.asserted_negative_conjunctions_by_left_operand.insert(left, hashmap! {right => c});
                    }
                    Some(by_right) => {
                        by_right.insert(right, c);
                    }
                }
                match state.asserted_negative_conjunctions_by_right_operand.get_mut(&right) {
                    None => {
                        state.asserted_negative_conjunctions_by_right_operand.insert(right, hashmap! {left => c});
                    }
                    Some(by_left) => {
                        by_left.insert(left, c);
                    }
                }
                Some(c)
            } else {
                None
            }
        })
        .collect();
    rule_plus_and_b(new_negative_conjunctions, state, todo);
}

fn rule_plus_and_b(new_negative_conjunctions: Vec<ConceptId>, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    for conjunction_id in new_negative_conjunctions {
        if let ConceptData::Conjunction { left, right } = state.interner.concept_data(conjunction_id) {
            let left = *left;
            let right = *right;
            if let Some(left_subclasses) = state.closure_subs_by_superclass.get(&left) {
                if let Some(right_subclasses) = state.closure_subs_by_superclass.get(&right) {
                    let common = left_subclasses.clone().intersection(right_subclasses.clone());
                    for c in common {
                        todo.push(QueueExpression::SubPlus(ConceptInclusion {
                            subclass: c,
                            superclass: conjunction_id,
                        }));
                    }
                }
            }
        }
    }
}

fn rule_plus_and_left(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    let d1 = ci.superclass;
    let c = ci.subclass;
    if let Some(d2s) = state.closure_subs_by_subclass.get(&c) {
        if let Some(conjunctions_matching_left) = state.asserted_negative_conjunctions_by_left_operand.get(&d1) {
            if d2s.len() < conjunctions_matching_left.len() {
                for &d2 in d2s {
                    if let Some(&conjunction) = conjunctions_matching_left.get(&d2) {
                        todo.push(QueueExpression::SubPlus(ConceptInclusion {
                            subclass: c,
                            superclass: conjunction,
                        }));
                    }
                }
            } else {
                for (&right, &conjunction) in conjunctions_matching_left {
                    if d2s.contains(&right) {
                        todo.push(QueueExpression::SubPlus(ConceptInclusion {
                            subclass: c,
                            superclass: conjunction,
                        }));
                    }
                }
            }
        }
    }
}

fn rule_plus_and_right(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    let d2 = ci.superclass;
    let c = ci.subclass;
    if let Some(d1s) = state.closure_subs_by_subclass.get(&c) {
        if let Some(conjunctions_matching_right) = state.asserted_negative_conjunctions_by_right_operand.get(&d2) {
            if d1s.len() < conjunctions_matching_right.len() {
                for &d1 in d1s {
                    if let Some(&conjunction) = conjunctions_matching_right.get(&d1) {
                        todo.push(QueueExpression::SubPlus(ConceptInclusion {
                            subclass: c,
                            superclass: conjunction,
                        }));
                    }
                }
            } else {
                for (&left, &conjunction) in conjunctions_matching_right {
                    if d1s.contains(&left) {
                        todo.push(QueueExpression::SubPlus(ConceptInclusion {
                            subclass: c,
                            superclass: conjunction,
                        }));
                    }
                }
            }
        }
    }
}

fn rule_minus_some(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let ConceptData::ExistentialRestriction { role, concept } = state.interner.concept_data(ci.superclass) {
        todo.push(QueueExpression::Link {
            subject: ci.subclass,
            role: *role,
            target: *concept,
        });
    }
}

fn rule_plus_some_a(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let sig = state.interner.concept_signature(ci.subclass);
    let new_negative_existentials: Vec<ConceptId> = sig
        .iter()
        .filter_map(|&c| {
            if let ConceptData::ExistentialRestriction { concept, .. } = state.interner.concept_data(c) {
                let concept = *concept;
                match state.negative_existential_restrictions_by_concept.get_mut(&concept) {
                    Some(ers) => {
                        ers.insert(c);
                    }
                    None => {
                        state.negative_existential_restrictions_by_concept.insert(concept, hashset![c]);
                    }
                }
                Some(c)
            } else {
                None
            }
        })
        .collect();
    rule_plus_some_b_left(new_negative_existentials, state, todo);
}

fn rule_plus_some_b_left(new_negative_existentials: Vec<ConceptId>, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let mut new_propagations: Vec<(ConceptId, ConceptId)> = vec![];
    for er_id in new_negative_existentials {
        if let ConceptData::ExistentialRestriction { role, concept } = state.interner.concept_data(er_id) {
            let role = *role;
            let concept = *concept;
            if let Some(subclasses) = state.closure_subs_by_superclass.get(&concept) {
                for &subclass in subclasses {
                    new_propagations.push((subclass, er_id));
                    match state.propagations.get_mut(&subclass) {
                        Some(roles_to_ers) => match roles_to_ers.get_mut(&role) {
                            Some(ers) => {
                                ers.push_back(er_id);
                            }
                            None => {
                                roles_to_ers.insert(role, vector![er_id]);
                            }
                        },
                        None => {
                            state.propagations.insert(subclass, hashmap! {role => vector![er_id]});
                        }
                    }
                }
            }
        }
    }
    rule_plus_some_left(new_propagations, state, todo);
}

fn rule_plus_some_b_right(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let mut new_propagations: Vec<(ConceptId, ConceptId)> = vec![];
    if let Some(er_ids) = state.negative_existential_restrictions_by_concept.get(&ci.superclass) {
        let er_ids: Vec<ConceptId> = er_ids.iter().copied().collect();
        for er_id in er_ids {
            if let ConceptData::ExistentialRestriction { role, .. } = state.interner.concept_data(er_id) {
                let role = *role;
                new_propagations.push((ci.subclass, er_id));
                match state.propagations.get_mut(&ci.subclass) {
                    Some(roles_to_ers) => match roles_to_ers.get_mut(&role) {
                        Some(ers) => {
                            ers.push_back(er_id);
                        }
                        None => {
                            roles_to_ers.insert(role, vector![er_id]);
                        }
                    },
                    None => {
                        state.propagations.insert(ci.subclass, hashmap! {role => vector![er_id]});
                    }
                }
            }
        }
    }
    rule_plus_some_left(new_propagations, state, todo);
}

fn rule_plus_some_left(new_propagations: Vec<(ConceptId, ConceptId)>, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    for (concept, er_id) in new_propagations {
        if let ConceptData::ExistentialRestriction { role: er_role, .. } = state.interner.concept_data(er_id) {
            let er_role = *er_role;
            if let Some(links_with_target) = state.links_by_target.get(&concept) {
                for (&role, subjects) in links_with_target {
                    if let Some(super_roles) = state.hier.get(&role) {
                        if super_roles.contains(&er_role) {
                            for &subject in subjects {
                                todo.push(QueueExpression::SubPlus(ConceptInclusion {
                                    subclass: subject,
                                    superclass: er_id,
                                }));
                            }
                        }
                    }
                }
            }
        }
    }
}

fn rule_plus_some_right(subject: ConceptId, role: RoleId, target: ConceptId, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(role_to_er) = state.propagations.get(&target) {
        if let Some(ss) = state.hier.get(&role) {
            for &s in ss {
                if let Some(fs) = role_to_er.get(&s) {
                    for &f in fs {
                        todo.push(QueueExpression::SubPlus(ConceptInclusion {
                            subclass: subject,
                            superclass: f,
                        }));
                    }
                }
            }
        }
    }
}

fn rule_ring_left(subject: ConceptId, role: RoleId, target: ConceptId, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(links_by_target_for_subject) = state.links_by_target.get(&subject) {
        for (&r1, es) in links_by_target_for_subject {
            if let Some(r1s) = state.hier_comps.get(&r1) {
                if let Some(ss) = r1s.get(&role) {
                    for &s in ss {
                        for &e in es {
                            todo.push(QueueExpression::Link { subject: e, role: s, target });
                        }
                    }
                }
            }
        }
    }
}

fn rule_ring_right(subject: ConceptId, role: RoleId, target: ConceptId, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    let links_by_link_subject = state.links_by_subject.get(&subject);
    if let Some(r2s) = state.hier_comps.get(&role) {
        if let Some(r2_to_targets) = state.links_by_subject.get(&target) {
            for (&r2, targets) in r2_to_targets {
                if let Some(ss) = r2s.get(&r2) {
                    for &s in ss {
                        let links_with_s = links_by_link_subject.and_then(|x| x.get(&s));
                        for &d in targets {
                            let create_link = match links_with_s {
                                None => true,
                                Some(l) => !l.contains(&d),
                            };
                            if create_link {
                                todo.push(QueueExpression::Link { subject, role: s, target: d });
                            }
                        }
                    }
                }
            }
        }
    }
}

fn rule_squiggle(target: ConceptId, todo: &mut Vec<QueueExpression>) {
    todo.push(QueueExpression::Concept(target));
}

fn rule_union(disjunction_id: ConceptId, operands: &HashSet<ConceptId>) -> Vec<ConceptInclusion> {
    operands
        .iter()
        .map(|&o| ConceptInclusion {
            subclass: o,
            superclass: disjunction_id,
        })
        .collect()
}

fn rule_complement(inner: ConceptId, bottom: ConceptId) -> ConceptInclusion {
    ConceptInclusion {
        subclass: inner,
        superclass: bottom,
    }
}

fn saturate_roles(role_inclusions: &HashSet<RoleInclusion>, all_roles: &HashSet<RoleId>) -> HashMap<RoleId, HashSet<RoleId>> {
    let grouped = role_inclusions.iter().into_group_map_by(|ri| ri.subproperty);
    let mut sub_to_super: HashMap<RoleId, HashSet<RoleId>> = HashMap::new();
    for (sub, ris) in &grouped {
        let supers: HashSet<RoleId> = ris.iter().map(|ri| ri.superproperty).collect();
        sub_to_super.insert(*sub, supers);
    }
    let mut result = HashMap::new();
    for &role in sub_to_super.keys() {
        let all_supers = all_super_roles(role, &HashSet::new(), &sub_to_super);
        result.insert(role, all_supers);
    }
    for &role in all_roles {
        match result.get_mut(&role) {
            None => {
                result.insert(role, hashset![role]);
            }
            Some(supers) => {
                supers.insert(role);
            }
        }
    }
    result
}

fn all_super_roles(role: RoleId, exclude: &HashSet<RoleId>, sub_to_super: &HashMap<RoleId, HashSet<RoleId>>) -> HashSet<RoleId> {
    let current_exclude = exclude.update(role);
    let mut result = HashSet::new();
    if let Some(supers) = sub_to_super.get(&role) {
        for &super_prop in supers.iter().filter(|sp| !current_exclude.contains(sp)) {
            let all_supers_reflexive = all_super_roles(super_prop, &current_exclude, sub_to_super).update(super_prop);
            for super_super_prop in all_supers_reflexive {
                result.insert(super_super_prop);
            }
        }
    }
    result
}

fn index_role_compositions(hier: &HashMap<RoleId, HashSet<RoleId>>, chains: &HashSet<RoleComposition>) -> HashMap<RoleId, HashMap<RoleId, Vector<RoleId>>> {
    let role_comps_groups = chains.iter().group_by(|rc| (rc.first, rc.second));
    let mut role_comps: HashMap<(RoleId, RoleId), HashSet<RoleId>> = HashMap::new();
    for (chain, group) in &role_comps_groups {
        let supers: HashSet<RoleId> = group.map(|rc| rc.superproperty).collect();
        role_comps.insert(chain, supers);
    }
    let mut hier_comps_tuples: HashSet<(RoleId, RoleId, RoleId)> = HashSet::new();
    for (&r1, s1s) in hier {
        for &s1 in s1s {
            for (&r2, s2s) in hier {
                for &s2 in s2s {
                    if let Some(ss) = role_comps.get(&(s1, s2)) {
                        for &s in ss {
                            hier_comps_tuples.insert((r1, r2, s));
                        }
                    }
                }
            }
        }
    }
    let mut hier_comps_remove: HashSet<(RoleId, RoleId, RoleId)> = HashSet::new();
    for &(r1, r2, s) in &hier_comps_tuples {
        for &super_s in hier.get(&s).unwrap() {
            if super_s != s && hier_comps_tuples.contains(&(r1, r2, super_s)) {
                hier_comps_remove.insert((r1, r2, super_s));
            }
        }
    }
    let hier_comps_tuples_filtered = hier_comps_tuples.relative_complement(hier_comps_remove);
    let mut hier_comps: HashMap<RoleId, HashMap<RoleId, Vector<RoleId>>> = HashMap::new();
    for (r1, r2, s) in hier_comps_tuples_filtered {
        match hier_comps.get_mut(&r1) {
            Some(r2_map) => match r2_map.get_mut(&r2) {
                Some(ss) => {
                    ss.push_back(s);
                }
                None => {
                    r2_map.insert(r2, vector![s]);
                }
            },
            None => {
                hier_comps.insert(r1, hashmap! {r2 => vector![s]});
            }
        }
    }
    hier_comps
}

#[cfg(test)]
mod test {
    use crate::read_input;
    use crate::whelk::model::{ConceptData, TranslatedOntology, TOP};
    use crate::whelk::owl::translate_ontology;
    use crate::whelk::reasoner::{assert, ReasonerState};
    use horned_owl::model::RcStr;
    use horned_owl::ontology::set::SetOntology;
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

    fn check_entailed(whelk: &ReasonerState, entailed: &TranslatedOntology) {
        let mut subs_checked = 0;
        for ci in &entailed.concept_inclusions {
            let sub_data = entailed.interner.concept_data(ci.subclass);
            let sup_data = entailed.interner.concept_data(ci.superclass);
            if let (ConceptData::AtomicConcept(sub_name), ConceptData::AtomicConcept(sup_name)) = (sub_data, sup_data) {
                let sub_id = whelk.interner.find_concept(&ConceptData::AtomicConcept(sub_name.clone()));
                let sup_id = whelk.interner.find_concept(&ConceptData::AtomicConcept(sup_name.clone()));
                if let (Some(sub_id), Some(sup_id)) = (sub_id, sup_id) {
                    let subs = whelk.closure_subs_by_subclass.get(&sub_id);
                    assert!(subs.is_some(), "values by subclass key is not found: {:?}", sub_name);
                    subs_checked += 1;
                    assert!(
                        subs.unwrap().contains(&sup_id),
                        "{:?} should be contained in subclass set with key {:?}",
                        sup_name, sub_name
                    );
                }
            }
        }
        println!("Checked {} entailed subsumptions", subs_checked);
    }

    fn check_invalid(whelk: &ReasonerState, invalid: &TranslatedOntology) {
        let mut subs_checked = 0;
        for ci in &invalid.concept_inclusions {
            let sub_data = invalid.interner.concept_data(ci.subclass);
            let sup_data = invalid.interner.concept_data(ci.superclass);
            if let (ConceptData::AtomicConcept(sub_name), ConceptData::AtomicConcept(sup_name)) = (sub_data, sup_data) {
                if sup_name != TOP {
                    let sub_id = whelk.interner.find_concept(&ConceptData::AtomicConcept(sub_name.clone()));
                    let sup_id = whelk.interner.find_concept(&ConceptData::AtomicConcept(sup_name.clone()));
                    if let (Some(sub_id), Some(sup_id)) = (sub_id, sup_id) {
                        if let Some(subs) = whelk.closure_subs_by_subclass.get(&sub_id) {
                            assert!(
                                !subs.contains(&sup_id),
                                "{:?} should not be contained in subclass set with key {:?}",
                                sup_name, sub_name
                            );
                            subs_checked += 1;
                        }
                    }
                }
            }
        }
        println!("Checked {} invalid subsumptions", subs_checked);
    }

    #[test]
    fn test_for_subclassof() {
        let data_inference_tests_dir = path::PathBuf::from("./src/data/inference-tests");
        let read_dir_results = fs::read_dir(data_inference_tests_dir).expect("no such directory?");

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
                    let translated = translate_ontology(&ao);
                    let whelk = assert(&translated);

                    let entailed = translate_ontology(&eo);
                    check_entailed(&whelk, &entailed);

                    let invalid = translate_ontology(&io);
                    check_invalid(&whelk, &invalid);
                }
                (Some(ao), Some(eo), None) => {
                    let translated = translate_ontology(&ao);
                    let whelk = assert(&translated);

                    let entailed = translate_ontology(&eo);
                    check_entailed(&whelk, &entailed);
                }
                (Some(ao), None, Some(io)) => {
                    let translated = translate_ontology(&ao);
                    let whelk = assert(&translated);

                    let invalid = translate_ontology(&io);
                    check_invalid(&whelk, &invalid);
                }
                _ => {}
            }
        });
    }
}
