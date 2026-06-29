use itertools::Itertools;

use crate::whelk::model::{
    ConceptData, ConceptId, ConceptInclusion, HashMap, HashSet, Interner, QueueExpression, RoleComposition, RoleId, RoleInclusion, RoleRange, TranslatedOntology, Vector,
};

#[derive(Clone, Debug)]
pub struct ReasonerState {
    pub interner: Interner,
    hier: HashMap<RoleId, HashSet<RoleId>>,
    hier_comps: HashMap<RoleId, HashMap<RoleId, Vector<RoleId>>>,
    role_ranges: HashMap<RoleId, ConceptId>,
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
            role_ranges: Default::default(),
            inits: Default::default(),
            asserted_concept_inclusions_by_subclass: Default::default(),
            closure_subs_by_superclass: std::iter::once((bottom, Default::default())).collect(),
            closure_subs_by_subclass: std::iter::once((top, Default::default())).collect(),
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
            .filter_map(|(&sub, supers)| if let ConceptData::AtomicConcept(sub_name) = self.interner.concept_data(sub) { Some((sub_name.as_str(), supers)) } else { None })
            .flat_map(|(sub_name, supers)| {
                supers.iter().filter_map(
                    move |&sup| {
                        if let ConceptData::AtomicConcept(sup_name) = self.interner.concept_data(sup) {
                            Some((sub_name, sup_name.as_str()))
                        } else {
                            None
                        }
                    },
                )
            })
            .collect()
    }

    pub fn is_subclass_of(&self, sub: ConceptId, sup: ConceptId) -> bool {
        self.closure_subs_by_subclass.get(&sub).is_some_and(|supers| supers.contains(&sup))
    }
}

pub fn assert(ontology: &TranslatedOntology) -> ReasonerState {
    let mut interner = ontology.interner.clone();

    // Collect all roles from role inclusions, compositions, ranges, and concept signatures.
    let mut all_roles: HashSet<RoleId> = Default::default();
    for ri in &ontology.role_inclusions {
        all_roles.insert(ri.subproperty);
        all_roles.insert(ri.superproperty);
    }
    for rc in &ontology.role_compositions {
        all_roles.insert(rc.first);
        all_roles.insert(rc.second);
        all_roles.insert(rc.superproperty);
    }
    for rr in &ontology.role_ranges {
        all_roles.insert(rr.role);
        for role in interner.all_roles_in_concept(rr.range) {
            all_roles.insert(role);
        }
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
    let role_ranges = index_role_ranges(&mut interner, &hier, &ontology.role_ranges);
    let role_range_concepts: HashSet<ConceptId> = role_ranges.values().flat_map(|&range| interner.concept_signature(range)).collect();
    let hier_comps = index_role_compositions(&hier, &ontology.role_compositions);
    let mut initial_state = ReasonerState::new(interner);
    initial_state.hier = hier;
    initial_state.hier_comps = hier_comps;
    initial_state.role_ranges = role_ranges;
    assert_append_with_concepts(&ontology.concept_inclusions, &initial_state, role_range_concepts)
}

pub fn assert_append(axioms: &HashSet<ConceptInclusion>, state: &ReasonerState) -> ReasonerState {
    assert_append_with_concepts(axioms, state, Default::default())
}

fn assert_append_with_concepts(axioms: &HashSet<ConceptInclusion>, state: &ReasonerState, extra_concepts: HashSet<ConceptId>) -> ReasonerState {
    let mut new_state = state.clone();

    let distinct_concepts_from_axioms: HashSet<ConceptId> =
        axioms.iter().flat_map(|ci| new_state.interner.concept_signature(ci.subclass).union(new_state.interner.concept_signature(ci.superclass))).collect();
    let distinct_concepts = distinct_concepts_from_axioms.union(extra_concepts);

    let concepts_to_queue: Vec<ConceptId> =
        distinct_concepts.iter().filter(|&&c| matches!(new_state.interner.concept_data(c), ConceptData::AtomicConcept(_) | ConceptData::Nominal(_))).copied().collect();

    let mut additional_axioms: HashSet<ConceptInclusion> = Default::default();
    for &c in &distinct_concepts {
        match new_state.interner.concept_data(c).clone() {
            ConceptData::Disjunction(operands) => {
                for ci in rule_union(c, &operands) {
                    additional_axioms.insert(ci);
                }
            }
            ConceptData::Complement(inner) => {
                additional_axioms.insert(rule_complement(c, inner, &mut new_state.interner, new_state.bottom));
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
    for concept in concepts_to_queue {
        todo.push(QueueExpression::Concept(concept));
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
            state.asserted_concept_inclusions_by_subclass.insert(ci.subclass, std::iter::once(ci).collect());
        }
        Some(vec) => {
            vec.push_back(ci);
        }
    }
    rule_subclass_left(&ci, state, todo);
    rule_plus_and_a(&ci, state, todo);
    rule_plus_some_a(&ci, state, todo);
    rule_plus_self_a(&ci, state, todo);
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
                state.closure_subs_by_subclass.insert(state.bottom, std::iter::once(concept).collect());
            }
            Some(super_classes_of_bottom) => {
                super_classes_of_bottom.insert(concept);
            }
        }
        state.inits.insert(concept);
        rule_0(concept, state, todo);
        rule_top(concept, state, todo);
    }
}

fn process_concept_inclusion(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) -> bool {
    let seen = match state.closure_subs_by_superclass.get_mut(&ci.superclass) {
        None => {
            state.closure_subs_by_superclass.insert(ci.superclass, std::iter::once(ci.subclass).collect());
            false
        }
        Some(subs) => subs.insert(ci.subclass).is_some(),
    };
    if !seen {
        match state.closure_subs_by_subclass.get_mut(&ci.subclass) {
            None => {
                state.closure_subs_by_subclass.insert(ci.subclass, std::iter::once(ci.superclass).collect());
            }
            Some(supers) => {
                supers.insert(ci.superclass);
            }
        }
        rule_bottom_left(ci, state, todo);
        rule_range_bottom_left(ci, state, todo);
        rule_subclass_right(ci, state, todo);
        rule_plus_and_right(ci, state, todo);
        rule_plus_and_left(ci, state, todo);
        rule_plus_some_b_right(ci, state, todo);
        rule_plus_self(ci, state, todo);
    }
    seen
}

fn process_concept_inclusion_minus(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    rule_minus_some(ci, state, todo);
    rule_minus_self(ci, state, todo);
    rule_minus_and(ci, state, todo);
}

fn process_link(subject: ConceptId, role: RoleId, target: ConceptId, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let seen = match state.links_by_subject.get_mut(&subject) {
        Some(roles_to_targets) => match roles_to_targets.get_mut(&role) {
            Some(targets) => targets.insert(target).is_some(),
            None => {
                roles_to_targets.insert(role, std::iter::once(target).collect());
                false
            }
        },
        None => {
            let inner: HashMap<RoleId, HashSet<ConceptId>> = std::iter::once((role, std::iter::once(target).collect())).collect();
            state.links_by_subject.insert(subject, inner);
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
                    role_to_subjects.insert(role, std::iter::once(subject).collect());
                }
            },
            None => {
                let inner: HashMap<RoleId, Vector<ConceptId>> = std::iter::once((role, std::iter::once(subject).collect())).collect();
                state.links_by_target.insert(target, inner);
            }
        }
        rule_bottom_right(subject, target, state, todo);
        rule_range_bottom_right(subject, role, target, state, todo);
        rule_plus_some_right(subject, role, target, state, todo);
        rule_plus_self_nominal_self_link(subject, role, target, state, todo);
        rule_ring_right(subject, role, target, state, todo);
        rule_ring_left(subject, role, target, state, todo);
        rule_ring_range_left(subject, role, target, state, todo);
        rule_squiggle(target, todo);
    }
}

fn rule_bottom_left(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if ci.subclass == state.bottom {
        if let Some(roles_to_subjects) = state.links_by_target.get(&ci.subclass) {
            for subjects in roles_to_subjects.values() {
                for &subject in subjects {
                    todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: subject, superclass: state.bottom }));
                }
            }
        }
    }
}

fn rule_bottom_right(subject: ConceptId, target: ConceptId, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(subs) = state.closure_subs_by_superclass.get(&state.bottom) {
        if subs.contains(&target) {
            todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: subject, superclass: state.bottom }));
        }
    }
}

fn rule_range_bottom_left(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if ci.superclass != state.bottom {
        return;
    }
    if let ConceptData::RoleTarget { range, concept: filler } = state.interner.concept_data(ci.subclass) {
        if let Some(roles_to_subjects) = state.links_by_target.get(filler) {
            for (&role, subjects) in roles_to_subjects {
                if role_has_exact_range(state, role, *range) {
                    for &subject in subjects {
                        todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: subject, superclass: state.bottom }));
                    }
                }
            }
        }
    }
}

fn rule_range_bottom_right(subject: ConceptId, role: RoleId, target: ConceptId, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if matches!(state.interner.concept_data(target), ConceptData::RoleTarget { .. }) {
        return;
    }
    if let Some(&range) = state.role_ranges.get(&role) {
        if concept_satisfies(state, target, range) {
            return;
        }
        if let Some(role_target) = find_role_target_concept(state, range, target) {
            if state.inits.contains(&role_target) && state.is_subclass_of(role_target, state.bottom) {
                todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: subject, superclass: state.bottom }));
            }
        }
    }
}

fn rule_subclass_left(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(others) = state.closure_subs_by_superclass.get(&ci.subclass) {
        for &other in others {
            todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: other, superclass: ci.superclass }));
        }
    }
}

fn rule_subclass_right(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let Some(others) = state.asserted_concept_inclusions_by_subclass.get(&ci.superclass) {
        for other in others {
            todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: ci.subclass, superclass: other.superclass }));
        }
    }
}

fn rule_0(concept: ConceptId, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let ConceptData::RoleTarget { range, concept: target } = state.interner.concept_data(concept) {
        todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: concept, superclass: *range }));
        todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: concept, superclass: *target }));
    } else {
        todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: concept, superclass: concept }));
    }
}

fn rule_top(concept: ConceptId, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: concept, superclass: state.top }));
}

fn rule_minus_and(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let ConceptData::Conjunction { left, right } = state.interner.concept_data(ci.superclass) {
        let left = *left;
        let right = *right;
        todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: ci.subclass, superclass: left }));
        todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: ci.subclass, superclass: right }));
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
                        state.asserted_negative_conjunctions_by_left_operand.insert(left, std::iter::once((right, c)).collect());
                    }
                    Some(by_right) => {
                        by_right.insert(right, c);
                    }
                }
                match state.asserted_negative_conjunctions_by_right_operand.get_mut(&right) {
                    None => {
                        state.asserted_negative_conjunctions_by_right_operand.insert(right, std::iter::once((left, c)).collect());
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
                    let (smaller, larger) = if left_subclasses.len() <= right_subclasses.len() { (left_subclasses, right_subclasses) } else { (right_subclasses, left_subclasses) };
                    for &c in smaller {
                        if larger.contains(&c) {
                            todo.push(QueueExpression::SubPlus(ConceptInclusion { subclass: c, superclass: conjunction_id }));
                        }
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
                        todo.push(QueueExpression::SubPlus(ConceptInclusion { subclass: c, superclass: conjunction }));
                    }
                }
            } else {
                for (&right, &conjunction) in conjunctions_matching_left {
                    if d2s.contains(&right) {
                        todo.push(QueueExpression::SubPlus(ConceptInclusion { subclass: c, superclass: conjunction }));
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
                        todo.push(QueueExpression::SubPlus(ConceptInclusion { subclass: c, superclass: conjunction }));
                    }
                }
            } else {
                for (&left, &conjunction) in conjunctions_matching_right {
                    if d1s.contains(&left) {
                        todo.push(QueueExpression::SubPlus(ConceptInclusion { subclass: c, superclass: conjunction }));
                    }
                }
            }
        }
    }
}

fn rule_minus_some(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let ConceptData::ExistentialRestriction { role, concept } = state.interner.concept_data(ci.superclass).clone() {
        if let Some(&range) = state.role_ranges.get(&role) {
            if !concept_satisfies(state, concept, range) {
                // Property assertions translate as {a} subclassOf exists r.{b};
                // only that non-empty nominal-to-nominal shape types the target.
                if matches!(state.interner.concept_data(ci.subclass), ConceptData::Nominal(_)) && matches!(state.interner.concept_data(concept), ConceptData::Nominal(_)) {
                    queue_derived_asserted_concept_inclusion(ConceptInclusion { subclass: concept, superclass: range }, state, todo);
                } else {
                    let role_target = role_target_concept(state, range, concept);
                    todo.push(QueueExpression::Concept(role_target));
                }
            }
        }
        todo.push(QueueExpression::Link { subject: ci.subclass, role, target: concept });
    }
}

fn queue_derived_asserted_concept_inclusion(ci: ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let already_asserted = state.asserted_concept_inclusions_by_subclass.get(&ci.subclass).is_some_and(|axioms| axioms.iter().any(|&axiom| axiom == ci));
    if !already_asserted {
        process_asserted_concept_inclusion(ci, state, todo);
    }
    todo.push(QueueExpression::ConceptInclusion(ci));
}

fn rule_minus_self(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let ConceptData::SelfRestriction(role) = state.interner.concept_data(ci.superclass) {
        if let Some(&range) = state.role_ranges.get(role) {
            todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: ci.subclass, superclass: range }));
        }
        todo.push(QueueExpression::Link { subject: ci.subclass, role: *role, target: ci.subclass });
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
                        state.negative_existential_restrictions_by_concept.insert(concept, std::iter::once(c).collect());
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
                                roles_to_ers.insert(role, std::iter::once(er_id).collect());
                            }
                        },
                        None => {
                            let inner: HashMap<RoleId, Vector<ConceptId>> = std::iter::once((role, std::iter::once(er_id).collect())).collect();
                            state.propagations.insert(subclass, inner);
                        }
                    }
                }
            }
        }
    }
    rule_plus_some_left(new_propagations, state, todo);
}

fn rule_plus_self_a(ci: &ConceptInclusion, state: &mut ReasonerState, todo: &mut Vec<QueueExpression>) {
    let sig = state.interner.concept_signature(ci.subclass);
    let mut new_negative_self_restrictions: Vec<(RoleId, ConceptId)> = vec![];
    for &concept in &sig {
        if let ConceptData::SelfRestriction(role) = state.interner.concept_data(concept) {
            let role = *role;
            if !state.asserted_negative_self_restrictions_by_role.contains_key(&role) {
                state.asserted_negative_self_restrictions_by_role.insert(role, concept);
                new_negative_self_restrictions.push((role, concept));
            }
        }
    }
    rule_plus_self_left(new_negative_self_restrictions, state, todo);
}

fn rule_plus_self_left(new_negative_self_restrictions: Vec<(RoleId, ConceptId)>, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    for (negative_role, negative_self_restriction) in new_negative_self_restrictions {
        for (&subclass, superclasses) in &state.closure_subs_by_subclass {
            for &superclass in superclasses {
                if let ConceptData::SelfRestriction(role) = state.interner.concept_data(superclass) {
                    if role_subsumes(state, *role, negative_role) {
                        todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass, superclass: negative_self_restriction }));
                    }
                }
            }
        }
        for (&subject, roles_to_targets) in &state.links_by_subject {
            if !matches!(state.interner.concept_data(subject), ConceptData::Nominal(_)) {
                continue;
            }
            for (&role, targets) in roles_to_targets {
                if targets.contains(&subject) && role_subsumes(state, role, negative_role) {
                    todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: subject, superclass: negative_self_restriction }));
                }
            }
        }
    }
}

fn rule_plus_self(ci: &ConceptInclusion, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let ConceptData::SelfRestriction(role) = state.interner.concept_data(ci.superclass) {
        let role = *role;
        for super_role in super_roles_inclusive(state, role) {
            if let Some(&self_restriction) = state.asserted_negative_self_restrictions_by_role.get(&super_role) {
                todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: ci.subclass, superclass: self_restriction }));
            }
        }
    }
}

fn rule_plus_self_nominal_self_link(subject: ConceptId, role: RoleId, target: ConceptId, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if subject == target && matches!(state.interner.concept_data(subject), ConceptData::Nominal(_)) {
        for super_role in super_roles_inclusive(state, role) {
            if let Some(&self_restriction) = state.asserted_negative_self_restrictions_by_role.get(&super_role) {
                todo.push(QueueExpression::ConceptInclusion(ConceptInclusion { subclass: subject, superclass: self_restriction }));
            }
        }
    }
}

fn super_roles_inclusive(state: &ReasonerState, role: RoleId) -> Vec<RoleId> {
    match state.hier.get(&role) {
        Some(roles) => roles.iter().copied().collect(),
        None => vec![role],
    }
}

fn role_subsumes(state: &ReasonerState, sub_role: RoleId, super_role: RoleId) -> bool {
    sub_role == super_role || state.hier.get(&sub_role).is_some_and(|super_roles| super_roles.contains(&super_role))
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
                            roles_to_ers.insert(role, std::iter::once(er_id).collect());
                        }
                    },
                    None => {
                        let inner: HashMap<RoleId, Vector<ConceptId>> = std::iter::once((role, std::iter::once(er_id).collect())).collect();
                        state.propagations.insert(ci.subclass, inner);
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
                                todo.push(QueueExpression::SubPlus(ConceptInclusion { subclass: subject, superclass: er_id }));
                            }
                        }
                    }
                }
            }
        }
        if let ConceptData::RoleTarget { range, concept: filler } = state.interner.concept_data(concept) {
            if let ConceptData::ExistentialRestriction { role: er_role, .. } = state.interner.concept_data(er_id) {
                let er_role = *er_role;
                if let Some(links_with_target) = state.links_by_target.get(filler) {
                    for (&role, subjects) in links_with_target {
                        if role_has_exact_range(state, role, *range) {
                            if let Some(super_roles) = state.hier.get(&role) {
                                if super_roles.contains(&er_role) {
                                    for &subject in subjects {
                                        todo.push(QueueExpression::SubPlus(ConceptInclusion { subclass: subject, superclass: er_id }));
                                    }
                                }
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
                        todo.push(QueueExpression::SubPlus(ConceptInclusion { subclass: subject, superclass: f }));
                    }
                }
            }
        }
    }
    if matches!(state.interner.concept_data(target), ConceptData::RoleTarget { .. }) {
        return;
    }
    if let Some(&range) = state.role_ranges.get(&role) {
        if concept_satisfies(state, target, range) {
            return;
        }
        if let Some(role_target) = find_role_target_concept(state, range, target) {
            if state.inits.contains(&role_target) {
                if let Some(role_to_er) = state.propagations.get(&role_target) {
                    if let Some(ss) = state.hier.get(&role) {
                        for &s in ss {
                            if let Some(fs) = role_to_er.get(&s) {
                                for &f in fs {
                                    todo.push(QueueExpression::SubPlus(ConceptInclusion { subclass: subject, superclass: f }));
                                }
                            }
                        }
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
        if !matches!(state.interner.concept_data(target), ConceptData::RoleTarget { .. }) {
            if let Some(&range) = state.role_ranges.get(&role) {
                if !concept_satisfies(state, target, range) {
                    if let Some(role_target) = find_role_target_concept(state, range, target) {
                        if state.inits.contains(&role_target) {
                            if let Some(r2_to_targets) = state.links_by_subject.get(&role_target) {
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
                }
            }
        }
    }
}

fn rule_ring_range_left(subject: ConceptId, role: RoleId, target: ConceptId, state: &ReasonerState, todo: &mut Vec<QueueExpression>) {
    if let ConceptData::RoleTarget { range, concept: filler } = state.interner.concept_data(subject) {
        if let Some(roles_to_subjects) = state.links_by_target.get(filler) {
            for (&r1, subjects) in roles_to_subjects {
                if role_has_exact_range(state, r1, *range) {
                    if let Some(r2s) = state.hier_comps.get(&r1) {
                        if let Some(ss) = r2s.get(&role) {
                            for &s in ss {
                                for &range_subject in subjects {
                                    todo.push(QueueExpression::Link { subject: range_subject, role: s, target });
                                }
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
    operands.iter().map(|&o| ConceptInclusion { subclass: o, superclass: disjunction_id }).collect()
}

fn rule_complement(complement: ConceptId, inner: ConceptId, interner: &mut Interner, bottom: ConceptId) -> ConceptInclusion {
    let contradiction = interner.intern_concept(ConceptData::Conjunction { left: inner, right: complement });
    ConceptInclusion { subclass: contradiction, superclass: bottom }
}

fn role_target_concept(state: &mut ReasonerState, range: ConceptId, concept: ConceptId) -> ConceptId {
    state.interner.intern_concept(ConceptData::RoleTarget { range, concept })
}

fn find_role_target_concept(state: &ReasonerState, range: ConceptId, concept: ConceptId) -> Option<ConceptId> {
    state.interner.find_concept(&ConceptData::RoleTarget { range, concept })
}

fn concept_satisfies(state: &ReasonerState, concept: ConceptId, superclass: ConceptId) -> bool {
    state.closure_subs_by_subclass.get(&concept).is_some_and(|superclasses| superclasses.contains(&superclass))
}

fn role_has_exact_range(state: &ReasonerState, role: RoleId, range: ConceptId) -> bool {
    state.role_ranges.get(&role).is_some_and(|&role_range| role_range == range)
}

fn index_role_ranges(interner: &mut Interner, hier: &HashMap<RoleId, HashSet<RoleId>>, role_range_axioms: &HashSet<RoleRange>) -> HashMap<RoleId, ConceptId> {
    let mut asserted_ranges_by_role: HashMap<RoleId, HashSet<ConceptId>> = Default::default();
    for role_range in role_range_axioms {
        match asserted_ranges_by_role.get_mut(&role_range.role) {
            Some(ranges) => {
                ranges.insert(role_range.range);
            }
            None => {
                asserted_ranges_by_role.insert(role_range.role, std::iter::once(role_range.range).collect());
            }
        }
    }

    let mut result: HashMap<RoleId, ConceptId> = Default::default();
    for (&subproperty, superproperties) in hier {
        let mut inherited_ranges: Vec<ConceptId> =
            superproperties.iter().filter_map(|superproperty| asserted_ranges_by_role.get(superproperty)).flat_map(|ranges| ranges.iter().copied()).collect();
        inherited_ranges.sort();
        inherited_ranges.dedup();
        if let Some(range) = conjunction_from_ranges(interner, inherited_ranges) {
            result.insert(subproperty, range);
        }
    }
    result
}

fn conjunction_from_ranges(interner: &mut Interner, ranges: Vec<ConceptId>) -> Option<ConceptId> {
    ranges.into_iter().reduce(|left, right| interner.intern_concept(ConceptData::Conjunction { left, right }))
}

fn saturate_roles(role_inclusions: &HashSet<RoleInclusion>, all_roles: &HashSet<RoleId>) -> HashMap<RoleId, HashSet<RoleId>> {
    let grouped = role_inclusions.iter().into_group_map_by(|ri| ri.subproperty);
    let mut sub_to_super: HashMap<RoleId, HashSet<RoleId>> = Default::default();
    for (sub, ris) in &grouped {
        let supers: HashSet<RoleId> = ris.iter().map(|ri| ri.superproperty).collect();
        sub_to_super.insert(*sub, supers);
    }
    let mut result: HashMap<RoleId, HashSet<RoleId>> = Default::default();
    for &role in sub_to_super.keys() {
        let all_supers = all_super_roles(role, &Default::default(), &sub_to_super);
        result.insert(role, all_supers);
    }
    for &role in all_roles {
        match result.get_mut(&role) {
            None => {
                result.insert(role, std::iter::once(role).collect());
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
    let mut result: HashSet<RoleId> = Default::default();
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
    let mut role_comps: HashMap<(RoleId, RoleId), HashSet<RoleId>> = Default::default();
    for rc in chains {
        match role_comps.get_mut(&(rc.first, rc.second)) {
            Some(superproperties) => {
                superproperties.insert(rc.superproperty);
            }
            None => {
                role_comps.insert((rc.first, rc.second), std::iter::once(rc.superproperty).collect());
            }
        }
    }
    let mut hier_comps_tuples: HashSet<(RoleId, RoleId, RoleId)> = Default::default();
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
    let mut hier_comps_remove: HashSet<(RoleId, RoleId, RoleId)> = Default::default();
    for &(r1, r2, s) in &hier_comps_tuples {
        for &super_s in hier.get(&s).unwrap() {
            if super_s != s && hier_comps_tuples.contains(&(r1, r2, super_s)) {
                hier_comps_remove.insert((r1, r2, super_s));
            }
        }
    }
    let hier_comps_tuples_filtered = hier_comps_tuples.relative_complement(hier_comps_remove);
    let mut hier_comps: HashMap<RoleId, HashMap<RoleId, Vector<RoleId>>> = Default::default();
    for (r1, r2, s) in hier_comps_tuples_filtered {
        match hier_comps.get_mut(&r1) {
            Some(r2_map) => match r2_map.get_mut(&r2) {
                Some(ss) => {
                    ss.push_back(s);
                }
                None => {
                    r2_map.insert(r2, std::iter::once(s).collect());
                }
            },
            None => {
                let inner: HashMap<RoleId, Vector<RoleId>> = std::iter::once((r2, std::iter::once(s).collect())).collect();
                hier_comps.insert(r1, inner);
            }
        }
    }
    hier_comps
}

#[cfg(test)]
mod test {
    use crate::read_input;
    use crate::whelk::model::{ConceptData, ConceptId, ConceptInclusion, HashSet, Interner, RoleComposition, RoleInclusion, RoleRange, TranslatedOntology, TOP};
    use crate::whelk::owl::translate_ontology;
    use crate::whelk::reasoner::{assert, assert_append, ReasonerState};
    use horned_owl::model::RcStr;
    use horned_owl::ontology::set::SetOntology;
    use std::{error, fs, path};

    #[test]
    fn self_restriction_uses_role_hierarchy() {
        let mut interner = Interner::new();
        let r = interner.intern_role("http://example.org/r");
        let s = interner.intern_role("http://example.org/s");
        let b = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/B".to_string()));
        let s_self_class = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/SSelf".to_string()));
        let self_r = interner.intern_concept(ConceptData::SelfRestriction(r));
        let self_s = interner.intern_concept(ConceptData::SelfRestriction(s));
        let ontology = TranslatedOntology {
            interner,
            concept_inclusions: vec![ConceptInclusion { subclass: b, superclass: self_r }, ConceptInclusion { subclass: self_s, superclass: s_self_class }]
                .into_iter()
                .collect::<HashSet<_>>(),
            role_inclusions: vec![RoleInclusion { subproperty: r, superproperty: s }].into_iter().collect::<HashSet<_>>(),
            role_compositions: Default::default(),
            role_ranges: Default::default(),
        };
        let whelk = assert(&ontology);
        assert!(whelk.is_subclass_of(b, s_self_class));
    }

    #[test]
    fn incremental_negative_self_restriction_replays_existing_self_subsumptions() {
        let mut interner = Interner::new();
        let r = interner.intern_role("http://example.org/r");
        let s = interner.intern_role("http://example.org/s");
        let b = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/B".to_string()));
        let s_self_class = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/SSelf".to_string()));
        let self_r = interner.intern_concept(ConceptData::SelfRestriction(r));
        let self_s = interner.intern_concept(ConceptData::SelfRestriction(s));
        let ontology = TranslatedOntology {
            interner,
            concept_inclusions: vec![ConceptInclusion { subclass: b, superclass: self_r }].into_iter().collect::<HashSet<_>>(),
            role_inclusions: vec![RoleInclusion { subproperty: r, superproperty: s }].into_iter().collect::<HashSet<_>>(),
            role_compositions: Default::default(),
            role_ranges: Default::default(),
        };
        let whelk = assert(&ontology);
        assert!(!whelk.is_subclass_of(b, s_self_class));

        let append_axioms = vec![ConceptInclusion { subclass: self_s, superclass: s_self_class }].into_iter().collect::<HashSet<_>>();
        let whelk = assert_append(&append_axioms, &whelk);
        assert!(whelk.is_subclass_of(b, s_self_class));
    }

    #[test]
    fn incremental_negative_self_restriction_replays_existing_nominal_self_links() {
        let mut interner = Interner::new();
        let r = interner.intern_role("http://example.org/r");
        let s = interner.intern_role("http://example.org/s");
        let individual = interner.intern_individual("http://example.org/a");
        let nominal = interner.intern_concept(ConceptData::Nominal(individual));
        let s_self_class = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/SSelf".to_string()));
        let self_s = interner.intern_concept(ConceptData::SelfRestriction(s));
        let r_some_nominal = interner.intern_concept(ConceptData::ExistentialRestriction { role: r, concept: nominal });
        let ontology = TranslatedOntology {
            interner,
            concept_inclusions: vec![ConceptInclusion { subclass: nominal, superclass: r_some_nominal }].into_iter().collect::<HashSet<_>>(),
            role_inclusions: vec![RoleInclusion { subproperty: r, superproperty: s }].into_iter().collect::<HashSet<_>>(),
            role_compositions: Default::default(),
            role_ranges: Default::default(),
        };
        let whelk = assert(&ontology);
        assert!(!whelk.is_subclass_of(nominal, s_self_class));

        let append_axioms = vec![ConceptInclusion { subclass: self_s, superclass: s_self_class }].into_iter().collect::<HashSet<_>>();
        let whelk = assert_append(&append_axioms, &whelk);
        assert!(whelk.is_subclass_of(nominal, s_self_class));
    }

    #[test]
    fn reflexive_property_supports_existential_classification() {
        let mut interner = Interner::new();
        let r = interner.intern_role("http://example.org/r");
        let top = interner.top();
        let a = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/A".to_string()));
        let r_some_a = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/RSomeA".to_string()));
        let self_r = interner.intern_concept(ConceptData::SelfRestriction(r));
        let some_r_a = interner.intern_concept(ConceptData::ExistentialRestriction { role: r, concept: a });
        let ontology = TranslatedOntology {
            interner,
            concept_inclusions: vec![
                ConceptInclusion { subclass: some_r_a, superclass: r_some_a },
                ConceptInclusion { subclass: r_some_a, superclass: some_r_a },
                ConceptInclusion { subclass: top, superclass: self_r },
            ]
            .into_iter()
            .collect::<HashSet<_>>(),
            role_inclusions: Default::default(),
            role_compositions: Default::default(),
            role_ranges: Default::default(),
        };
        let whelk = assert(&ontology);
        assert!(whelk.is_subclass_of(a, r_some_a));
    }

    #[test]
    fn object_property_range_uses_role_target_without_retyping_filler() {
        let mut interner = Interner::new();
        let r = interner.intern_role("http://example.org/r");
        let source = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/Source".to_string()));
        let filler = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/Filler".to_string()));
        let range = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/Range".to_string()));
        let r_some_range_class = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/RSomeRange".to_string()));
        let r_some_filler = interner.intern_concept(ConceptData::ExistentialRestriction { role: r, concept: filler });
        let r_some_range = interner.intern_concept(ConceptData::ExistentialRestriction { role: r, concept: range });

        let ontology = TranslatedOntology {
            interner,
            concept_inclusions: vec![ConceptInclusion { subclass: source, superclass: r_some_filler }, ConceptInclusion { subclass: r_some_range, superclass: r_some_range_class }]
                .into_iter()
                .collect::<HashSet<_>>(),
            role_inclusions: Default::default(),
            role_compositions: Default::default(),
            role_ranges: vec![RoleRange { role: r, range }].into_iter().collect::<HashSet<_>>(),
        };

        let whelk = assert(&ontology);

        assert!(whelk.is_subclass_of(source, r_some_range_class));
        assert!(!whelk.is_subclass_of(filler, range));
        for role_to_targets in whelk.links_by_subject.values() {
            for targets in role_to_targets.values() {
                for target in targets {
                    assert!(!matches!(whelk.interner.concept_data(*target), ConceptData::RoleTarget { .. }));
                }
            }
        }
    }

    #[test]
    fn complement_does_not_make_inner_concept_bottom() {
        let mut interner = Interner::new();
        let a = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/A".to_string()));
        let not_a = interner.intern_concept(ConceptData::Complement(a));
        let marker = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/Marker".to_string()));
        let bottom = interner.bottom();

        let ontology = TranslatedOntology {
            interner,
            concept_inclusions: vec![ConceptInclusion { subclass: not_a, superclass: marker }].into_iter().collect::<HashSet<_>>(),
            role_inclusions: Default::default(),
            role_compositions: Default::default(),
            role_ranges: Default::default(),
        };

        let whelk = assert(&ontology);

        assert!(!whelk.is_subclass_of(a, bottom));
    }

    #[test]
    fn incremental_append_does_not_reprocess_static_role_range_support_axioms() {
        let mut interner = Interner::new();
        let r = interner.intern_role("http://example.org/r");
        let range_base = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/RangeBase".to_string()));
        let range = interner.intern_concept(ConceptData::Complement(range_base));
        let appended_subclass = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/AppendedSubclass".to_string()));
        let appended_superclass = interner.intern_concept(ConceptData::AtomicConcept("http://example.org/AppendedSuperclass".to_string()));

        let ontology = TranslatedOntology {
            interner,
            concept_inclusions: Default::default(),
            role_inclusions: Default::default(),
            role_compositions: Default::default(),
            role_ranges: vec![RoleRange { role: r, range }].into_iter().collect::<HashSet<_>>(),
        };

        let whelk = assert(&ontology);
        let contradiction = whelk.interner.find_concept(&ConceptData::Conjunction { left: range_base, right: range }).unwrap();
        assert_eq!(1, asserted_axiom_count(&whelk, contradiction, whelk.bottom));

        let append_axioms = vec![ConceptInclusion { subclass: appended_subclass, superclass: appended_superclass }].into_iter().collect::<HashSet<_>>();
        let whelk = assert_append(&append_axioms, &whelk);

        assert_eq!(1, asserted_axiom_count(&whelk, contradiction, whelk.bottom));
    }

    fn asserted_axiom_count(state: &ReasonerState, subclass: ConceptId, superclass: ConceptId) -> usize {
        state.asserted_concept_inclusions_by_subclass.get(&subclass).map_or(0, |axioms| axioms.iter().filter(|&&ci| ci.subclass == subclass && ci.superclass == superclass).count())
    }

    #[test]
    fn role_composition_index_preserves_specific_superproperty_with_multiple_axioms_for_same_chain() {
        let mut interner = Interner::new();
        let part_of = interner.intern_role("http://example.org/part_of");
        let overlaps = interner.intern_role("http://example.org/overlaps");

        let role_inclusions = vec![RoleInclusion { subproperty: part_of, superproperty: overlaps }].into_iter().collect::<HashSet<_>>();
        let all_roles = vec![part_of, overlaps].into_iter().collect::<HashSet<_>>();
        let hier = super::saturate_roles(&role_inclusions, &all_roles);

        // Reproduce the failure mode of the previous group_by-based implementation by ensuring the
        // two (part_of, part_of) entries are not adjacent in set iteration order.
        let mut role_compositions: HashSet<RoleComposition> = Default::default();
        role_compositions.insert(RoleComposition { first: part_of, second: part_of, superproperty: part_of });
        role_compositions.insert(RoleComposition { first: part_of, second: part_of, superproperty: overlaps });

        let mut found_non_adjacent = false;
        for i in 0..256 {
            let id = format!("http://example.org/r{}", i);
            let r = interner.intern_role(&id);
            role_compositions.insert(RoleComposition { first: r, second: r, superproperty: r });

            let positions: Vec<_> =
                role_compositions.iter().enumerate().filter(|(_, rc)| rc.first == part_of && rc.second == part_of).map(|(idx, rc)| (idx, rc.superproperty)).collect();

            if positions.len() == 2 && positions[0].0 + 1 != positions[1].0 && positions[1].1 == overlaps {
                found_non_adjacent = true;
                break;
            }
        }
        assert!(found_non_adjacent, "test setup failed to construct non-adjacent iteration order");

        let hier_comps = super::index_role_compositions(&hier, &role_compositions);
        let indexed_superproperties = hier_comps.get(&part_of).and_then(|by_second| by_second.get(&part_of)).expect("part_of chain should be indexed");

        assert!(indexed_superproperties.iter().any(|&r| r == part_of));
    }

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
                    assert!(subs.unwrap().contains(&sup_id), "{:?} should be contained in subclass set with key {:?}", sup_name, sub_name);
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
                            assert!(!subs.contains(&sup_id), "{:?} should not be contained in subclass set with key {:?}", sup_name, sub_name);
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
