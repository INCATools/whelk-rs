use im::{HashMap, HashSet, Vector};

pub const TOP: &str = "http://www.w3.org/2002/07/owl#Thing";
pub const BOTTOM: &str = "http://www.w3.org/2002/07/owl#Nothing";
pub const COMPOSITION_ROLE_PREFIX: &str = "urn:whelk:composition_role:";

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct RoleId(u32);

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct ConceptId(u32);

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct IndividualId(u32);

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub enum ConceptData {
    AtomicConcept(String),
    ExistentialRestriction { role: RoleId, concept: ConceptId },
    Conjunction { left: ConceptId, right: ConceptId },
    Disjunction(HashSet<ConceptId>),
    Complement(ConceptId),
    Nominal(IndividualId),
    SelfRestriction(RoleId),
}

#[derive(Clone, Debug)]
pub struct Interner {
    roles: Vector<String>,
    role_ids: HashMap<String, RoleId>,
    individuals: Vector<String>,
    individual_ids: HashMap<String, IndividualId>,
    concepts: Vector<ConceptData>,
    concept_ids: HashMap<ConceptData, ConceptId>,
}

impl Default for Interner {
    fn default() -> Self {
        Self::new()
    }
}

impl Interner {
    pub fn new() -> Self {
        let mut interner = Interner {
            roles: Vector::new(),
            role_ids: HashMap::new(),
            individuals: Vector::new(),
            individual_ids: HashMap::new(),
            concepts: Vector::new(),
            concept_ids: HashMap::new(),
        };
        // Pre-intern TOP and BOTTOM so they have well-known IDs
        interner.intern_concept(ConceptData::AtomicConcept(TOP.to_string()));
        interner.intern_concept(ConceptData::AtomicConcept(BOTTOM.to_string()));
        interner
    }

    pub fn top(&self) -> ConceptId {
        ConceptId(0)
    }

    pub fn bottom(&self) -> ConceptId {
        ConceptId(1)
    }

    pub fn intern_role(&mut self, id: &str) -> RoleId {
        if let Some(&role_id) = self.role_ids.get(id) {
            role_id
        } else {
            let role_id = RoleId(self.roles.len() as u32);
            self.roles.push_back(id.to_string());
            self.role_ids.insert(id.to_string(), role_id);
            role_id
        }
    }

    pub fn intern_individual(&mut self, id: &str) -> IndividualId {
        if let Some(&ind_id) = self.individual_ids.get(id) {
            ind_id
        } else {
            let ind_id = IndividualId(self.individuals.len() as u32);
            self.individuals.push_back(id.to_string());
            self.individual_ids.insert(id.to_string(), ind_id);
            ind_id
        }
    }

    pub fn intern_concept(&mut self, data: ConceptData) -> ConceptId {
        if let Some(&concept_id) = self.concept_ids.get(&data) {
            concept_id
        } else {
            let concept_id = ConceptId(self.concepts.len() as u32);
            self.concepts.push_back(data.clone());
            self.concept_ids.insert(data, concept_id);
            concept_id
        }
    }

    pub fn role_name(&self, id: RoleId) -> &str {
        &self.roles[id.0 as usize]
    }

    pub fn individual_name(&self, id: IndividualId) -> &str {
        &self.individuals[id.0 as usize]
    }

    pub fn concept_data(&self, id: ConceptId) -> &ConceptData {
        &self.concepts[id.0 as usize]
    }

    pub fn find_concept(&self, data: &ConceptData) -> Option<ConceptId> {
        self.concept_ids.get(data).copied()
    }

    pub fn concept_signature(&self, id: ConceptId) -> HashSet<ConceptId> {
        match self.concept_data(id) {
            ConceptData::AtomicConcept(_) => HashSet::unit(id),
            ConceptData::Conjunction { left, right } => {
                let left = *left;
                let right = *right;
                let mut sig = self.concept_signature(left).union(self.concept_signature(right));
                sig.insert(id);
                sig
            }
            ConceptData::Disjunction(operands) => {
                let operands = operands.clone();
                operands.iter().flat_map(|&o| self.concept_signature(o)).collect()
            }
            ConceptData::ExistentialRestriction { concept, .. } => {
                let concept = *concept;
                let mut sig = self.concept_signature(concept);
                sig.insert(id);
                sig
            }
            ConceptData::SelfRestriction(_) => HashSet::unit(id),
            ConceptData::Complement(inner) => {
                let inner = *inner;
                let mut sig = self.concept_signature(inner);
                sig.insert(id);
                sig
            }
            ConceptData::Nominal(_) => HashSet::unit(id),
        }
    }

    pub fn all_roles_in_concept(&self, id: ConceptId) -> HashSet<RoleId> {
        match self.concept_data(id) {
            ConceptData::AtomicConcept(_) => HashSet::new(),
            ConceptData::Conjunction { left, right } => {
                let left = *left;
                let right = *right;
                self.all_roles_in_concept(left).union(self.all_roles_in_concept(right))
            }
            ConceptData::Disjunction(operands) => {
                let operands = operands.clone();
                operands.iter().flat_map(|&o| self.all_roles_in_concept(o)).collect()
            }
            ConceptData::ExistentialRestriction { role, concept } => {
                let role = *role;
                let concept = *concept;
                let mut sig = self.all_roles_in_concept(concept);
                sig.insert(role);
                sig
            }
            ConceptData::SelfRestriction(role) => HashSet::unit(*role),
            ConceptData::Complement(inner) => {
                let inner = *inner;
                self.all_roles_in_concept(inner)
            }
            ConceptData::Nominal(_) => HashSet::new(),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct ConceptInclusion {
    pub subclass: ConceptId,
    pub superclass: ConceptId,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct RoleInclusion {
    pub subproperty: RoleId,
    pub superproperty: RoleId,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct RoleComposition {
    pub first: RoleId,
    pub second: RoleId,
    pub superproperty: RoleId,
}

pub struct TranslatedOntology {
    pub interner: Interner,
    pub concept_inclusions: HashSet<ConceptInclusion>,
    pub role_inclusions: HashSet<RoleInclusion>,
    pub role_compositions: HashSet<RoleComposition>,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum QueueExpression {
    Concept(ConceptId),
    ConceptInclusion(ConceptInclusion),
    SubPlus(ConceptInclusion),
    Link { subject: ConceptId, role: RoleId, target: ConceptId },
}
