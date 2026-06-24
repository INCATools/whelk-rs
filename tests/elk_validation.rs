use std::collections::{BTreeSet, HashSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use whelk::read_input;
use whelk::whelk::model::{ConceptData, TranslatedOntology, BOTTOM, TOP};
use whelk::whelk::owl::translate_ontology;
use whelk::whelk::reasoner::assert as reason;

type Subsumption = (String, String);

#[test]
#[ignore = "requires ROBOT/ELK and runs external commands"]
fn fixture_expectations_match_elk() {
    let mut failures = Vec::new();

    for fixture_dir in fixture_directories() {
        let fixture_name = fixture_dir.file_name().unwrap().to_string_lossy();
        let asserted = fixture_dir.join(format!("{fixture_name}-asserted.owx"));
        let entailed = fixture_dir.join(format!("{fixture_name}-entailed.owx"));
        let invalid = fixture_dir.join(format!("{fixture_name}-invalid.owx"));

        let expected_entailed = if entailed.exists() { named_asserted_subsumptions(&read_translated(&entailed)) } else { BTreeSet::new() };
        let expected_invalid = if invalid.exists() { named_asserted_subsumptions(&read_translated(&invalid)) } else { BTreeSet::new() };

        match materialized_elk_subsumptions(&asserted) {
            Ok(elk_subsumptions) => {
                if let Some(failure) = all_present_failure(&expected_entailed, &elk_subsumptions, &format!("{fixture_name} ELK entailed")) {
                    failures.push(failure);
                }
                if let Some(failure) = all_absent_failure(&expected_invalid, &elk_subsumptions, &format!("{fixture_name} ELK invalid")) {
                    failures.push(failure);
                }
            }
            Err(error) => {
                eprintln!("ROBOT could not materialize {fixture_name}; falling back to robot explain per expected subsumption.\n{error}");
                failures.extend(explain_failures(&asserted, &expected_entailed, true, &format!("{fixture_name} ELK entailed")));
                failures.extend(explain_failures(&asserted, &expected_invalid, false, &format!("{fixture_name} ELK invalid")));
            }
        }
    }

    assert!(failures.is_empty(), "ELK fixture validation failed:\n\n{}", failures.join("\n\n"));
}

#[test]
#[ignore = "requires ROBOT/ELK and an ontology path in WHELK_ELK_ONTOLOGY"]
fn whelk_matches_elk_for_input_ontology() {
    let ontology_path = match env::var("WHELK_ELK_ONTOLOGY") {
        Ok(path) => PathBuf::from(path),
        Err(_) => {
            eprintln!("skipping: set WHELK_ELK_ONTOLOGY=/path/to/ontology.owx to compare an ontology with ELK");
            return;
        }
    };

    if !ontology_path.exists() {
        eprintln!("skipping: {} does not exist", ontology_path.display());
        return;
    }

    let whelk_subsumptions = reasoned_whelk_subsumptions(&ontology_path);
    let elk_subsumptions =
        materialized_elk_subsumptions(&ontology_path).unwrap_or_else(|error| panic!("failed to materialize ELK hierarchy for {}:\n{error}", ontology_path.display()));

    assert_equal_subsumptions(&whelk_subsumptions, &elk_subsumptions, &ontology_path.display().to_string());
}

fn fixture_directories() -> Vec<PathBuf> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/data/inference-tests");
    let mut dirs: Vec<PathBuf> = fs::read_dir(&root)
        .unwrap_or_else(|error| panic!("failed to list {}: {error}", root.display()))
        .map(|entry| entry.unwrap_or_else(|error| panic!("failed to read fixture directory entry: {error}")).path())
        .filter(|path| path.is_dir())
        .collect();
    dirs.sort();
    dirs
}

fn read_translated(path: &Path) -> TranslatedOntology {
    let path_buf = path.to_path_buf();
    let ontology = read_input(&path_buf).unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
    translate_ontology(&ontology)
}

fn named_asserted_subsumptions(ontology: &TranslatedOntology) -> BTreeSet<Subsumption> {
    ontology
        .concept_inclusions
        .iter()
        .filter_map(|ci| {
            let sub_data = ontology.interner.concept_data(ci.subclass);
            let sup_data = ontology.interner.concept_data(ci.superclass);
            match (sub_data, sup_data) {
                (ConceptData::AtomicConcept(subclass), ConceptData::AtomicConcept(superclass)) => Some((normalize_iri(subclass), normalize_iri(superclass))),
                _ => None,
            }
        })
        .filter(keep_subsumption)
        .collect()
}

fn reasoned_whelk_subsumptions(path: &Path) -> BTreeSet<Subsumption> {
    let translated = read_translated(path);
    let whelk = reason(&translated);
    whelk.named_subsumptions().into_iter().map(|(subclass, superclass)| (normalize_iri(subclass), normalize_iri(superclass))).filter(keep_subsumption).collect()
}

fn normalize_iri(iri: &str) -> String {
    iri.replace("##", "#")
}

fn keep_subsumption((subclass, superclass): &Subsumption) -> bool {
    subclass != superclass && subclass != BOTTOM && superclass != TOP
}

fn materialized_elk_subsumptions(input: &Path) -> Result<BTreeSet<Subsumption>, String> {
    let temp_dir = temp_dir("materialize");
    fs::create_dir_all(&temp_dir).map_err(|error| format!("failed to create {}: {error}", temp_dir.display()))?;
    let output_path = temp_dir.join("elk-materialized.owx");

    let output = robot_command()
        .arg("reason")
        .arg("--input")
        .arg(input)
        .arg("--reasoner")
        .arg("ELK")
        .arg("--include-indirect")
        .arg("true")
        .arg("--remove-redundant-subclass-axioms")
        .arg("false")
        .arg("--create-new-ontology")
        .arg("false")
        .arg("--exclude-duplicate-axioms")
        .arg("false")
        .arg("--exclude-tautologies")
        .arg("structural")
        .arg("--exclude-owl-thing")
        .arg("true")
        .arg("--equivalent-classes-allowed")
        .arg("all")
        .arg("--output")
        .arg(&output_path)
        .output()
        .map_err(|error| format!("failed to run ROBOT: {error}"))?;

    if !output.status.success() {
        let _ = fs::remove_dir_all(&temp_dir);
        return Err(format!(
            "ROBOT exited with status {}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }

    let subsumptions = named_asserted_subsumptions(&read_translated(&output_path));
    let _ = fs::remove_dir_all(&temp_dir);
    Ok(subsumptions)
}

fn explain_failures(input: &Path, subsumptions: &BTreeSet<Subsumption>, expected: bool, label: &str) -> Vec<String> {
    let mut failures = Vec::new();
    for subsumption in subsumptions {
        match robot_explains(input, subsumption) {
            Ok(explained) if explained == expected => {}
            Ok(_) => {
                failures.push(format!("{label}: unexpected ELK explanation result for:\n{}", format_subsumption(subsumption)));
            }
            Err(error) => {
                failures.push(format!("{label}: failed to explain {}:\n{error}", format_subsumption(subsumption)));
            }
        }
    }
    failures
}

fn robot_explains(input: &Path, subsumption: &Subsumption) -> Result<bool, String> {
    let temp_dir = temp_dir("explain");
    fs::create_dir_all(&temp_dir).map_err(|error| format!("failed to create {}: {error}", temp_dir.display()))?;
    let explanation_path = temp_dir.join("explanation.md");
    let output_path = temp_dir.join("explanation.owx");
    let (prefixes, axiom) = manchester_subclass_axiom(subsumption);

    let mut command = robot_command();
    command.arg("explain").arg("--input").arg(input).arg("--reasoner").arg("ELK").arg("--mode").arg("entailment");

    for prefix in prefixes {
        command.arg("--prefix").arg(prefix);
    }

    let output = command
        .arg("--axiom")
        .arg(axiom)
        .arg("--explanation")
        .arg(&explanation_path)
        .arg("--output")
        .arg(&output_path)
        .output()
        .map_err(|error| format!("failed to run ROBOT: {error}"))?;

    if !output.status.success() {
        let _ = fs::remove_dir_all(&temp_dir);
        return Err(format!(
            "ROBOT exited with status {}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }

    let explanation = fs::read_to_string(&explanation_path).map_err(|error| format!("failed to read {}: {error}", explanation_path.display()))?;
    let _ = fs::remove_dir_all(&temp_dir);
    Ok(!explanation.trim_start().starts_with("No explanations found."))
}

fn manchester_subclass_axiom((subclass, superclass): &Subsumption) -> (Vec<String>, String) {
    let (sub_prefix, sub_term) = manchester_class(subclass, 0);
    let (sup_prefix, sup_term) = manchester_class(superclass, 1);
    let prefixes: Vec<String> = [sub_prefix, sup_prefix].into_iter().flatten().collect::<HashSet<_>>().into_iter().collect();
    (prefixes, format!("{sub_term} SubClassOf {sup_term}"))
}

fn manchester_class(iri: &str, index: usize) -> (Option<String>, String) {
    const OWL_PREFIX: &str = "http://www.w3.org/2002/07/owl#";
    let iri = normalize_iri(iri);
    if let Some(local_name) = iri.strip_prefix(OWL_PREFIX) {
        return (Some(format!("owl: {OWL_PREFIX}")), format!("owl:{local_name}"));
    }

    let split_at = iri.rfind(|character| character == '#' || character == '/').unwrap_or_else(|| panic!("cannot create Manchester prefix for IRI without '/' or '#': {iri}"));
    let base = &iri[..=split_at];
    let local_name = &iri[split_at + 1..];
    assert!(!local_name.is_empty(), "cannot create Manchester prefix for IRI with empty local name: {iri}");

    let prefix_name = format!("w{index}");
    (Some(format!("{prefix_name}: {base}")), format!("{prefix_name}:{local_name}"))
}

fn robot_command() -> Command {
    Command::new(env::var("ROBOT").unwrap_or_else(|_| "robot".to_string()))
}

fn temp_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH).expect("system clock before UNIX_EPOCH").as_nanos();
    let sanitized_label: String = label.chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }).collect();
    env::temp_dir().join(format!("whelk-elk-validation-{}-{nanos}-{sanitized_label}", std::process::id()))
}

fn all_present_failure(expected: &BTreeSet<Subsumption>, actual: &BTreeSet<Subsumption>, label: &str) -> Option<String> {
    let missing: Vec<&Subsumption> = expected.difference(actual).collect();
    if missing.is_empty() {
        None
    } else {
        Some(format!("{label}: {} expected subsumptions were not entailed by ELK; first missing:\n{}", missing.len(), format_subsumptions(missing.into_iter().take(25))))
    }
}

fn all_absent_failure(unexpected: &BTreeSet<Subsumption>, actual: &BTreeSet<Subsumption>, label: &str) -> Option<String> {
    let present: Vec<&Subsumption> = unexpected.intersection(actual).collect();
    if present.is_empty() {
        None
    } else {
        Some(format!("{label}: {} invalid subsumptions were entailed by ELK; first present:\n{}", present.len(), format_subsumptions(present.into_iter().take(25))))
    }
}

fn assert_equal_subsumptions(whelk: &BTreeSet<Subsumption>, elk: &BTreeSet<Subsumption>, label: &str) {
    let whelk_only: Vec<&Subsumption> = whelk.difference(elk).collect();
    let elk_only: Vec<&Subsumption> = elk.difference(whelk).collect();

    assert!(
        whelk_only.is_empty() && elk_only.is_empty(),
        "{label}: Whelk/ELK subsumption mismatch\nWhelk only: {}\n{}\nELK only: {}\n{}",
        whelk_only.len(),
        format_subsumptions(whelk_only.into_iter().take(25)),
        elk_only.len(),
        format_subsumptions(elk_only.into_iter().take(25))
    );
}

fn format_subsumptions<'a>(subsumptions: impl IntoIterator<Item = &'a Subsumption>) -> String {
    let lines: Vec<String> = subsumptions.into_iter().map(format_subsumption).collect();
    if lines.is_empty() {
        "(none)".to_string()
    } else {
        lines.join("\n")
    }
}

fn format_subsumption((subclass, superclass): &Subsumption) -> String {
    format!("{subclass}\t{superclass}")
}
