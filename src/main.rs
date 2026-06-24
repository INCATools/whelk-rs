#[macro_use]
extern crate log;

use clap::Parser;
use humantime::format_duration;
use std::error;
use std::path;
use std::time;
use whelk::read_input;
use whelk::whelk::model::{ConceptData, TranslatedOntology, BOTTOM, TOP};
use whelk::whelk::owl::translate_ontology;
use whelk::whelk::reasoner::assert;

#[derive(Parser, Debug)]
#[clap(name = "whelk", about = "whelk")]
struct Options {
    #[clap(short = 'i', long = "input", long_help = "expects an *.owl file", required = true)]
    input: path::PathBuf,
    #[clap(long = "subsumptions", long_help = "print reasoned named class subsumptions as TSV")]
    subsumptions: bool,
    #[clap(long = "asserted-subsumptions", long_help = "print named class subsumptions translated directly from the input as TSV", conflicts_with = "subsumptions")]
    asserted_subsumptions: bool,
    #[clap(long = "include-tautologies", long_help = "include self-subsumptions and owl:Nothing tautologies in TSV output")]
    include_tautologies: bool,
    #[clap(long = "include-owl-thing", long_help = "include subsumptions to owl:Thing in TSV output")]
    include_owl_thing: bool,
}

fn main() -> Result<(), Box<dyn error::Error>> {
    let start = time::Instant::now();
    env_logger::init();

    let options = Options::parse();
    debug!("{:?}", options);

    let path: &path::PathBuf = &options.input;
    let ontology = read_input(path).expect("unable to parse input");
    debug!("Loaded ontology in {}s", start.elapsed().as_secs());

    let start_convert = time::Instant::now();
    let translated = translate_ontology(&ontology);
    debug!("Converted axioms in {}ms", start_convert.elapsed().as_millis());
    debug!(
        "concept_inclusions: {}, role_inclusions: {}, role_compositions: {}, role_ranges: {}",
        translated.concept_inclusions.len(),
        translated.role_inclusions.len(),
        translated.role_compositions.len(),
        translated.role_ranges.len()
    );

    if options.asserted_subsumptions {
        print_subsumptions(named_asserted_subsumptions(&translated), &options);
        return Ok(());
    }

    let start_reason = time::Instant::now();
    let whelk = assert(&translated);
    debug!("Reasoned in {}s", start_reason.elapsed().as_secs());

    if options.subsumptions {
        print_subsumptions(whelk.named_subsumptions().into_iter().map(|(subclass, superclass)| (subclass.to_string(), superclass.to_string())).collect(), &options);
    }

    info!("Duration: {}", format_duration(start.elapsed()).to_string());
    Ok(())
}

fn named_asserted_subsumptions(ontology: &TranslatedOntology) -> Vec<(String, String)> {
    ontology
        .concept_inclusions
        .iter()
        .filter_map(|ci| {
            let sub_data = ontology.interner.concept_data(ci.subclass);
            let sup_data = ontology.interner.concept_data(ci.superclass);
            match (sub_data, sup_data) {
                (ConceptData::AtomicConcept(subclass), ConceptData::AtomicConcept(superclass)) => Some((subclass.clone(), superclass.clone())),
                _ => None,
            }
        })
        .collect()
}

fn print_subsumptions(mut subsumptions: Vec<(String, String)>, options: &Options) {
    subsumptions.retain(|(subclass, superclass)| {
        let is_tautology = subclass == superclass || subclass == BOTTOM;
        let is_thing = superclass == TOP;
        (!is_tautology || options.include_tautologies) && (!is_thing || options.include_owl_thing)
    });
    subsumptions.sort();
    subsumptions.dedup();
    for (subclass, superclass) in subsumptions {
        println!("{subclass}\t{superclass}");
    }
}
