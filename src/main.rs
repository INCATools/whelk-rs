#[macro_use]
extern crate log;

use clap::Parser;
use horned_owl::io::ParserConfiguration;
use horned_owl::model::RcStr;
use horned_owl::ontology::set::SetOntology;
use humantime::format_duration;
use im::hashset;
use std::error;
use std::fs::File;
use std::io::BufReader;
use std::path;
use std::time;
use whelk::whelk::model::AtomicConcept;
use whelk::whelk::owl::translate_ontology;
use whelk::whelk::reasoner::assert;

#[derive(Parser, Debug)]
#[clap(name = "whelk", about = "whelk")]
struct Options {
    #[clap(short = 'i', long = "input", long_help = "expects an *.owl file", required = true)]
    input: path::PathBuf,
}
fn main() -> Result<(), Box<dyn error::Error>> {
    let start = time::Instant::now();
    env_logger::init();

    let options = Options::parse();
    debug!("{:?}", options);

    let path: &path::PathBuf = &options.input;
    let ontology = read_input(&path).expect("unable to parse input");
    debug!("Loaded ontology in {}s", start.elapsed().as_secs());

    // let summary = horned_bin::summary::summarize(ont.clone());
    // debug!("Logical Axioms: {}, Annotation Axioms: {}", summary.logical_axiom, summary.annotation_axiom);

    let start_convert = time::Instant::now();
    let whelk_axioms = translate_ontology(&ontology);
    debug!("Converted axioms in {}ms", start_convert.elapsed().as_millis());
    debug!("whelk_axioms.len(): {}", whelk_axioms.len());

    let start_reason = time::Instant::now();
    let whelk = assert(&whelk_axioms);
    debug!("Reasoned in {}s", start_reason.elapsed().as_secs());
    // for (sub, sup) in whelk.named_subsumptions() {
    //     println!("{}\t{}", sub.id, sup.id);
    // }

    // let ci = ConceptInclusion {
    //     subclass: Rc::new(Concept::AtomicConcept(Rc::new(AtomicConcept { id: "foo".to_string() }))),
    //     superclass: Rc::new(Concept::AtomicConcept(Rc::new(AtomicConcept { id: "bar".to_string() }))),
    // };
    // let new_axioms = hashset![Rc::new(ci)];
    // let whelk2 = assert_append(&new_axioms, &whelk);
    // println!("{}", whelk2 == whelk);
    // let whelk3 = whelk2.clone();
    // println!("{}", whelk3 == whelk);
    // println!("{}", whelk3 == whelk2);
    info!("Duration: {}", format_duration(start.elapsed()).to_string());
    Ok(())
}

fn read_input(input_path: &path::PathBuf) -> Result<SetOntology<RcStr>, Box<dyn error::Error>> {
    let file = File::open(&input_path)?;
    let mut bufreader = BufReader::new(file);
    let config = ParserConfiguration::default();
    match input_path.extension().and_then(|s| s.to_str()) {
        Some("owx") => {
            let ret = horned_owl::io::owx::reader::read(&mut bufreader, config)?;
            Ok(ret.0)
        }
        Some("owl") => {
            let ret = horned_owl::io::rdf::reader::read(&mut bufreader, config)?;
            Ok(ret.0.into())
        }
        _ => Err(Box::<dyn error::Error>::from("unable to parse input")),
    }
}

#[cfg(test)]
mod test {
    use crate::read_input;
    use horned_owl::model as hm;
    use horned_owl::ontology::set::SetOntology;
    use itertools::Itertools;
    use std::path;

    #[test]
    fn test_parse() {
        let build = hm::Build::new_rc();
        let sub_class_1 = hm::AnnotatedAxiom::from(hm::SubClassOf {
            sub: hm::ClassExpression::Class(build.class("http://purl.obolibrary.org/obo/CHEBI_24432")),
            sup: hm::ClassExpression::Class(build.class("http://purl.obolibrary.org/obo/BFO_0000023")),
        });
        let sub_class_2 = hm::AnnotatedAxiom::from(hm::SubClassOf {
            sub: hm::ClassExpression::Class(build.class("http://purl.obolibrary.org/obo/CHEBI_36080")),
            sup: hm::ClassExpression::Class(build.class("http://purl.obolibrary.org/obo/PR_000018263")),
        });

        let mut known_diffs = vec![sub_class_1, sub_class_2];

        let asserted_path = path::PathBuf::from("./src/data/go-extract-asserted.owx");
        let asserted_ontology = read_input(&asserted_path).expect("valid input???");
        // asserted_ontology.iter().for_each(|e| println!("{:?}", e));
        let mut asserted_ontology_iter = asserted_ontology.iter();
        assert!(known_diffs.iter().all(|f| !asserted_ontology_iter.contains(f)));

        let asserted_whelk_axioms = crate::translate_ontology(&asserted_ontology);
        // asserted_whelk_axioms.iter().for_each(|e| println!("{:?}", e));

        let entailed_path = path::PathBuf::from("./src/data/go-extract-entailed.owx");
        let entailed_ontology = read_input(&entailed_path).expect("valid input???");
        // entailed_ontology.iter().for_each(|e| println!("{:?}", e));
        let mut entailed_ontology_iter = entailed_ontology.iter();
        assert!(known_diffs.iter().all(|f| entailed_ontology_iter.contains(f)));
    }
}
