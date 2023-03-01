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
    use horned_owl::model::{AnnotatedAxiom, Axiom, AxiomKind, ForIRI, Kinded, RcStr, SubClassOf};
    use horned_owl::ontology::set::SetOntology;
    use itertools::Itertools;
    use std::{error, path};
    use whelk::whelk::owl::{concept_inclusion, convert_expression};

    fn load_test_ontologies(dir: &str) -> Result<(Option<SetOntology<RcStr>>, Option<SetOntology<RcStr>>, Option<SetOntology<RcStr>>), Box<dyn error::Error>> {
        let parent_path = path::PathBuf::from("./src/data/inference-tests");

        let mut asserted_path = parent_path.clone().join(dir).join(format!("{}-asserted.owx", dir));
        let mut entailed_path = parent_path.clone().join(dir).join(format!("{}-entailed.owx", dir));
        let mut invalid_path = parent_path.clone().join(dir).join(format!("{}-invalid.owx", dir));

        let ret = match (asserted_path.exists(), entailed_path.exists(), invalid_path.exists()) {
            (true, true, true) => {
                let asserted_ontology = read_input(&asserted_path).expect("failed to read asserted_ontology");
                let entailed_ontology = read_input(&entailed_path).expect("failed to read entailed_ontology");
                let invalid_ontology = read_input(&invalid_path).expect("failed to read invalid_ontology");
                (Some(asserted_ontology), Some(entailed_ontology), Some(invalid_ontology))
            }
            (true, true, false) => {
                let asserted_ontology = read_input(&asserted_path).expect("failed to read asserted_ontology");
                let entailed_ontology = read_input(&entailed_path).expect("failed to read entailed_ontology");
                (Some(asserted_ontology), Some(entailed_ontology), None)
            }
            _ => (None, None, None),
        };

        Ok(ret)
    }

    macro_rules! subclassof_test {
        ($name:ident, $dir:literal) => {
            #[test]
            fn $name() {
                let (asserted_ontology, entailed_ontology, invalid_ontology) = load_test_ontologies($dir).expect("could not get test ontologies");
                match (asserted_ontology, entailed_ontology, invalid_ontology) {
                    (Some(ao), Some(eo), Some(io)) => {
                        let asserted_whelk_axioms = crate::translate_ontology(&ao);
                        let eo_subclassofs: Vec<_> = eo.into_iter().filter(|a| a.axiom.kind() == AxiomKind::SubClassOf).map(|a| a.axiom).collect();
                        eo_subclassofs.iter().for_each(|e| match e {
                            hm::Axiom::SubClassOf(ax) => {
                                match (convert_expression(&ax.sub), convert_expression(&ax.sup)) {
                                    (Some(subclass), Some(superclass)) => {
                                        let ci = concept_inclusion(&subclass, &superclass);
                                        println!("{:?}", ci);
                                        assert!(asserted_whelk_axioms.iter().contains(&ci));
                                    }
                                    _ => {}
                                };
                            }
                            _ => {}
                        });
                        let io_subclassofs: Vec<_> = io.into_iter().filter(|a| a.axiom.kind() == AxiomKind::SubClassOf).map(|a| a.axiom).collect();
                        io_subclassofs.iter().for_each(|e| match e {
                            hm::Axiom::SubClassOf(ax) => {
                                match (convert_expression(&ax.sub), convert_expression(&ax.sup)) {
                                    (Some(subclass), Some(superclass)) => {
                                        let ci = concept_inclusion(&subclass, &superclass);
                                        println!("{:?}", ci);
                                        assert!(!asserted_whelk_axioms.iter().contains(&ci));
                                    }
                                    _ => {}
                                };
                            }
                            _ => {}
                        });
                    }
                    (Some(ao), Some(eo), None) => {
                        let asserted_whelk_axioms = crate::translate_ontology(&ao);
                        let eo_subclassofs: Vec<_> = eo.into_iter().filter(|a| a.axiom.kind() == AxiomKind::SubClassOf).map(|a| a.axiom).collect();
                        eo_subclassofs.iter().for_each(|e| match e {
                            hm::Axiom::SubClassOf(ax) => {
                                match (convert_expression(&ax.sub), convert_expression(&ax.sup)) {
                                    (Some(subclass), Some(superclass)) => {
                                        let ci = concept_inclusion(&subclass, &superclass);
                                        println!("{:?}", ci);
                                        assert!(asserted_whelk_axioms.iter().contains(&ci));
                                    }
                                    _ => {}
                                };
                            }
                            _ => {}
                        });
                    }
                    _ => {}
                }
            }
        };
    }

    subclassof_test!(test_for_subclassof_go_extract, "go-extract");
    subclassof_test!(test_for_subclassof_skeletons, "skeletons");
}
