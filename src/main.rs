#[macro_use]
extern crate log;

use clap::Parser;
use horned_bin::parse_path;
use horned_owl::io::ParserConfiguration;
use humantime::format_duration;
use im::hashset;
use std::error;
use std::path;
use std::rc::Rc;
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

    let owl_ont = parse_path(&options.input, ParserConfiguration::default()).expect("could not parse path");

    let rc1 = Rc::new(AtomicConcept { id: "foo".to_string() });
    let rc2 = Rc::clone(&rc1);
    let set1 = hashset![rc1];
    debug!("{}", set1.contains(&rc2));
    debug!("Loaded ontology in {}s", start.elapsed().as_secs());
    let start_convert = time::Instant::now();
    let whelk_axioms = translate_ontology(&owl_ont.decompose().0);
    debug!("Converted axioms in {}ms", start_convert.elapsed().as_millis());
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
