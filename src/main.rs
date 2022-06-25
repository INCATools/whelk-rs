use std::path::Path;
use std::rc::Rc;
use std::time::{Duration, Instant};

use horned_owl::command::parse_path;
use horned_owl::error::CommandError;
use horned_owl::io::ParserOutput;
use im::hashset;

use whelk::whelk::model::{AtomicConcept, Concept, ConceptInclusion};
use whelk::whelk::owl::{translate_axiom, translate_ontology};
use whelk::whelk::reasoner::{assert, assert_append};

fn main() {
    let start_parse = Instant::now();
    match parse_path(Path::new("ontology.owl")) {
        Ok(parsed) => {
            let rc1 = Rc::new(AtomicConcept{id: "foo".to_string()});
            let rc2 = Rc::clone(&rc1);
            let set1 = hashset![rc1];
            //println!("{}", set1.contains(&rc1));
            println!("{}", set1.contains(&rc2));
            let parse_time = start_parse.elapsed().as_secs();
            println!("Loaded ontology in {}s", parse_time);
            let start_convert = Instant::now();
            let whelk_axioms = translate_ontology(&parsed.decompose().0);
            let convert_time = start_convert.elapsed().as_millis();
            println!("Converted axioms in {}ms", convert_time);
            let start_reason = Instant::now();
            let whelk = assert(&whelk_axioms);
            let reason_time = start_reason.elapsed().as_secs();
            println!("Reasoned in {}s", reason_time);

            let ci = ConceptInclusion {
                subclass: Rc::new(Concept::AtomicConcept(Rc::new(AtomicConcept { id: "foo".to_string() }))),
                superclass: Rc::new(Concept::AtomicConcept(Rc::new(AtomicConcept { id: "bar".to_string() }))),
            };
            let new_axioms = hashset![Rc::new(ci)];
            let whelk2 = assert_append(&new_axioms, &whelk);
            println!("{}", whelk2 == whelk);
        }
        Err(error) => { dbg!("{}", error); }
    }
}
