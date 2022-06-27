use std::path::Path;
use std::rc::Rc;
use std::time::Instant;

use horned_owl::command::parse_path;
use im::hashset;

use whelk::whelk::model::AtomicConcept;
use whelk::whelk::owl::translate_ontology;
use whelk::whelk::reasoner::{assert, assert_append};

fn main() {
    let start_parse = Instant::now();
    match parse_path(Path::new("ontology.owl")) {
        Ok(parsed) => {
            let rc1 = Rc::new(AtomicConcept { id: "foo".to_string() });
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
        }
        Err(error) => { dbg!("{}", error); }
    }
}
