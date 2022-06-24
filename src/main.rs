use std::path::Path;
use std::rc::Rc;

use horned_owl::command::parse_path;
use horned_owl::error::CommandError;
use horned_owl::io::ParserOutput;

use whelk::whelk::owl::translate_axiom;
use whelk::whelk::reasoner::assert;
use std::time::{Duration, Instant};

fn main() {
    let start_parse = Instant::now();
    match parse_path(Path::new("ontology.owl")) {
        Ok(parsed) => {
            let parse_time = start_parse.elapsed().as_secs();
            println!("Loaded ontology in {}s", parse_time);
            let start_convert = Instant::now();
            let whelk_axioms = parsed.decompose().0.iter()
                .flat_map(|ann_axiom| translate_axiom(&ann_axiom.axiom))
                .collect();
            let convert_time = start_convert.elapsed().as_millis();
            println!("Converted axioms in {}ms", convert_time);
            let start_reason = Instant::now();
            let whelk = assert(&whelk_axioms);
            let reason_time = start_reason.elapsed().as_secs();
            println!("Reasoned in {}s", reason_time);
        }
        Err(error) => { dbg!("{}", error); }
    }
}
