use std::path::Path;
use std::rc::Rc;

use horned_owl::command::parse_path;
use horned_owl::error::CommandError;
use horned_owl::io::ParserOutput;

use whelk::whelk::owl::translate_axiom;
use whelk::whelk::reasoner::assert;

fn main() {
    match parse_path(Path::new("ontology.owl")) {
        Ok(parsed) => {
            let whelk_axioms = parsed.decompose().0.iter()
                .flat_map(|ann_axiom| translate_axiom(&ann_axiom.axiom))
                .collect();
            let whelk = assert(&whelk_axioms);
        }
        Err(error) => { dbg!("{}", error); }
    }
}
