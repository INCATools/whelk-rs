#[macro_use]
extern crate log;

use clap::Parser;
use humantime::format_duration;
use std::error;
use std::path;
use std::time;
use whelk::read_input;
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

    let start_convert = time::Instant::now();
    let translated = translate_ontology(&ontology);
    debug!("Converted axioms in {}ms", start_convert.elapsed().as_millis());
    debug!("concept_inclusions: {}, role_inclusions: {}, role_compositions: {}",
        translated.concept_inclusions.len(),
        translated.role_inclusions.len(),
        translated.role_compositions.len());

    let start_reason = time::Instant::now();
    let _whelk = assert(&translated);
    debug!("Reasoned in {}s", start_reason.elapsed().as_secs());

    info!("Duration: {}", format_duration(start.elapsed()).to_string());
    Ok(())
}
