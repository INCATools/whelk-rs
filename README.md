# whelk-rs

This is an experimental implementation of [Whelk](https://github.com/balhoff/whelk) in Rust

## Build

Clone this repo, change into the whelk-rs directory (```cd whelk-rs```), and then:
```shell
cargo build --release
```

## Running
```shell
./target/release/whelk -i path/to/ontology.owl
```

To write named class subsumptions as tab-separated IRIs:
```shell
cargo run --release -- -i path/to/ontology.owl --subsumptions
```
Use `--asserted-subsumptions` to print named class subsumptions translated from the input without running Whelk.

## Testing
```shell
cargo test --release -- --nocapture
```

## ELK validation

Install ROBOT and make sure `robot` is on `PATH`, or set `ROBOT=/path/to/robot`.
The ELK tests are ignored by default because they run external commands; mismatches are reported as test failures with example pairs.

Compare Whelk's reasoned named class subsumptions with ELK's materialized hierarchy:
```shell
scripts/compare-with-elk.sh path/to/ontology.owx target/elk-validation/ontology
```
This also writes `whelk-unsatisfiable.tsv` and asks ELK for unsatisfiability explanations in `elk-unsatisfiable.md`.

Validate the checked-in inference fixtures against ELK:
```shell
cargo test --release --test elk_validation fixture_expectations_match_elk -- --ignored --nocapture
```

Run the ignored Whelk/ELK ontology comparison as a test:
```shell
WHELK_ELK_ONTOLOGY=path/to/ontology.owx cargo test --release --test elk_validation whelk_matches_elk_for_input_ontology -- --ignored --nocapture
```
