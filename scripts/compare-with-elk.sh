#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
  echo "usage: $0 ONTOLOGY [OUTPUT_DIR]" >&2
  exit 2
fi

ontology="$1"
output_dir="${2:-target/elk-validation/$(basename "${ontology%.*}")}"
robot_bin="${ROBOT:-robot}"

mkdir -p "$output_dir"

if [ -n "${WHELK_BIN:-}" ]; then
  whelk_bin="$WHELK_BIN"
else
  cargo_build_log="$output_dir/cargo-build.log"
  if ! cargo build --release > "$cargo_build_log" 2>&1; then
    cat "$cargo_build_log" >&2
    exit 1
  fi
  whelk_bin="target/release/whelk"
fi

whelk_tsv="$output_dir/whelk-subsumptions.tsv"
elk_ontology="$output_dir/elk-materialized.owx"
elk_tsv="$output_dir/elk-subsumptions.tsv"
whelk_only="$output_dir/whelk-only.tsv"
elk_only="$output_dir/elk-only.tsv"
whelk_unsatisfiable="$output_dir/whelk-unsatisfiable.tsv"
elk_unsatisfiable="$output_dir/elk-unsatisfiable.md"

"$whelk_bin" -i "$ontology" --subsumptions | sed 's/##/#/g' | LC_ALL=C sort -u > "$whelk_tsv"
awk -F '\t' '$2 == "http://www.w3.org/2002/07/owl#Nothing" { print $1 }' "$whelk_tsv" > "$whelk_unsatisfiable"

"$robot_bin" explain \
  --input "$ontology" \
  --reasoner ELK \
  --mode unsatisfiability \
  --unsatisfiable all \
  --explanation "$elk_unsatisfiable"

if ! "$robot_bin" reason \
  --input "$ontology" \
  --reasoner ELK \
  --include-indirect true \
  --remove-redundant-subclass-axioms false \
  --create-new-ontology false \
  --exclude-duplicate-axioms false \
  --exclude-tautologies structural \
  --exclude-owl-thing true \
  --equivalent-classes-allowed all \
  --output "$elk_ontology"; then
  echo "ELK could not materialize a hierarchy. Unsatisfiability report: $elk_unsatisfiable" >&2
  exit 1
fi

"$whelk_bin" -i "$elk_ontology" --asserted-subsumptions | sed 's/##/#/g' | LC_ALL=C sort -u > "$elk_tsv"

comm -23 "$whelk_tsv" "$elk_tsv" > "$whelk_only"
comm -13 "$whelk_tsv" "$elk_tsv" > "$elk_only"

whelk_only_count="$(wc -l < "$whelk_only" | tr -d ' ')"
elk_only_count="$(wc -l < "$elk_only" | tr -d ' ')"
whelk_only_bottom_count="$(awk -F '\t' '$2 == "http://www.w3.org/2002/07/owl#Nothing" { count++ } END { print count + 0 }' "$whelk_only")"
elk_only_bottom_count="$(awk -F '\t' '$2 == "http://www.w3.org/2002/07/owl#Nothing" { count++ } END { print count + 0 }' "$elk_only")"

echo "Whelk subsumptions: $(wc -l < "$whelk_tsv" | tr -d ' ')"
echo "Whelk unsatisfiable classes: $(wc -l < "$whelk_unsatisfiable" | tr -d ' ') ($whelk_unsatisfiable)"
if grep -qx 'No explanations found.' "$elk_unsatisfiable"; then
  echo "ELK unsatisfiable classes: none reported ($elk_unsatisfiable)"
else
  echo "ELK unsatisfiability explanations: $elk_unsatisfiable"
fi
echo "ELK subsumptions:   $(wc -l < "$elk_tsv" | tr -d ' ')"
echo "Whelk only:         $whelk_only_count ($whelk_only)"
echo "  to owl:Nothing:   $whelk_only_bottom_count"
echo "ELK only:           $elk_only_count ($elk_only)"
echo "  to owl:Nothing:   $elk_only_bottom_count"

if [ "$whelk_only_count" -ne 0 ] || [ "$elk_only_count" -ne 0 ]; then
  exit 1
fi
