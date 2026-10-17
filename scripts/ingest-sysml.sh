#!/usr/bin/env bash
# SysML v2 PKC DSL → Lean: convert each model with OpenSysML, read it into a `PkcModel`,
# write the generated Lean module, and have the kernel check it.
#
#   scripts/ingest-sysml.sh sysml/examples/HarmonicOscillator.sysml [more.sysml …]
#
# Needs OpenSysML's `sysml` on PATH (or SYSML=/path/to/sysml) and `lake build Interchange`.
set -euo pipefail
cd "$(dirname "$0")/.."
SYSML="${SYSML:-sysml}"
mkdir -p .lake/build/sysml
jsons=()
for model in "$@"; do
  pkg="$(basename "$model" .sysml)"
  out=".lake/build/sysml/$pkg.api.json"
  "$SYSML" -convert api-json sysml/PKC.sysml "$model" > "$out"
  jsons+=("$out")
done
generated=".lake/build/sysml/generated-modules.txt"
PKC_INGEST="$(IFS=,; echo "${jsons[*]}")" PKC_INGEST_OUT="$generated" lake env lean scripts/ingest-sysml.lean
count=0
while IFS= read -r gen; do
  [ -n "$gen" ] || continue
  echo "checking $gen"
  lake env lean "$gen"
  count=$((count + 1))
done < "$generated"
if [ "$count" -ne "${#jsons[@]}" ]; then
  echo "ingest-sysml: expected ${#jsons[@]} generated module(s), checked $count" >&2
  exit 1
fi
