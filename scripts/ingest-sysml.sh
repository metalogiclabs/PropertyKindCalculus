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
PKC_INGEST="$(IFS=,; echo "${jsons[*]}")" lake env lean scripts/ingest-sysml.lean
for model in "$@"; do
  pkg="$(basename "$model" .sysml)"
  gen="$(ls .lake/build/sysml/Generated/*.lean | grep -i "$(echo "$pkg" | tr -cd '[:alnum:]_')" | head -1 || true)"
  [ -n "$gen" ] || continue
  echo "checking $gen"
  lake env lean "$gen"
done
