#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

lake build PropertyKindCalculus.Graph.Bisimulation
experiment_dir="$repo_root/experiments/mathgraph-cse-match-transport-v1"
experiment_build="$repo_root/.lake/build/mathgraph-experiments"
mkdir -p "$experiment_build"
lake env lean -o "$experiment_build/CseMatchTransport.olean" \
  "$experiment_dir/CseMatchTransport.lean"
lean_path="$(lake env printenv LEAN_PATH)"
LEAN_PATH="$experiment_build:$lean_path" lean -o "$experiment_build/CseQuotientChecker.olean" \
  "$experiment_dir/CseQuotientChecker.lean"
LEAN_PATH="$experiment_build:$lean_path" lean -o "$experiment_build/RecordedCseQualification.olean" \
  "$experiment_dir/RecordedCseQualification.lean"
LEAN_PATH="$experiment_build:$lean_path" lean -o "$experiment_build/CertifiedCseGate.olean" \
  "$experiment_dir/CertifiedCseGate.lean"
LEAN_PATH="$experiment_build:$lean_path" lean -o "$experiment_build/CertifiedCseControls.olean" \
  "$experiment_dir/CertifiedCseControls.lean"

manifest="$(mktemp)"
trap 'rm -f "$manifest"' EXIT
LEAN_PATH="$experiment_build:$lean_path" lean --run \
  "$experiment_dir/PkcCertify.lean" all > "$manifest"
rg -q '^scenario: worked-model$' "$manifest"
rg -q '^status: CERTIFIED$' "$manifest"
rg -q '^raw_vertices: 18$' "$manifest"
rg -q '^compacted_vertices: 14$' "$manifest"
rg -q '^failed_clauses: \["component-ownership", "component-multiplicity"\]$' "$manifest"
rg -q '^failed_clauses: \["source-match-acceptance", "leaves-are-sources"\]$' "$manifest"
cmp "$manifest" "$experiment_dir/CERTIFICATION_MANIFEST.yml"

lake build PropertyKindCalculus.Tests.Graph.Bisimulation

# Replay the preceding executable CSE controls that produced the remap used by the
# lawful-sharing and distinct-source graph theorems in this qualification.
lake build PropertyKindCalculus.Torch.Paradigm.TapeCse
lake build PropertyKindCalculus.Torch.Paradigm.TapeCodegen
lake env lean \
  experiments/mathgraph-cse-provenance-boundary-v1/CseProvenanceBoundary.lean

if rg -n '\b(sorry|admit|native_decide)\b' \
    experiments/mathgraph-cse-match-transport-v1/CseMatchTransport.lean \
    experiments/mathgraph-cse-match-transport-v1/CseQuotientChecker.lean \
    experiments/mathgraph-cse-match-transport-v1/RecordedCseQualification.lean \
    experiments/mathgraph-cse-match-transport-v1/CertifiedCseGate.lean \
    experiments/mathgraph-cse-match-transport-v1/CertifiedCseControls.lean \
    experiments/mathgraph-cse-match-transport-v1/PkcCertify.lean; then
  echo "forbidden proof placeholder or native_decide found" >&2
  exit 1
fi
