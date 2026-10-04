#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

lake build PropertyKindCalculus.Tests.Torch.TapeSeal
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
LEAN_PATH="$experiment_build:$lean_path" lean -o "$experiment_build/MatchInferenceCore.olean" \
  "$experiment_dir/MatchInferenceCore.lean"
LEAN_PATH="$experiment_build:$lean_path" lean \
  "$experiment_dir/MatchInferenceCoreTests.lean"
LEAN_PATH="$experiment_build:$lean_path" lean -o "$experiment_build/RecordedMatchInference.olean" \
  "$experiment_dir/RecordedMatchInference.lean"
LEAN_PATH="$experiment_build:$lean_path" lean \
  "$experiment_dir/RecordedMatchInferenceTests.lean"

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

automatic_manifest="$(mktemp)"
trap 'rm -f "$manifest" "$automatic_manifest"' EXIT
LEAN_PATH="$experiment_build:$lean_path" lean --run \
  "$experiment_dir/PkcMatchCertify.lean" > "$automatic_manifest"
rg -q '^matcher_policy: dependency-closure$' "$automatic_manifest"
rg -q '^status: CERTIFIED$' "$automatic_manifest"
rg -q '^match_equals_independent_control: true$' "$automatic_manifest"
rg -q '^source_match_accepted: true$' "$automatic_manifest"
cmp "$automatic_manifest" "$experiment_dir/AUTOMATIC_CERTIFICATION_MANIFEST.yml"

recording_manifest="$(mktemp)"
trap 'rm -f "$manifest" "$automatic_manifest" "$recording_manifest"' EXIT
LEAN_PATH="$experiment_build:$lean_path" lean --run \
  "$experiment_dir/PkcCertifyRecording.lean" > "$recording_manifest"
rg -q '^  status: INFERRED$' "$recording_manifest"
rg -q '^  warrant: WARRANTED_BOUNDED$' "$recording_manifest"
rg -q '^  status: OBLIGATIONS_REMAIN$' "$recording_manifest"
rg -q '^  explicit_recorder_scopes: REQUIRED_FOR_GENERAL_INTENDED_CALL_RECOVERY$' \
  "$recording_manifest"
cmp "$recording_manifest" "$experiment_dir/PKC_CERTIFY_RECORDING_MANIFEST.yml"

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
    experiments/mathgraph-cse-match-transport-v1/MatchInferenceCore.lean \
    experiments/mathgraph-cse-match-transport-v1/MatchInferenceCoreTests.lean \
    experiments/mathgraph-cse-match-transport-v1/PkcCertify.lean \
    experiments/mathgraph-cse-match-transport-v1/RecordedMatchInference.lean \
    experiments/mathgraph-cse-match-transport-v1/RecordedMatchInferenceTests.lean \
    experiments/mathgraph-cse-match-transport-v1/PkcMatchCertify.lean \
    experiments/mathgraph-cse-match-transport-v1/PkcCertifyRecording.lean; then
  echo "forbidden proof placeholder or native_decide found" >&2
  exit 1
fi
