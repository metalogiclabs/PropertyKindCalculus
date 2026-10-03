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
LEAN_PATH="$experiment_build:$lean_path" lean \
  "$experiment_dir/RecordedCseQualification.lean"

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
    experiments/mathgraph-cse-match-transport-v1/RecordedCseQualification.lean; then
  echo "forbidden proof placeholder or native_decide found" >&2
  exit 1
fi
