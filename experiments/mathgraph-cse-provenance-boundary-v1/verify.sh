#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

lake build \
  PropertyKindCalculus.Torch.Paradigm.TapeCodegen \
  PropertyKindCalculus.Torch.Paradigm.TapeCse \
  PropertyKindCalculus.Graph.Bisimulation

lake env lean \
  experiments/mathgraph-cse-provenance-boundary-v1/CseProvenanceBoundary.lean

lake build \
  PropertyKindCalculus.Tests.Graph.Bisimulation \
  PropertyKindCalculus.Tests.Torch.TapeSeal

if rg -n '\b(sorry|admit|native_decide)\b' \
    experiments/mathgraph-cse-provenance-boundary-v1/CseProvenanceBoundary.lean; then
  echo "forbidden proof placeholder or native_decide found" >&2
  exit 1
fi
