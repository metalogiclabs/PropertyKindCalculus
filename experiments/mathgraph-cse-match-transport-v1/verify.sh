#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

lake build PropertyKindCalculus.Graph.Bisimulation
lake env lean \
  experiments/mathgraph-cse-match-transport-v1/CseMatchTransport.lean

lake build PropertyKindCalculus.Tests.Graph.Bisimulation

if rg -n '\b(sorry|admit|native_decide)\b' \
    experiments/mathgraph-cse-match-transport-v1/CseMatchTransport.lean; then
  echo "forbidden proof placeholder or native_decide found" >&2
  exit 1
fi
