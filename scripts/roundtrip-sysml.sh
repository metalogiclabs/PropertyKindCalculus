#!/usr/bin/env bash
# Lean → SysML → Lean, checked by content: harvest the ISO 80000-3 catalogue and the
# harmonic-oscillator tutorial, emit them in the PKC DSL, validate and convert them with
# OpenSysML, read the element form back, and compare with the harvest.
#
# Needs OpenSysML's `sysml` on PATH (or SYSML=/path/to/sysml) and
# `lake build Interchange Iso80000 Tutorial`.
set -euo pipefail
cd "$(dirname "$0")/.."
SYSML="${SYSML:-sysml}"
lake env lean scripts/emit-sysml.lean
for pkg in PKC_ISO80000_3 HarmonicOscillatorRequirements; do
  "$SYSML" -validate sysml/PKC.sysml ".lake/build/sysml/$pkg.sysml"
  "$SYSML" -convert api-json sysml/PKC.sysml ".lake/build/sysml/$pkg.sysml" > ".lake/build/sysml/$pkg.api.json"
done
lake env lean scripts/roundtrip-sysml.lean
