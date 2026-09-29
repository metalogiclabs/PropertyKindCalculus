#!/usr/bin/env bash
# Regenerate the blueprint's hand-authored schematics — figures/*.svg — from the
# generators under scripts/figures/, or, with --check, verify that the committed SVGs
# are what the generators emit, so a generator edit cannot land without its figure.
#
#   scripts/make-figures.sh            # rewrite figures/*.svg
#   scripts/make-figures.sh --check    # exit 1 and name each figure that differs
#
# The figures are read into `PropertyKindCalculusBlueprint/Figures.lean` by `include_str`
# at compile time, and Lake's trace does not see that file dependency: a regenerated
# figure alone does not rebuild the module. So after writing a figure that changed, this
# script removes the module's build products, and the next `lake build` rebuilds it and
# every chapter that inlines a figure.
#
# The deck's copies (research-presentations) are not covered here: regenerate them with
# each generator's `--out`, and the cake's with `--audience deck` (its docstring says why
# the two audiences differ).
#
# The generators use only the standard library, so any Python 3 will do; when none is
# found the script says so and exits 0, as ci-pages.sh does for its own Python pass.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # blueprint/
GEN="$ROOT/scripts/figures"
FIG="$ROOT/figures"
FIGURES_MODULE="$ROOT/.lake/build/lib/lean/PropertyKindCalculusBlueprint/Figures"

py_works() { "$@" -c 'import sys; raise SystemExit(0 if sys.version_info[0] == 3 else 1)' \
               >/dev/null 2>&1; }
PY=""
for c in python3 python; do
  if command -v "$c" >/dev/null 2>&1 && py_works "$c"; then PY="$c"; break; fi
done
if [ -z "$PY" ]; then
  echo "note: no Python 3 found — figures/*.svg left as committed, not regenerated or checked" >&2
  exit 0
fi

# generator -> figure, one line each
GENERATORS=(
  "make-architecture-cake.py architecture-cake.svg"
  "make-lowe-square-pkc.py lowe-square-pkc.svg"
  "make-three-layers-pkc.py three-layers-pkc.svg"
)

MODE="${1:-write}"
case "$MODE" in
  write|--check) ;;
  *) echo "usage: make-figures.sh [--check]" >&2; exit 2 ;;
esac

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

changed=0
for entry in "${GENERATORS[@]}"; do
  read -r gen fig <<<"$entry"
  "$PY" "$GEN/$gen" --out "$TMP/$fig" >/dev/null
  if [ -f "$FIG/$fig" ] && cmp -s "$TMP/$fig" "$FIG/$fig"; then
    echo "  unchanged  figures/$fig"
    continue
  fi
  changed=$((changed + 1))
  if [ "$MODE" = "--check" ]; then
    echo "  DIFFERS    figures/$fig  (run scripts/make-figures.sh and commit the result)"
  else
    cp "$TMP/$fig" "$FIG/$fig"
    echo "  rewritten  figures/$fig  ($(stat -c %s "$FIG/$fig") bytes)"
  fi
done

if [ "$MODE" = "--check" ]; then
  if [ "$changed" -gt 0 ]; then
    echo "error: $changed figure(s) differ from their generators" >&2
    exit 1
  fi
  echo "figures: all $((${#GENERATORS[@]})) match their generators"
  exit 0
fi

if [ "$changed" -gt 0 ]; then
  rm -f "$FIGURES_MODULE".* "$FIGURES_MODULE"/*.* 2>/dev/null || true
  echo "$changed figure(s) rewritten; Figures.lean build products removed so the next lake build re-reads them"
fi
