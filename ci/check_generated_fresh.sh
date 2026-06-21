#!/usr/bin/env bash
# The committed generated file must equal a fresh codegen run (no hand-edits, no staleness).
set -eu
cd "$(dirname "$0")/.."
dune build generated/ >/dev/null 2>&1   # (mode promote) overwrites the source with fresh output
if git ls-files --error-unmatch generated/prog0_generated.ml >/dev/null 2>&1; then
  if ! git diff --quiet -- generated/prog0_generated.ml; then
    echo "FAIL: generated/prog0_generated.ml differs from a fresh codegen run (hand-edited or stale)."
    git --no-pager diff -- generated/prog0_generated.ml | head -20
    exit 1
  fi
fi
echo "OK: generated file matches a fresh codegen run"
