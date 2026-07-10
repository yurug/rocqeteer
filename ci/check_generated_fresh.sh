#!/usr/bin/env bash
# The committed generated file must equal a fresh codegen run (no hand-edits, no staleness).
set -eu
cd "$(dirname "$0")/.."
dune build generated/ >/dev/null 2>&1   # (mode promote) overwrites the source with fresh output
# Compare the source-tree file against the build artefact to detect hand-edits or staleness.
# (git diff is also run when the file is tracked, to give a readable diff on failure.)
genfile="generated/prog0_generated.ml"
buildfile="_build/default/generated/prog0_generated.ml"
if ! diff -q "$genfile" "$buildfile" >/dev/null 2>&1; then
  echo "FAIL: $genfile differs from a fresh codegen run (hand-edited or stale)."
  diff "$genfile" "$buildfile" | head -20
  exit 1
fi
echo "OK: generated file matches a fresh codegen run"
