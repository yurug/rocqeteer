#!/usr/bin/env bash
# Regenerate the TCB report and assert its key invariants; fail on silent TCB drift.
#
# The toolchain block records the versions of the switch that produced the
# committed report. It is informational: a contributor on a different Rocq or
# OCaml point release must not see a red gate for that reason alone. Everything
# else in the report is compared strictly, because that is where trust lives:
# assumptions, admits, Obj.magic budget, realizers, discharge paths, gates.
set -eu
cd "$(dirname "$0")/.."
./ci/gen_tcb_report.sh >/dev/null
grep -q "Closed under the global context" docs/tcb_report.md || { echo "FAIL: incr_correct is not axiom-free"; exit 1; }
grep -qE "Obj.magic.*\*\*0\*\*" docs/tcb_report.md || { echo "FAIL: Obj.magic budget (0) exceeded"; exit 1; }

# Strip the three toolchain lines from both sides before comparing.
strip_toolchain() { grep -vE '^- (Rocq|OCaml|dune): ' "$1"; }

if git ls-files --error-unmatch docs/tcb_report.md >/dev/null 2>&1; then
  committed=$(mktemp) ; regenerated=$(mktemp)
  trap 'rm -f "$committed" "$regenerated"' EXIT
  git show HEAD:docs/tcb_report.md > "$committed"
  cp docs/tcb_report.md "$regenerated"
  if ! diff -q <(strip_toolchain "$committed") <(strip_toolchain "$regenerated") >/dev/null; then
    echo "FAIL: tcb_report.md changed — review the TCB drift and commit"
    diff -u <(strip_toolchain "$committed") <(strip_toolchain "$regenerated") | head -30
    exit 1
  fi
  # Only the toolchain block moved: keep the committed report, and say so.
  if ! git diff --quiet -- docs/tcb_report.md; then
    git checkout -- docs/tcb_report.md
    echo "note: local toolchain differs from the one that generated the committed report"
    echo "      (run 'make tcb-report' and commit if this machine is the reference)"
  fi
fi
echo "OK: TCB report regenerated; invariants hold; no drift"
