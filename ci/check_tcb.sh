#!/usr/bin/env bash
# Regenerate the TCB report and assert its key invariants; fail on silent TCB drift.
set -eu
cd "$(dirname "$0")/.."
./ci/gen_tcb_report.sh >/dev/null
grep -q "Closed under the global context" docs/tcb_report.md || { echo "FAIL: incr_correct is not axiom-free"; exit 1; }
grep -qE "Obj.magic.*\*\*0\*\*" docs/tcb_report.md || { echo "FAIL: Obj.magic budget (0) exceeded"; exit 1; }
if git ls-files --error-unmatch docs/tcb_report.md >/dev/null 2>&1; then
  if ! git diff --quiet -- docs/tcb_report.md; then
    echo "FAIL: tcb_report.md changed — review the TCB drift and commit"
    git --no-pager diff -- docs/tcb_report.md | head -30
    exit 1
  fi
fi
echo "OK: TCB report regenerated; invariants hold; no drift"
