#!/usr/bin/env bash
# Fail if any proof is admitted or any new Axiom is declared (vernacular forms only,
# so doc comments mentioning the words don't trip it). The authoritative no-axiom
# guarantee is `Print Assumptions` -> "Closed under the global context" in the build log.
set -euo pipefail
cd "$(dirname "$0")/.."
if grep -rnE '(^|[[:space:]])(Axiom|Parameter|Hypothesis|Conjecture|Variable|Admitted)([[:space:]]|\.)|(^|[^[:alnum:]_])admit([^[:alnum:]_]|$)' theories/; then
  echo "FAIL: Admitted/admit/Axiom found in theories/"
  exit 1
fi
echo "OK: no Admitted/admit/Axiom in theories/"
