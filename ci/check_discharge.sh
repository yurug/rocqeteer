#!/usr/bin/env bash
# ADR-0016 §5: every effect entry in the runtime manifest must name its discharge
# path — kernel-v1 (irreducible at this level) or derived(<Module.theorem>) — and
# every named discharge theorem must EXIST in theories/ (a dangling name would let
# the report claim a proof nobody wrote). The axiom-free-ness of the theorems is
# covered by check_no_admitted.sh + the Print Assumptions discipline.
set -eu
cd "$(dirname "$0")/.."
manifest="docs/runtime_manifest.toml"

fail=0

# 1. Every [effect."X"] block carries a discharge field.
effects=$(grep -n '^\[effect\.' "$manifest" | cut -d: -f1)
for line in $effects; do
  name=$(sed -n "${line}p" "$manifest")
  # block extends to the next section header or EOF
  next=$(awk -v s="$line" 'NR>s && /^\[/ {print NR; exit}' "$manifest")
  [ -z "$next" ] && next=$(($(wc -l < "$manifest") + 1))
  if ! sed -n "${line},$((next - 1))p" "$manifest" | grep -q '^discharge'; then
    echo "FAIL: $name has no discharge field (adr-0016 §5)"
    fail=1
  fi
done

# 2. Every derived(<Module.theorem>) names a theorem/corollary present in theories/.
thms=$(grep -o 'derived([A-Za-z0-9_]*\.[A-Za-z0-9_]*)' "$manifest" \
       | sed 's/derived(\(.*\))/\1/' | sort -u)
for t in $thms; do
  mod=${t%%.*}; thm=${t##*.}
  if [ ! -f "theories/${mod}.v" ]; then
    echo "FAIL: discharge theorem $t: theories/${mod}.v does not exist"
    fail=1
  elif ! grep -Eq "^(Theorem|Corollary|Lemma) ${thm}( |:)" "theories/${mod}.v"; then
    echo "FAIL: discharge theorem $t not found in theories/${mod}.v"
    fail=1
  fi
done

if [ "$fail" -ne 0 ]; then exit 1; fi
echo "OK: every effect entry names its discharge path; all derived theorems exist"
