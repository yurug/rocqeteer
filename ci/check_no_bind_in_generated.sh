#!/usr/bin/env bash
# Property P3: the generated fast code must contain no free-monad/Bind constructor.
set -euo pipefail
cd "$(dirname "$0")/.."
dune build generated/ >/dev/null 2>&1
gen=$(find _build/default/generated -name '*_generated.ml' 2>/dev/null || true)
if [ -z "$gen" ]; then echo "FAIL: no generated file found"; exit 1; fi
if grep -nE '\bBind\b|\bRet \(|\bProg\b|free.?monad' $gen; then
  echo "FAIL: free-monad construct in generated code"; exit 1
fi
echo "OK: generated code is direct-style (no Bind/free-monad) in: $gen"
