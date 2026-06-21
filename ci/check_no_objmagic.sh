#!/usr/bin/env bash
# Fail if Obj.magic appears in extracted OCaml or our hand-written sources.
# (The only sanctioned home for a cast is one reviewed GADT-witness module, which does
#  not exist yet — see kb/architecture/decisions/adr-0004-trust-model.md.)
set -euo pipefail
cd "$(dirname "$0")/.."
dune build extraction/ >/dev/null 2>&1 || true
hits=$(grep -rln "Obj.magic" _build/default/extraction _build/default/generated codegen runtime support tests generated 2>/dev/null || true)
if [ -n "$hits" ]; then
  echo "FAIL: Obj.magic found in:"; echo "$hits"; exit 1
fi
echo "OK: no Obj.magic"
