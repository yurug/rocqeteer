#!/usr/bin/env bash
# Effect.perform may appear only in runtime/ (the realizer modules), never in codegen,
# tests, support, or generated code (which must call the curried wrappers).
set -euo pipefail
cd "$(dirname "$0")/.."
hits=$(grep -rln "Effect.perform" codegen support tests generated 2>/dev/null || true)
if [ -n "$hits" ]; then
  echo "FAIL: raw Effect.perform outside runtime/ in:"; echo "$hits"; exit 1
fi
echo "OK: Effect.perform confined to runtime/"
