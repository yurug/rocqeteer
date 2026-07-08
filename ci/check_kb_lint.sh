#!/usr/bin/env bash
# Mechanical KB validation: frontmatter, required keys, closed type set, valid dates,
# no duplicate ids, links + id-refs resolve, files <= 200 lines, INDEX coverage, no
# orphans. Vendored kb-lint.py (from agentic-dev-kit). --no-git keeps it stable in fresh
# clones / CI (date-staleness is a local-editing concern, not a build gate).
set -eu
cd "$(dirname "$0")/.."
python3 ci/kb-lint.py kb --strict --no-git
