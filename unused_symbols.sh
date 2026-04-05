#!/usr/bin/env bash
set -euo pipefail

# Generate/refresh UNUSED_SYMBOLS.md (heuristic unused-symbol report).
# Output is written to the repository root.

python3 scripts/unused_symbols.py

echo "Wrote UNUSED_SYMBOLS.md"