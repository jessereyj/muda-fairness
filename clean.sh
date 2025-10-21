#!/usr/bin/env bash
set -euo pipefail

echo "Cleaning build artifacts..."

# Remove Coq compiled files
find . \( -name "*.vo" -o -name "*.vok" -o -name "*.vos" \
          -o -name "*.glob" -o -name "*.aux" -o -name ".*.aux" \
          -o -name ".lia.cache" \) -type f -delete 2>/dev/null || true

# Remove generated makefiles
rm -f Makefile.coq Makefile.coq.conf .coqdeps.d 2>/dev/null || true

# Remove backup files
find . -name "*~" -type f -delete 2>/dev/null || true
find . -name "*.bak" -type f -delete 2>/dev/null || true

echo "✓ Clean complete."