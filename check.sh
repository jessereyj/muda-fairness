#!/usr/bin/env bash
set -euo pipefail

echo "================================================"
echo "  MUDA Fairness Verification - Proof Completeness Check"
echo "================================================"
echo ""

# Check for unfinished proofs.
# In this development, a proof left unfinished will appear as `Admitted.`.
# (Using `Abort.` would not compile; other tactics that leave goals open
# ultimately result in `Admitted.`.)

PATTERN='Admitted\.'

MATCHES="$(grep -RIn --exclude-dir=.git --include='*.v' -e "${PATTERN}" LTL MUDA Fairness Example 2>/dev/null || true)"

if [[ -z "${MATCHES}" ]]; then
  echo "[OK] No admitted lemmas found."
  exit 0
fi

echo "[FAIL] Found admitted lemmas (unfinished proofs):"
echo ""
echo "${MATCHES}"
exit 1
