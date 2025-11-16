#!/usr/bin/env bash
set -euo pipefail

echo "================================================"
echo "  Checking for Admitted Lemmas"
echo "================================================"
echo ""

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

# Check for Admitted
# Make this robust with 'set -euo pipefail' by allowing zero-match grep to succeed
ADMITS="$( (grep -rn "Admitted\." LTL/ MUDA/ Fairness/ Example/ 2>/dev/null || true) | wc -l | tr -d ' ' )"

if [[ ${ADMITS:-0} -eq 0 ]]; then
    echo -e "${GREEN}✓ SUCCESS${NC}: No admitted lemmas found!"
    echo "All proofs are complete."
    exit 0
else
    echo -e "${RED}✗ FAILURE${NC}: Found $ADMITS admitted lemma(s):"
    echo ""
    grep -rn "Admitted\." LTL/ MUDA/ Fairness/ Example/ 2>/dev/null || true
    echo ""
    echo -e "${YELLOW}Please complete these proofs before submission.${NC}"
    exit 1
fi