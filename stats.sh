#!/usr/bin/env bash
set -euo pipefail

echo "================================================"
echo "  MUDA Fairness Verification - Statistics"
echo "================================================"
echo ""

# Count files
LTL_FILES=$(find LTL -name "*.v" 2>/dev/null | wc -l | tr -d ' ')
MUDA_FILES=$(find MUDA -name "*.v" 2>/dev/null | wc -l | tr -d ' ')
FAIRNESS_FILES=$(find Fairness -name "*.v" 2>/dev/null | wc -l | tr -d ' ')
TOTAL_FILES=$((LTL_FILES + MUDA_FILES + FAIRNESS_FILES))

echo "Files:"
echo "  LTL:      $LTL_FILES"
echo "  MUDA:     $MUDA_FILES"
echo "  Fairness: $FAIRNESS_FILES"
echo "  Total:    $TOTAL_FILES"
echo ""

# Count lines of code
LTL_LOC=$(find LTL -name "*.v" -exec cat {} \; 2>/dev/null | wc -l | tr -d ' ')
MUDA_LOC=$(find MUDA -name "*.v" -exec cat {} \; 2>/dev/null | wc -l | tr -d ' ')
FAIRNESS_LOC=$(find Fairness -name "*.v" -exec cat {} \; 2>/dev/null | wc -l | tr -d ' ')
TOTAL_LOC=$((LTL_LOC + MUDA_LOC + FAIRNESS_LOC))

echo "Lines of Code:"
echo "  LTL:      $LTL_LOC"
echo "  MUDA:     $MUDA_LOC"
echo "  Fairness: $FAIRNESS_LOC"
echo "  Total:    $TOTAL_LOC"
echo ""

# Count theorems
THEOREMS=$(grep -rh "^Theorem\|^Lemma\|^Corollary" LTL/ MUDA/ Fairness/ 2>/dev/null | wc -l | tr -d ' ')
echo "Theorems/Lemmas: $THEOREMS"
echo ""

# Count admitted
ADMITS=$(grep -r "Admitted\." LTL/ MUDA/ Fairness/ 2>/dev/null | wc -l | tr -d ' ')
echo "Admitted lemmas: $ADMITS"
echo ""

# Count definitions
DEFS=$(grep -rh "^Definition\|^Fixpoint\|^Inductive\|^Record" LTL/ MUDA/ Fairness/ 2>/dev/null | wc -l | tr -d ' ')
echo "Definitions: $DEFS"
echo ""

echo "================================================"