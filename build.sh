#!/usr/bin/env bash
set -euo pipefail

# Clean only build artifacts, keep sources/_CoqProject
find . \( -name "*.aux" -o -name "*.vo" -o -name "*.vos" -o -name "*.vok" -o -name "*.glob" -o -name ".lia.cache" \) -type f -delete || true
rm -f Makefile Makefile.conf .Makefile.d || true

# Recreate _CoqProject (no 'theories/' prefixes, Sims→Cases)
cat > _CoqProject <<'EOF'
-R . MudaFairness

# Base utilities
Base/Prelude.v
Base/Tactics.v
Base/Finite.v

# Logic framework
#Logic/Semantics.v
#Logic/Hoare.v
#Logic/Meta/Consistency.v
#Logic/Meta/Soundness.v
#Logic/Meta/Completeness.v

# MUDA model
#Muda/Core.v
#Muda/Sorting.v
#Muda/Matching.v
#Muda/ClearingPrice.v
#Muda/Specs/MatchingSpec.v
#Muda/Specs/ClearingPriceSpec.v

# Core lemmas + fairness theorems
#Proofs/CoreLemmas.v
#Proofs/PriorityFairness.v
#Proofs/QuantityFairness.v
#Proofs/Finality.v
#Proofs/Maximality.v
#Proofs/RejectionFairness.v

# Scenarios (Cases)
#Cases/Scenarios.v
#Cases/Verification.v

# Aggregates
#Aggregates/MUDAProgram.v
#Aggregates/AllFairness.v
#Aggregates/All.v
EOF

# Generate Makefile and build
coq_makefile -f _CoqProject -o Makefile

# Use available cores if possible
NPROC="$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 2)"
make -j"$NPROC"
