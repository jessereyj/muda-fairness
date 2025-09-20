#!/bin/sh
set -e

cat > _CoqProject <<'EOF'
-Q . ""
Tactics.v
MudaCore.v
Sorting.v
Matching.v
ClearingPrice.v
Temporal.v
PriorityFairness.v
QuantityFairness.v
Finality.v
Maximality.v
RejectionFairness.v
All.v
EOF

coq_makefile -f _CoqProject -o Makefile
make clean
make -j
