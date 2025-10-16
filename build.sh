#!/bin/sh
set -e

rm -f *.vo *.glob *.vok *.vos Makefile _CoqProject

cat > _CoqProject <<'EOF'
-Q . ""
Tactics.v
MudaCore.v
Sorting.v
Matching.v
ClearingPrice.v
PriorityFairness.v
QuantityFairness.v
Finality.v
Maximality.v
RejectionFairness.v
SimulationVerification.v
All.v
EOF

coq_makefile -f _CoqProject -o Makefile
make clean
make -j
