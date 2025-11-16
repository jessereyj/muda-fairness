# MUDA Fairness Verification

Formal verification of fairness properties in Multi-Unit Double Auction (MUDA) using Rocq/Coq and Linear Temporal Logic (LTL).

## Structure
```
LTL/       - Linear Temporal Logic foundation
MUDA/      - MUDA protocol model (state, sorting, matching, price)
Fairness/  - Fairness property formulas and proofs
Example/   - Cloud market scenarios exercising the proofs
```

## Quick Start

### Build everything
```bash
./build.sh
```

### Clean build artifacts
```bash
./clean.sh
```

### Check for admitted lemmas
```bash
./check.sh
```

### Show project statistics
```bash
./stats.sh
```

## Requirements

- **Rocq:** 9.1.0 (or compatible)
- **Bash:** For build scripts

## Build Process

The `build.sh` script:
1. Cleans old artifacts
2. Verifies directory structure
3. Generates `_CoqProject`
4. Creates a minimal `Makefile.rocq`
5. Builds with parallel jobs using `rocq compile`
6. Checks for admitted lemmas

## Statistics

Run `./stats.sh` to see up-to-date counts of files, lines, definitions, and admitted lemmas.

## Verification Results (high level)

- Quantity Fairness: `quantityOK := G (Atom p_allocOK)` — proven for traces from initial states
- Priority Fairness: `priorityOK := (G (Atom p_prioB_step)) ∧ (G (Atom p_prioS_step))`
- Uniform Price Fairness: `uniformPriceOK := G (Atom p_bounds_cstar)` — proven for traces from initial states
- Match Finality: `finalityOK := G (Atom p_match_keep)`
- Maximality: `maximal := F (Atom (p_phase 4) ∧ Atom p_no_feasible)`
- Rejection Fairness: `rejectionOK` (see `Fairness/RejectionFairness.v`)

## Development Workflow

### Edit a file
```bash
vim MUDA/State.v
```

### Compile just that file (optional)
```bash
rocq compile -R LTL LTL -R MUDA MUDA -R Fairness Fairness MUDA/State.v
```

### Full rebuild
```bash
./build.sh
```

### Watch mode (auto-rebuild)
```bash
./watch.sh
```

## License

MIT License