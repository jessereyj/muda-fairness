# MUDA Fairness Verification

Temporal verification of fairness in Multi-Unit Double Auction (MUDA) using Rocq/Coq and Linear Temporal Logic (LTL).

## Structure
```
LTL/       - Linear Temporal Logic foundation
MUDA/      - MUDA protocol model (state, sorting, matching, price)
Fairness/  - Fairness property formulas and proofs
Example/   - Validate the logical soundness and completeness. Cloud market scenarios exercising the proofs
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
- Uniform Price Fairness: `priceOK := G (Atom p_bounds_cstar) ∧ G((phase≥4) → Atom p_has_cprice) ∧ G (Atom p_price_rule)` — proven for traces from initial states
- Match Finality: `finalityOK := G (Atom p_match_keep)`
- Maximality: `maximal := F (Atom (p_phase 4) ∧ Atom p_no_feasible)`
- Rejection Fairness: `rejectionOK` (see `Fairness/JustifiedRejection.v`)

## Assumptions & Foundations

- **Axiomatic LTL Core:** The project retains a Hilbert-style axiomatic foundation for LTL. Files `LTL/Axioms.v`, `LTL/Soundness.v`, and `LTL/Completeness.v` are available and registered; examples and fairness proofs use semantic satisfaction (`satisfies`) over traces and do not mix derivability judgments.
- **Operational Invariants:** MUDA invariants (e.g., `wf_state`, match persistence, clearing price bounds) are proved constructively in `MUDA/*` and lifted to LTL via the interpretation of atomic predicates.
- **Remaining MUDA Axioms:** Some protocol properties are currently axiomatized for build stability:
	- Sorting bridges between strong sortedness and index-based priority
	- Greedy priority respect lemmas for bids/asks
	Fairness results depend on these axioms; constructive replacements are planned.

## Module Notes

- **Price Fairness:** Consolidated in `Fairness/PriceFairness.v` as `priceOK := G (Atom p_bounds_cstar) ∧ G((phase≥4) → Atom p_has_cprice) ∧ G (Atom p_price_rule)`. Examples in `Example/CloudMarket.v` use `priceOK` and the theorem `uniform_price_fairness_LTL_initial`.
- **Fairness Export:** `Fairness/All.v` re-exports `Interpretation`, `PriorityFairness`, `QuantityFairness`, `PriceFairness`, `MatchFinality`, `Maximality`, and `JustifiedRejection` for convenience.

## Future Work

- Replace sorting and greedy priority axioms with constructive proofs and update fairness theorems accordingly.
- Optional: add a phase-guarded price fairness variant (only required from `P4` onward) and prove it from initial states.
- Trim example imports to the minimal needed LTL modules (e.g., `Syntax`, `Semantics`, `LTL`) while keeping axioms available.

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
