# MUDA Fairness Verification

Temporal verification of fairness in the Multi-Unit Double Auction (MUDA) using Rocq and Linear Temporal Logic (LTL).

If you’re looking for thesis defense/study notes (internal), see [docs/README.md](docs/README.md).

## Structure

```
LTL/       - Linear Temporal Logic foundation
MUDA/      - MUDA protocol model (state, sorting, matching, price)
Fairness/  - Fairness property formulas and proofs
Example/   - Cloud market scenarios that exercise the definitions and fairness theorems
```

## Docs

- Internal defense pack: [docs/README.md](docs/README.md)
- Text extraction of the thesis (for search/alignment): [docs/thesis.txt](docs/thesis.txt)
- Exact trusted assumptions inventory: [docs/TRUSTED_ASSUMPTIONS.md](docs/TRUSTED_ASSUMPTIONS.md)

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

- **Rocq** 9.1.0 or compatible
- **Bash** for build scripts

## Build Process

The `build.sh` script performs the following steps:

1. Cleans old build artifacts
2. Verifies directory structure
3. Generates `_CoqProject`
4. Creates a minimal `Makefile.rocq`
5. Builds the project using `rocq compile` with parallel jobs
6. Runs a check to ensure no admitted lemmas remain

## Statistics

Run `./stats.sh` to report:

- Number of files per module
- Lines of code
- Definitions and inductive objects
- Theorem and lemma declarations
- Admitted lemmas

## Verification Results (high level)

### Quantity Fairness

`quantityOK := G (Atom p_allocOK)`

Proven for traces starting from initial states.

### Priority Fairness

`priorityOK := G (Atom p_prioB_step) ∧ G (Atom p_prioS_step)`

### Uniform Price Fairness

`priceOK := G (Atom p_has_cprice → (Atom p_bounds_cstar ∧ Atom p_price_rule))`

Proven for traces starting from initial states.

Note: `p_has_cprice` reflects whether a clearing price exists (i.e., `Some _`). The implication form ensures no-trade executions are not excluded; the bound/rule atoms are also totalized to remain well-defined when no marginal pair exists.

### Match Finality

`finalityOK := G (Atom p_match_keep)`

### Maximality

Post-matching invariant form (Chapter 5):

`phase_ge_4 := Atom (p_phase 4) ∨ Atom (p_phase 5) ∨ Atom (p_phase 6) ∨ Atom (p_phase 7)`

`maximal := G (phase_ge_4 → Atom p_no_feasible)`

### Justified Rejection

`rejectionOK := G (phase_ge_4 → Atom p_rejection_justified)`

See `Fairness/JustifiedRejection.v`.

## Verification Status

### Proof Completeness

- Lemmas and theorems closed with `Qed`, reported by `stats.sh`
- Admitted lemmas: **0**, enforced by `check.sh`
- Axioms and parameters, reported by `stats.sh`

All fairness theorems are proven using `Qed`. No fairness proof uses `Admitted`.

Fairness verification uses semantic satisfaction over traces and relies on LTL soundness only. Completeness axioms are present for the meta-theory and are not required by fairness proofs.

### Axiomatized Components

The development makes a small number of explicit axiomatic assumptions. These are documented and separated from admitted proofs.

#### LTL Meta-Theory

- Propositional tautologies as a meta-axiom schema
- Canonical model construction
- Weak completeness of LTL with X and U (derived from the canonical-countermodel assumption)

These are standard results adopted from the LTL literature. Fairness proofs depend only on soundness (proved modulo the standard propositional meta-assumption `A0_valid`).

#### MUDA Sorting

- Correctness of lexicographic bid sorting
- Correctness of lexicographic ask sorting

These formalize standard sorting properties. They could be discharged using Coq's verified sorting libraries. They are axiomatized to keep the focus on temporal verification.

#### Greedy Matching Priority

- Greedy matching respects bid priority ordering
- Greedy matching respects ask priority ordering

These follow from sorting correctness by construction. The greedy algorithm scans sorted lists in order.

### Theorem Dependencies

| Fairness Property | Depends on MUDA Axioms | Depends on LTL Meta-Axioms | Admitted |
|-------------------|------------------------|----------------------------|----------|
| Priority Fairness | Yes | No | 0 |
| Quantity Fairness | Yes | No | 0 |
| Price Fairness | Yes | No | 0 |
| Match Finality | Yes | No | 0 |
| Maximality | Yes | No | 0 |
| Justified Rejection | Yes | No | 0 |

Notes:

- The fairness proofs are semantic (they prove `satisfies ...`) and do not use the LTL meta-theory axioms (e.g., `WeakCompleteness`).
- All fairness theorems depend on the axiomatized sorting functions `sort_bids`/`sort_asks` because they are used by the MUDA transition function (`step`).
- Priority fairness additionally depends on the greedy-priority axioms (`greedy_respects_priority_bids` and `greedy_respects_priority_asks`).

**Summary:**

- All fairness theorems depend on the sorting-function axioms (`sort_bids`, `sort_asks`)
- Priority fairness additionally depends on greedy priority assumptions
- All fairness theorems are proven with `Qed` and use no `Admitted`

### Comparison to Standard Practice

Axiomatizing well-known components is common in formal verification. This allows verification effort to focus on novel properties rather than re-proving standard algorithms.

This work follows the same approach by isolating sorting and greedy correctness as explicit assumptions.

### Verification Commands

```bash
# Check for admitted lemmas
grep -rn "Admitted\." LTL/ MUDA/ Fairness/ Example/

# List axioms and parameters
grep -rn "Axiom\|Parameter" LTL/ MUDA/ Fairness/

# Show proof and definition statistics
./stats.sh
```

## Assumptions and Foundations

### Axiomatic LTL Core

The project uses a Hilbert-style axiomatic foundation for LTL. Fairness proofs reason over semantic satisfaction on traces and do not mix derivability judgments.

### Operational Invariants

MUDA invariants such as well-formed states, match persistence, and clearing price bounds are proven constructively in `MUDA/*` and lifted to LTL via atomic predicate interpretation.

### Remaining MUDA Axioms

Sorting and greedy priority properties are axiomatized for build stability and scope control. Fairness results depend on these assumptions, which are explicit and documented.

## Thesis-to-Code Mapping

The thesis presents a mathematical model focused on economically relevant components. The Rocq implementation includes additional bookkeeping required for mechanical verification.

### State

- **Thesis:** `x = (B, S, orders, residuals, M, p*, phase)`
- **Code:** `State = (bids, asks, matches, clearing_price, phase)`

Residuals are computed dynamically using `residual_bid` and `residual_ask`.

### Bids and Asks

- **Thesis:** Uses 3-tuple notation `(price, quantity, time)`
- **Code:** Uses records with identifiers and agent ownership for traceability

### Matches

- **Thesis:** Uses `(b, s, q)` triples
- **Code:** Stores full bid and ask records with quantities

### Allocation

- **Thesis:** Presents abstract allocation functions
- **Code:** Uses recursive functions with decidable equality

### Traces

- **Thesis:** Describes infinite executions conceptually
- **Code:** Uses a coinductive trace construction via `mu_trace`

This abstraction pattern is standard in formal verification. The mathematical model emphasizes logic. The implementation handles mechanical details.

**Note (Chapter 5 narrative):** The mechanization advances deterministically through phases `P4 → P5 → P6 → P7`,
and then stutters forever at `P7` (because `step` is the identity in `P7`). If the thesis text informally describes
“repeating xhalt at P4”, the mechanically precise reading is “we remain in the post-matching region forever”, which
this development captures using the guard `phase_ge_4` (i.e., `P4`–`P7`).

## Module Notes

### Price Fairness

Defined in `Fairness/PriceFairness.v` as `priceOK`. Examples in `Example/CloudMarket.v` exercise the property from initial states.

### Fairness Export

`Fairness/All.v` re-exports all fairness properties for convenience.

## Future Work

- Replace sorting and greedy priority axioms with constructive proofs
- Add a phase-guarded price fairness variant if needed
- Reduce example imports to the minimal LTL modules

## Development Workflow

### Edit a file

```bash
vim MUDA/State.v
```

### Compile a single file

```bash
rocq compile -R LTL LTL -R MUDA MUDA -R Fairness Fairness MUDA/State.v
```

### Full rebuild

```bash
./build.sh
```

### Watch mode

```bash
./watch.sh
```

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.
