# MUDA Fairness Verification

Temporal verification of fairness in the Multi-Unit Double Auction (MUDA) using Rocq and Linear Temporal Logic (LTL).

## Structure

```
LTL/       - Linear Temporal Logic foundation
MUDA/      - MUDA protocol model (state, sorting, matching, price)
Fairness/  - Fairness property formulas and proofs
Example/   - Chapter 5 Scenario 1 (executable trace checks)
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

Quantity fairness is evaluated over the MUDA execution trace using the Chapter 4
state predicates (math notation): residual conservation via `residualB(b)` and
the match record (i.e., `matched(b, s, q)` entries).

Proven for traces starting from initial states (as an invariant lifted to LTL).

### Priority Fairness

Priority fairness states that during matching, the selected feasible pair does
not skip any higher-priority feasible buyer/seller (using `feasible(b, s)` and
the priority orderings).

### Uniform Price Fairness

Uniform price fairness states that trades recorded in the match record are
priced consistently with the clearing price `price(x) = c` determined by MUDA.

Proven for traces starting from initial states.

See the Chapter 4 predicate notation mapping in [NOTATION.md](NOTATION.md) and
the corresponding Rocq definitions in [MUDA/State.v](MUDA/State.v).

## Verification Status

### Proof Completeness

- Lemmas and theorems closed with `Qed`, reported by `stats.sh`
- Admitted lemmas: **0**, enforced by `check.sh`
All fairness theorems are proven using `Qed`. No fairness proof uses `Admitted`.

This refactored version introduces no unproven postulates in the `.v` sources under `LTL/`, `MUDA/`, `Fairness/`, and `Example/`.

### Verification Commands

```bash
# Check for admitted lemmas
grep -rn "Admitted\." LTL/ MUDA/ Fairness/ Example/

# Show proof and definition statistics
./stats.sh
```

## Foundations

### Operational Invariants

MUDA invariants such as well-formed states, match persistence, and clearing price bounds are proven constructively in `MUDA/*` and lifted to LTL via atomic predicate interpretation.

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

## Module Notes

### Price Fairness

Defined in `Fairness/PriceFairness.v` as `priceOK`. The Chapter 5 executable trace checks are in `Example/Scenario1.v`.

### Fairness Export

`Fairness/All.v` re-exports all fairness properties for convenience.

## Future Work

- Add more Chapter 5 scenarios
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
