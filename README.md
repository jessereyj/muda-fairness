# MUDA Fairness Verification

Temporal verification of fairness in the Multi-Unit Double Auction (MUDA) using Rocq and Linear Temporal Logic (LTL).

## Structure

```
LTL/       - Linear Temporal Logic foundation
MUDA/      - MUDA protocol model (state, sorting, matching, price)
Fairness/  - Fairness property formulas and proofs
Example/   - Concrete scenario(s) and end-to-end checks (Scenario 1)
html/      - Generated browsing documentation (coqdoc output)
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
state predicates (math notation): residual conservation via the residual functions
(`residual_bid`/`residual_ask` over the match record) and the match record entries.

Proven for traces starting from initial states (as an invariant lifted to LTL).

### Priority Fairness

Priority fairness states that during matching, the selected feasible pair does
not skip any higher-priority feasible buyer/seller (using `feasible(b, s)` and
the priority orderings).

### Uniform Price Fairness

Uniform price fairness states that trades recorded in the match record are
priced consistently with the clearing price carried by the state (i.e.,
`clearing_price(x) = Some c`) as determined by MUDA.

Proven for traces starting from initial states.

See the Chapter 4 predicate notation mapping in [NOTATION.md](NOTATION.md) and
the corresponding Rocq definitions in [MUDA/State.v](MUDA/State.v).

## Thesis questions answered (where in the code)

1) **How can MUDA execution be formalized as a deterministic STS?**
- State space: `State` in [MUDA/State.v](MUDA/State.v)
- Deterministic transition function: `δ : State -> State` in [MUDA/Transitions.v](MUDA/Transitions.v)
- Finite execution: `execute n s` (iterate `δ`) in [MUDA/Transitions.v](MUDA/Transitions.v)
- Infinite trace for LTL: `mu_trace` (coinductively iterating `δ`) in [Fairness/Interpretation.v](Fairness/Interpretation.v)

2) **Which temporal operators are sufficient to express fairness properties over MUDA traces?**
- The development uses the Chapter 4 core temporal operators `X`, `F`, `G` (see [LTL/Syntax.v](LTL/Syntax.v) and [LTL/Semantics.v](LTL/Semantics.v)).
- The three fairness properties in this repo are expressed as invariants, so `G` (plus propositional connectives) is sufficient for them:
	- Priority: `G(p_prioB_step) ∧ G(p_prioS_step)` in [Fairness/PriorityFairness.v](Fairness/PriorityFairness.v)
	- Quantity: `G(p_allocOK)` in [Fairness/QuantityFairness.v](Fairness/QuantityFairness.v)
		- Price: `G(p_has_cprice → (p_bounds_pstar ∧ p_price_rule))` in [Fairness/PriceFairness.v](Fairness/PriceFairness.v)

3) **Can all three fairness properties be verified using Rocq?**
- Yes. Each property is proven for MUDA traces from initial states:
	- Priority: `priority_fairness_LTL_initial` in [Fairness/PriorityFairness.v](Fairness/PriorityFairness.v)
	- Quantity: `quantity_fairness_LTL_initial` in [Fairness/QuantityFairness.v](Fairness/QuantityFairness.v)
	- Price: `uniform_price_fairness_LTL_initial` in [Fairness/PriceFairness.v](Fairness/PriceFairness.v)
- The build/check scripts enforce that no proofs are left unfinished (see `./check.sh`).

## Verification Status

### Proof Completeness

- Lemmas and theorems closed with `Qed`, reported by `stats.sh`
- Admitted lemmas: **0**, enforced by `check.sh`
All fairness theorems are proven using `Qed`. No fairness proof uses `Admitted`.

This refactored version contains no admitted proofs in the `.v` sources under `LTL/`, `MUDA/`, `Fairness/`, and `Example/`.

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
Concrete example executions and checks are in `Example/`.

### Bids and Asks

- **Thesis:** Uses 3-tuple notation `(price, quantity, time)`
- **Code:** Uses records with identifiers and agent ownership for traceability

### Matches

- **Thesis:** Uses `(b, s, q)` triples
- **Code:** Stores full bid and ask records with quantities

- **Thesis:** Presents abstract allocation functions
- **Code:** Uses recursive functions with decidable equality

### Traces

- **Thesis:** Describes infinite executions conceptually
- **Code:** Uses a coinductive trace construction via `mu_trace`

This abstraction pattern is standard in formal verification. The mathematical model emphasizes logic. The implementation handles mechanical details.

## Module Notes

### Price Fairness

Defined in `Fairness/PriceFairness.v` as `priceOK`.

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
