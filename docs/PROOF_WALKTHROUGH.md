# Line-by-line Rocq Proof Walkthrough Guide

Goal: be able to explain *every major definition* and *why each fairness theorem is true* by following the proof scripts.

## How to read proofs efficiently
- Start by finding the **top-level theorem** in the file.
- Then identify:
  1) the **state-level predicate** being proved (often defined in `MUDA/Atoms.v`),
  2) the **LTL formula** (usually `G (...)`),
  3) the **bridge lemma** that lifts state predicates to trace satisfaction (in `Fairness/Interpretation.v`),
  4) any **phase case splits** (`P1`..`P7`) and post-matching guard (`phase_ge_4`).

## File-by-file walkthrough order

### 1) The trace bridge
- Read: [Fairness/Interpretation.v](../../Fairness/Interpretation.v)
- What to extract:
  - Atom numbering scheme (which nat corresponds to which predicate)
  - `mu_trace` definition (turning `step` into an infinite trace)
  - Lemmas connecting `execute`/iteration of `step` to `trace_at`
  - Key lemmas: `mu_trace_at_execute`, `mu_trace_atom_at_execute`

### 2) Quantity Fairness (warm-up invariant)
- Read: [Fairness/QuantityFairness.v](../../Fairness/QuantityFairness.v)
- Focus questions:
  - What exactly is `p_allocOK` asserting about residuals/allocations?
  - Which lemma shows it holds after each `step`?
  - How is it lifted to `G (Atom p_allocOK)` over `mu_trace`?

Concrete targets to find:
- `Definition quantityOK`
- `Theorem quantity_fairness_step`
- `Theorem quantity_fairness_LTL_initial`

### 3) Match Finality
- Read: [Fairness/MatchFinality.v](../../Fairness/MatchFinality.v)
- Focus questions:
  - What is the definition of “post-matching” in code (phase predicate)?
  - Which lemma proves `matches` are preserved in P4–P7?
  - How does it become `G (Atom p_match_keep)`?

Concrete targets to find:
- `Definition finalityOK`
- `Theorem match_finality_LTL`
- (Chapter-4 phrasing) `Theorem match_finality_LTL_ch4`

### 4) Price Fairness
- Read: [Fairness/PriceFairness.v](../../Fairness/PriceFairness.v)
- Focus questions:
  - How is “no clearing price” handled (implication + totalization of the bound/rule atoms)?
  - Where is the marginal pair defined, and where are bounds proven?
  - Which lemmas connect the clearing price computation in P4 to stability in P5–P7?

Concrete targets to find:
- `Notation priceOK := QuantityFairness.priceOK`
- `Lemma uniform_price_fairness_LTL_initial`
- In [Fairness/QuantityFairness.v](../../Fairness/QuantityFairness.v): `bounds_cstar_from_wf`, `price_rule_fairness_LTL_initial`

### 5) Maximality
- Read: [Fairness/Maximality.v](../../Fairness/Maximality.v)
- Focus questions:
  - What is `phase_ge_4` exactly?
  - How is `no_feasible` proved at the P3→P4 boundary?
  - Is there a potential/measure argument that matching cannot continue?

Concrete targets to find:
- `Definition maximal`
- Measure: `Definition mu`
- Boundary lemma: `Lemma step_P4_inversion`
- Core theorem used elsewhere: `Theorem maximality_from_P1_or_P2`

### 6) Justified Rejection
- Read: [Fairness/JustifiedRejection.v](../../Fairness/JustifiedRejection.v)
- Focus questions:
  - How is “rejected” formalized (occurs in final match record)?
  - Where is the key lemma that rejected implies no feasible partner at the boundary state?
  - How is the post-matching guard used to make it an always-property?

Concrete targets to find:
- `Definition rejectionOK`
- `Lemma rejection_justified_of_no_feasible_prop`
- `Theorem justified_rejection_LTL_initial`

### 7) Priority Fairness (depends on explicit axioms)
- Read: [Fairness/PriorityFairness.v](../../Fairness/PriorityFairness.v)
- Focus questions:
  - What are the exact priority-respecting assumptions (axioms) used?
  - How does the proof avoid re-proving sorting correctness?
  - What does “priority step ok” mean in states where no trade is appended?

Concrete targets to find:
- `Definition priorityOK`
- `Lemma priorityB_step_ok_everywhere` / `Lemma priorityS_step_ok_everywhere`
- `Theorem priority_fairness_LTL`

## Dependency files to keep open
- [MUDA/Transitions.v](../../MUDA/Transitions.v) — `step` case split by phase; P7 absorbing
- [MUDA/Atoms.v](../../MUDA/Atoms.v) — definitions of the atomic predicates
- [MUDA/ClearingPrice.v](../../MUDA/ClearingPrice.v) — marginal pair + bounds
- [LTL/Semantics.v](../../LTL/Semantics.v) — `satisfies` unfolding lemmas for `G`/`F`/`U`

## Suggested “defense-ready” narrative per theorem
For each fairness theorem, prepare 3 sentences:
1) Operational statement (what it means in MUDA states).
2) Why it holds (invariant / boundary lemma / phase structure).
3) How it becomes an LTL property (lift to `G` with `mu_trace` + atom interpretation).
