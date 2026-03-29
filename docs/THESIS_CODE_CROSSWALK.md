# Thesis ↔ Rocq Code Crosswalk

This crosswalk links thesis concepts to the verified Rocq development.

## Repo “layers” (matches Chapter 4)
- **LTL foundation**: [LTL/Syntax.v](../../LTL/Syntax.v), [LTL/Semantics.v](../../LTL/Semantics.v)
- **MUDA operational semantics**: [MUDA/State.v](../../MUDA/State.v), [MUDA/Transitions.v](../../MUDA/Transitions.v), [MUDA/Matching.v](../../MUDA/Matching.v), [MUDA/ClearingPrice.v](../../MUDA/ClearingPrice.v)
- **Fairness properties (LTL formulas + proofs)**: [Fairness](../../Fairness)
- **Examples**: [Example/CloudMarket.v](../../Example/CloudMarket.v)

## Chapter 3: MUDA STS
- State + phases P1..P7: [MUDA/State.v](../../MUDA/State.v)
- Deterministic transition `δ` (`step`): [MUDA/Transitions.v](../../MUDA/Transitions.v)
- Feasibility + greedy matching: [MUDA/Matching.v](../../MUDA/Matching.v)
- Priority ordering and sorting: [MUDA/Sorting.v](../../MUDA/Sorting.v)
- Marginal pair + uniform clearing price rule + boundedness: [MUDA/ClearingPrice.v](../../MUDA/ClearingPrice.v)
- State predicates as atoms: [MUDA/Atoms.v](../../MUDA/Atoms.v)

## Chapter 4: LTL foundation and trace semantics
- LTL syntax/operators (`G`, `F`, `U`, `X`, etc.): [LTL/Syntax.v](../../LTL/Syntax.v)
- Trace semantics + satisfaction: [LTL/Semantics.v](../../LTL/Semantics.v)
- Hilbert-style axiom system (A0–A3, MP, restricted necessitation): [LTL/Axioms.v](../../LTL/Axioms.v)
- Soundness (proved): [LTL/Soundness.v](../../LTL/Soundness.v)
- Weak completeness / adequacy (treated as standard results; includes axioms): [LTL/Completeness.v](../../LTL/Completeness.v)
- Convenience bundle: [LTL/LTL.v](../../LTL/LTL.v)

## Chapter 4.2: MUDA → LTL trace bridge
- Interpretation of atoms + induced trace: [Fairness/Interpretation.v](../../Fairness/Interpretation.v)

## Chapter 4.3–4.4: Fairness properties (formulas + theorems)
- Priority fairness: [Fairness/PriorityFairness.v](../../Fairness/PriorityFairness.v)
	- Main theorem: `priority_fairness_LTL`
- Quantity fairness: [Fairness/QuantityFairness.v](../../Fairness/QuantityFairness.v)
	- Formula: `quantityOK`
	- Main theorem (from initial state): `quantity_fairness_LTL_initial`
- Price fairness: [Fairness/QuantityFairness.v](../../Fairness/QuantityFairness.v) + [Fairness/PriceFairness.v](../../Fairness/PriceFairness.v)
	- Formula: `priceOK`
	  - Current shape: `G (Atom p_has_cprice → (Atom p_bounds_cstar ∧ Atom p_price_rule))`
	- Main theorem (from initial state): `uniform_price_fairness_LTL_initial`
- Match finality: [Fairness/MatchFinality.v](../../Fairness/MatchFinality.v)
	- Main theorems: `match_finality_LTL` and `match_finality_LTL_ch4`
- Maximality: [Fairness/Maximality.v](../../Fairness/Maximality.v)
	- Formula: `maximal`
	- Main theorem (from initial state P1/P2): `maximality_from_P1_or_P2`
- Justified rejection: [Fairness/JustifiedRejection.v](../../Fairness/JustifiedRejection.v)
	- Formula: `rejectionOK`
	- Main theorem (from initial state): `justified_rejection_LTL_initial`
- Bundle: [Fairness/All.v](../../Fairness/All.v)

## Thesis notation mapping
- For a more detailed symbol-by-symbol mapping, use [NOTATION.md](../../NOTATION.md).
