# Trusted Assumptions (Exact Inventory)

This repository contains **no admitted proofs** (see `./check.sh`), but it does include a small set of explicit **trusted assumptions** (`Axiom` / `Parameter`).

The list below is intended to match the thesis scope: we accept standard LTL meta-theory assumptions and treat sorting/priority behavior as abstracted background so the main effort focuses on the temporal fairness results.

## LTL (Foundation Layer)

- Propositional tautology oracle
  - [LTL/Axioms.v](../LTL/Axioms.v#L12): `Parameter IsPropTaut : LTL_formula -> Prop.`
  - Role: abstracts the notion of propositional tautology used by the Hilbert system.

- Tautologies are valid
  - [LTL/Soundness.v](../LTL/Soundness.v#L15): `Axiom A0_valid : forall φ, IsPropTaut φ -> valid φ.`
  - Role: the only meta-assumption used by the soundness proof; corresponds to “standard propositional reasoning”.

- Canonical countermodel construction (for completeness)
  - [LTL/Completeness.v](../LTL/Completeness.v#L18): `Axiom canonical_countermodel : ...`
  - Role: a standard ingredient to obtain weak completeness / adequacy results; fairness proofs do **not** depend on completeness.

## MUDA (Protocol Layer)

### Sorting (Phase P2)

- Abstract sorting functions
  - [MUDA/Sorting.v](../MUDA/Sorting.v#L318): `Axiom sort_bids : list Bid -> list Bid.`
  - [MUDA/Sorting.v](../MUDA/Sorting.v#L319): `Axiom sort_asks : list Ask -> list Ask.`

- Sorting correctness and permutation
  - [MUDA/Sorting.v](../MUDA/Sorting.v#L321): `Axiom sort_bids_correct : forall bs, bids_sorted (sort_bids bs).`
  - [MUDA/Sorting.v](../MUDA/Sorting.v#L322): `Axiom sort_asks_correct : forall asx, asks_sorted (sort_asks asx).`
  - [MUDA/Sorting.v](../MUDA/Sorting.v#L324): `Axiom sort_bids_perm : forall bs, Permutation (sort_bids bs) bs.`
  - [MUDA/Sorting.v](../MUDA/Sorting.v#L325): `Axiom sort_asks_perm : forall asx, Permutation (sort_asks asx) asx.`

### Greedy matching priority (Phase P3)

- Sortedness during P3
  - [MUDA/Atoms.v](../MUDA/Atoms.v#L107): `Axiom bids_sorted_in_P3 : ...`
  - [MUDA/Atoms.v](../MUDA/Atoms.v#L110): `Axiom asks_sorted_in_P3 : ...`

- Greedy respects priority
  - [MUDA/Atoms.v](../MUDA/Atoms.v#L113): `Axiom greedy_respects_priority_bids : ...`
  - [MUDA/Atoms.v](../MUDA/Atoms.v#L120): `Axiom greedy_respects_priority_asks : ...`

## Notes on dependency

- Fairness results are semantic theorems (`satisfies` over `mu_trace`) and do not require LTL completeness.
- The MUDA transition function uses sorting, so *all* fairness theorems inherit the sorting axioms as background assumptions.
- Priority fairness additionally uses the greedy-priority axioms.
