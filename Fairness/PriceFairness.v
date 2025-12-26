(* Fairness/PriceFairness.v *)
From Stdlib Require Import List Nat.
Import ListNotations.
From LTL  Require Import Syntax Semantics.
From MUDA Require Import Types State Matching ClearingPrice Transitions Atoms.
From Fairness Require Import Interpretation QuantityFairness.

Local Open Scope LTL_scope.

Notation priceOK := QuantityFairness.priceOK.

Lemma bounds_cstar_prop_holds_all : forall s i,
  wf_state (execute i s) -> bounds_cstar_prop (execute i s).
Proof.
  intros s i Hwf. apply bounds_cstar_from_wf. exact Hwf.
Qed.

Lemma uniform_price_fairness_LTL_initial : forall bs as_list,
  satisfies (mu_trace (initial_state bs as_list)) 0 priceOK.
Proof.
  intros bs as_list.
  unfold priceOK.
  rewrite satisfies_always_unfold.
  intros j _.
  rewrite mu_trace_atom_at_execute.
  unfold interp_atom.
  change (bounds_cstar_prop (execute j (initial_state bs as_list))).
  apply bounds_cstar_from_wf.
  apply wf_state_execute_n.
  apply wf_state_initial.
Qed.
