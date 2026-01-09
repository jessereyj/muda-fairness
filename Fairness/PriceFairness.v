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
  apply QuantityFairness.uniform_price_fairness_LTL_initial.
Qed.

(* Price rule holds pointwise by definition of determine_clearing_price. *)
Lemma price_rule_fairness_LTL_initial : forall bs as_list,
  satisfies (mu_trace (initial_state bs as_list)) 0 (G (Atom p_price_rule)).
Proof.
  apply QuantityFairness.price_rule_fairness_LTL_initial.
Qed.
