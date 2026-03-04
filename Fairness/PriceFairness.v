(** Chapter 4 (Fairness Verification Layer) — Section 4.3/4.4

  Price fairness: the clearing price (when defined) follows the rule and is
  bounded by the marginal pair.
*)
From LTL  Require Import LTL.
From MUDA Require Import State.
From Fairness Require Import Interpretation QuantityFairness.

Local Open Scope LTL_scope.

Notation priceOK := QuantityFairness.priceOK.

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
