(** Chapter 5 — Scenario 1 (from the thesis excerpt)

  Buyers:
    b1 = (10,5,1)
    b2 = (8,4,2)

  Sellers:
    s1 = (6,3,1)
    s2 = (7,4,2)

  Expected greedy matching:
    (b1,s1,q=3), (b1,s2,q=2), (b2,s2,q=2)
  Expected clearing price:
    p* = 8 (marginal seller exhausted => use marginal bid price).

  This file serves two purposes:
  - Correctness of the concrete execution (expected matches + clearing price).
  - Fairness of the induced trace, using the Chapter 4 fairness modules:
      PriorityFairness, QuantityFairness, PriceFairness.
*)
From Stdlib Require Import List.
Import ListNotations.

From LTL      Require Import Syntax Semantics.
From MUDA     Require Import Types State Matching Transitions.
From Fairness Require Import Interpretation PriorityFairness QuantityFairness PriceFairness.

Local Open Scope LTL_scope.

Definition mk_buyer (id : nat) : Agent :=
  {| agent_id := id; agent_type := Buyer |}.

Definition mk_seller (id : nat) : Agent :=
  {| agent_id := id; agent_type := Seller |}.

Definition B (id p q t : nat) : Bid :=
  {| bid_id := id; buyer := mk_buyer id; price := p; quantity := q; ts := t |}.

Definition A (id p q t : nat) : Ask :=
  {| ask_id := id; seller := mk_seller id; ask_price := p; ask_quantity := q; ask_ts := t |}.

Definition b1 : Bid := B 1 10 5 1.
Definition b2 : Bid := B 2 8 4 2.

Definition s1 : Ask := A 1 6 3 1.
Definition s2 : Ask := A 2 7 4 2.

Definition bs_s1 : list Bid := [b1; b2].
Definition as_s1 : list Ask := [s1; s2].

Definition st0 : State := initial_state bs_s1 as_s1.
Definition run_s1 : trace := mu_trace st0.

(* ------------------------------------------------------------------------- *)
(* Fairness: Scenario 1 satisfies all three fairness properties on run_s1. *)

Definition scenario1_fairness : LTL_formula :=
  priorityOK ∧ (quantityOK ∧ priceOK).

Example Scenario1_Priority : satisfies run_s1 0 priorityOK.
Proof.
  unfold run_s1, st0.
  apply priority_fairness_LTL_initial.
Qed.

Example Scenario1_Quantity : satisfies run_s1 0 quantityOK.
Proof.
  unfold run_s1, st0.
  apply quantity_fairness_LTL_initial.
Qed.

Example Scenario1_UniformPrice : satisfies run_s1 0 priceOK.
Proof.
  unfold run_s1, st0.
  apply uniform_price_fairness_LTL_initial.
Qed.

Example Scenario1_AllFairness : satisfies run_s1 0 scenario1_fairness.
Proof.
  unfold scenario1_fairness.
  split.
  - apply Scenario1_Priority.
  - split.
    + apply Scenario1_Quantity.
    + apply Scenario1_UniformPrice.
Qed.

(* Concrete execution checks: matches and clearing price. *)

Definition m1 : Match := create_match b1 s1 [].
Definition m2 : Match := create_match b1 s2 [m1].
Definition m3 : Match := create_match b2 s2 [m1; m2].

Example Scenario1_Matches_After_Round1 :
  matches (execute 3 st0) = [m1].
Proof. cbv. reflexivity. Qed.

Example Scenario1_Matches_After_Round2 :
  matches (execute 4 st0) = [m1; m2].
Proof. cbv. reflexivity. Qed.

Example Scenario1_Matches_After_Round3 :
  matches (execute 5 st0) = [m1; m2; m3].
Proof. cbv. reflexivity. Qed.

Example Scenario1_P3_Terminates_After_Round3 :
  match_step (execute 5 st0) = None.
Proof. cbv. reflexivity. Qed.

Example Scenario1_Enters_P4 :
  phase (execute 6 st0) = P4.
Proof. cbv. reflexivity. Qed.

Example Scenario1_ClearingPrice_Is_8 :
  clearing_price (execute 7 st0) = Some 8.
Proof. cbv. reflexivity. Qed.

Example Scenario1_Final_Phase_And_Price :
  phase (execute 7 st0) = P5 /\ clearing_price (execute 7 st0) = Some 8.
Proof. cbv. auto. Qed.
