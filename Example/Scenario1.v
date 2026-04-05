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

(** Panel index (thesis ↔ code)

  Chapter 5 (Scenario 1 illustration)
  - st0, run_s1: concrete initial state and its induced trace (both Local)
  - Scenario1_Priority/Quantity/UniformPrice: instantiate Chapter 4 theorems (Local)
  - Scenario1_Matches_* and Scenario1_ClearingPrice_*: concrete execute-based checks (Local)
*)

Local Open Scope LTL_scope.

(* mk_buyer: create a buyer agent with a given identifier. *)
Local Definition mk_buyer (id : nat) : Agent :=
  {| agent_id := id; agent_type := Buyer |}.

(* mk_seller: create a seller agent with a given identifier. *)
Local Definition mk_seller (id : nat) : Agent :=
  {| agent_id := id; agent_type := Seller |}.

(* B: build a Bid record matching the thesis tuple (p,q,t) plus an id. *)
Local Definition B (id p q t : nat) : Bid :=
  {| bid_id := id; buyer := mk_buyer id; price := p; quantity := q; ts := t |}.

(* A: build an Ask record matching the thesis tuple (a,q,t) plus an id. *)
Local Definition A (id p q t : nat) : Ask :=
  {| ask_id := id; seller := mk_seller id; ask_price := p; ask_quantity := q; ask_ts := t |}.

(* b1, b2: concrete buyers from Scenario 1. *)
Local Definition b1 : Bid := B 1 10 5 1.
Local Definition b2 : Bid := B 2 8 4 2.

(* s1, s2: concrete sellers from Scenario 1. *)
Local Definition s1 : Ask := A 1 6 3 1.
Local Definition s2 : Ask := A 2 7 4 2.

(* bs_s1/as_s1: the concrete input lists used for initial_state. *)
Local Definition bs_s1 : list Bid := [b1; b2].
Local Definition as_s1 : list Ask := [s1; s2].

(* st0: initial state for Scenario 1. *)
Local Definition st0 : State := initial_state bs_s1 as_s1.
(* run_s1: induced infinite trace μ(st0). *)
Local Definition run_s1 : trace := mu_trace st0.

(* ------------------------------------------------------------------------- *)
(* Fairness: Scenario 1 satisfies all three fairness properties on run_s1. *)

Local Definition scenario1_fairness : LTL_formula :=
  priorityOK ∧ (quantityOK ∧ priceOK).

(* Scenario1_Priority: Scenario 1 satisfies the priority fairness property. *)
Local Example Scenario1_Priority : run_s1 ⊨ priorityOK.
Proof.
  unfold run_s1, st0.
  apply priority_fairness_LTL_initial.
Qed.

(* Scenario1_Quantity: Scenario 1 satisfies the quantity fairness property. *)
Local Example Scenario1_Quantity : run_s1 ⊨ quantityOK.
Proof.
  unfold run_s1, st0.
  apply quantity_fairness_LTL_initial.
Qed.

(* Scenario1_UniformPrice: Scenario 1 satisfies the uniform price property. *)
Local Example Scenario1_UniformPrice : run_s1 ⊨ priceOK.
Proof.
  unfold run_s1, st0.
  apply uniform_price_fairness_LTL_initial.
Qed.

(* Scenario1_AllFairness: bundle all three properties into one conjunction. *)
Local Example Scenario1_AllFairness : run_s1 ⊨ scenario1_fairness.
Proof.
  unfold scenario1_fairness.
  split.
  - apply Scenario1_Priority.
  - split.
    + apply Scenario1_Quantity.
    + apply Scenario1_UniformPrice.
Qed.

(* Concrete execution checks: matches and clearing price. *)

Local Definition m1 : Match := create_match b1 s1 [].
Local Definition m2 : Match := create_match b1 s2 [m1].
Local Definition m3 : Match := create_match b2 s2 [m1; m2].

(* Scenario1_Matches_After_Round1: after 3 steps, first match recorded. *)
Local Example Scenario1_Matches_After_Round1 :
  matches (execute 3 st0) = [m1].
Proof. cbv. reflexivity. Qed.

(* Scenario1_Matches_After_Round2: after 4 steps, second match recorded. *)
Local Example Scenario1_Matches_After_Round2 :
  matches (execute 4 st0) = [m1; m2].
Proof. cbv. reflexivity. Qed.

(* Scenario1_Matches_After_Round3: after 5 steps, third match recorded. *)
Local Example Scenario1_Matches_After_Round3 :
  matches (execute 5 st0) = [m1; m2; m3].
Proof. cbv. reflexivity. Qed.

(* Scenario1_P3_Terminates_After_Round3: greedy matcher finds no further feasible pair. *)
Local Example Scenario1_P3_Terminates_After_Round3 :
  match_step (execute 5 st0) = None.
Proof. cbv. reflexivity. Qed.

(* Scenario1_Enters_P4: protocol advances to clearing-price phase. *)
Local Example Scenario1_Enters_P4 :
  phase (execute 6 st0) = P4.
Proof. cbv. reflexivity. Qed.

(* Scenario1_ClearingPrice_Is_8: computed p* matches the thesis value. *)
Local Example Scenario1_ClearingPrice_Is_8 :
  clearing_price (execute 7 st0) = Some 8.
Proof. cbv. reflexivity. Qed.

(* Scenario1_Final_Phase_And_Price: phase and p* after Phase P4. *)
Local Example Scenario1_Final_Phase_And_Price :
  phase (execute 7 st0) = P5 /\ clearing_price (execute 7 st0) = Some 8.
Proof. cbv. auto. Qed.
