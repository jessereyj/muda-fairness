(** * MUDA Fairness Simulations
    Seven scenarios checked against LTL fairness properties.

    Preconditions
    - Section 3: State, transitions, and MUDA operations are defined.
    - Section 4: LTL syntax/semantics and the five finalized formulas are exported.
    - Section 5: These scenarios match the narrative and figures in the text.

    This file only depends on the exported, finalized formulas:
      priorityOK, allocOK, final, maximal, rejectionOK.
    The Examples below state exactly the claims listed in Section 5.
*)

From MUDA Require Import Eqb Types State Sorting Matching ClearingPrice Transitions Atoms.
From LTL Require Import Syntax Semantics Axioms Soundness Completeness LTL.
From Stdlib Require Import List.
Import ListNotations.
(* Import fairness properties (LTL formulas) *)
From Fairness Require Import All.

Local Open Scope LTL_scope.

Set Implicit Arguments.
Generalizable All Variables.

(* If your LTL library uses a valuation for atoms, ensure the five formulas
  below are already closed formulas, exported by Fairness/Fairness.v. *)
(*** Utilities **************************************************************)
(* Concrete construction helpers for scenarios *)
Definition mk_buyer (id: nat) : Agent := {| agent_id := id; agent_type := Buyer |}.
Definition mk_seller (id: nat) : Agent := {| agent_id := id; agent_type := Seller |}.

Definition B (id p q t: nat) : Bid :=
  {| bid_id := id; buyer := mk_buyer id; price := p; quantity := q; ts := t |}.

Definition A (id p q t: nat) : Ask :=
  {| ask_id := id; seller := mk_seller id; ask_price := p; ask_quantity := q; ask_ts := t |}.

(** * 
    Case 1: Late Buyer Attempts to Rematch
    Inputs (price, quantity, ts):
      b1 = (100, 1, 1), b2 = (90, 1, 2), b3 = (95, 1, 3)
      s1 = (85,  1, 1)
    We construct the initial state and instantiate the Fairness theorems.
*)
Section Case_1.
  (* Inputs: b1=(100,1,1), b2=(90,1,2), b3=(95,1,3); s1=(85,1,1) *)
  Definition bs1 : list Bid := [B 1 100 1 1; B 2 90 1 2; B 3 95 1 3].
  Definition as1 : list Ask := [A 1 85 1 1].
  Definition s0_case_1 : State := initial_state bs1 as1.
  Definition run_case_1 : trace := mu_trace s0_case_1.

  Example Case1_Priority :
    satisfies run_case_1 0 priorityOK.
  Proof. apply priority_fairness_LTL. Qed.

  Example Case1_Quantity :
    satisfies run_case_1 0 quantityOK.
  Proof. apply quantity_fairness_LTL_initial. Qed.

  Example Case1_MatchFinality :
    satisfies run_case_1 0 finalityOK.
  Proof. apply match_finality_LTL. Qed.

  Example Case1_Maximality :
    satisfies run_case_1 0 maximal.
  Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.

  Example Case1_Rejection :
    satisfies run_case_1 0 rejectionOK.
  Proof.
  unfold rejectionOK. rewrite satisfies_always_unfold.
  intros j _. right.
  apply (proj2 (mu_trace_atom_at_execute s0_case_1 j p_rejection_justified)).
  apply rejection_justified_all.
  Qed.
End Case_1.

(*** Scenario 2 *************************************************************)

Section Case_2.
  (* Inputs: b1=(100,1,1), b2=(60,1,2); s1=(80,1,1) *)
  Definition bs2 : list Bid := [B 1 100 1 1; B 2 60 1 2].
  Definition as2 : list Ask := [A 1 80 1 1].
  Definition s0_case_2 : State := initial_state bs2 as2.
  Definition run_case_2 : trace := mu_trace s0_case_2.

  Example Case2_Priority : satisfies run_case_2 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case2_Quantity : satisfies run_case_2 0 quantityOK.   Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case2_MatchFinality :  satisfies run_case_2 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case2_Maximality: satisfies run_case_2 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
  Example Case2_Rejection : satisfies run_case_2 0 rejectionOK.   Proof.
  unfold rejectionOK. rewrite satisfies_always_unfold. intros j _. right.
  apply (proj2 (mu_trace_atom_at_execute s0_case_2 j p_rejection_justified)).
  apply rejection_justified_all.
  Qed.
  (* Remove duplicate admitted examples (already proved above). *)
End Case_2.

(*** Scenario 3 *************************************************************)

Section Case_3.
  (* Inputs: b1=(100,2,1), b2=(90,1,2), b3=(85,1,3); s1=(80,1,1), s2=(85,1,2) *)
  Definition bs3 : list Bid := [B 1 100 2 1; B 2 90 1 2; B 3 85 1 3].
  Definition as3 : list Ask := [A 1 80 1 1; A 2 85 1 2].
  Definition s0_case_3 : State := initial_state bs3 as3.
  Definition run_case_3 : trace := mu_trace s0_case_3.

  Example Case3_Priority : satisfies run_case_3 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case3_Quantity : satisfies run_case_3 0 quantityOK.   Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case3_MatchFinality :  satisfies run_case_3 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case3_Maximality: satisfies run_case_3 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
  Example Case3_Rejection : satisfies run_case_3 0 rejectionOK.   Proof.
  unfold rejectionOK. rewrite satisfies_always_unfold. intros j _. right.
  apply (proj2 (mu_trace_atom_at_execute s0_case_3 j p_rejection_justified)).
  apply rejection_justified_all.
  Qed.
End Case_3.

(*** Scenario 4 *************************************************************)

Section Case_4.
  (* Inputs: b1=(90,1,2), b2=(90,1,3); s1=(80,1,1) *)
  Definition bs4 : list Bid := [B 1 90 1 2; B 2 90 1 3].
  Definition as4 : list Ask := [A 1 80 1 1].
  Definition s0_case_4 : State := initial_state bs4 as4.
  Definition run_case_4 : trace := mu_trace s0_case_4.

  Example Case4_Priority : satisfies run_case_4 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case4_Quantity : satisfies run_case_4 0 quantityOK.   Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case4_MatchFinality :  satisfies run_case_4 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case4_Maximality: satisfies run_case_4 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
  Example Case4_Rejection : satisfies run_case_4 0 rejectionOK.   Proof.
  unfold rejectionOK. rewrite satisfies_always_unfold. intros j _. right.
  apply (proj2 (mu_trace_atom_at_execute s0_case_4 j p_rejection_justified)).
  apply rejection_justified_all.
  Qed.
End Case_4.

(*** Scenario 5 *************************************************************)

Section Case_5.
  (* Inputs: b1=(100,5,1), b2=(95,1,2); s1=(80,1,1), s2=(85,1,2), s3=(90,1,3) *)
  Definition bs5 : list Bid := [B 1 100 5 1; B 2 95 1 2].
  Definition as5 : list Ask := [A 1 80 1 1; A 2 85 1 2; A 3 90 1 3].
  Definition s0_case_5 : State := initial_state bs5 as5.
  Definition run_case_5 : trace := mu_trace s0_case_5.

  Example Case5_Priority : satisfies run_case_5 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case5_Quantity : satisfies run_case_5 0 quantityOK.   Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case5_MatchFinality :  satisfies run_case_5 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case5_Maximality: satisfies run_case_5 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
  Example Case5_Rejection : satisfies run_case_5 0 rejectionOK.   Proof.
  unfold rejectionOK. rewrite satisfies_always_unfold. intros j _. right.
  apply (proj2 (mu_trace_atom_at_execute s0_case_5 j p_rejection_justified)).
  apply rejection_justified_all.
  Qed.
End Case_5.

(*** Scenario 6 *************************************************************)

Section Case_6.
  (* Inputs: b1=(100,1,1) (true need 2); s1=(80,2,1) *)
  Definition bs6 : list Bid := [B 1 100 1 1].
  Definition as6 : list Ask := [A 1 80 2 1].
  Definition s0_case_6 : State := initial_state bs6 as6.
  Definition run_case_6 : trace := mu_trace s0_case_6.

  Example Case6_Priority : satisfies run_case_6 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case6_Quantity : satisfies run_case_6 0 quantityOK.   Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case6_MatchFinality :  satisfies run_case_6 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case6_Maximality: satisfies run_case_6 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
  Example Case6_Rejection : satisfies run_case_6 0 rejectionOK.   Proof.
  unfold rejectionOK. rewrite satisfies_always_unfold. intros j _. right.
  apply (proj2 (mu_trace_atom_at_execute s0_case_6 j p_rejection_justified)).
  apply rejection_justified_all.
  Qed.
End Case_6.

(*** Scenario 7 *************************************************************)

Section Case_7.
  (* Inputs: b1=(100,1,1), b2=(90,1,2), b3=(85,1,3); s1=(80,1,1), s2=(95,1,2) *)
  Definition bs7 : list Bid := [B 1 100 1 1; B 2 90 1 2; B 3 85 1 3].
  Definition as7 : list Ask := [A 1 80 1 1; A 2 95 1 2].
  Definition s0_case_7 : State := initial_state bs7 as7.
  Definition run_case_7 : trace := mu_trace s0_case_7.

  Example Case7_Priority : satisfies run_case_7 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case7_Quantity : satisfies run_case_7 0 quantityOK.   Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case7_MatchFinality :  satisfies run_case_7 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case7_Maximality: satisfies run_case_7 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
  Example Case7_Rejection : satisfies run_case_7 0 rejectionOK.   Proof.
  unfold rejectionOK. rewrite satisfies_always_unfold. intros j _. right.
  apply (proj2 (mu_trace_atom_at_execute s0_case_7 j p_rejection_justified)).
  apply rejection_justified_all.
  Qed.
End Case_7.
