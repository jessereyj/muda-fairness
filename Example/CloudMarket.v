(* Example/CloudMarket.v *)
From MUDA Require Import Eqb Types State Sorting Matching ClearingPrice Transitions Atoms.
From LTL Require Import Syntax Semantics Axioms Soundness Completeness LTL.
From Stdlib Require Import List.
Import ListNotations.
From Fairness Require Import All.

Local Open Scope LTL_scope.

Set Implicit Arguments.
Generalizable All Variables.

Definition mk_buyer (id: nat) : Agent := {| agent_id := id; agent_type := Buyer |}.
Definition mk_seller (id: nat) : Agent := {| agent_id := id; agent_type := Seller |}.

Definition B (id p q t: nat) : Bid :=
  {| bid_id := id; buyer := mk_buyer id; price := p; quantity := q; ts := t |}.

Definition A (id p q t: nat) : Ask :=
  {| ask_id := id; seller := mk_seller id; ask_price := p; ask_quantity := q; ask_ts := t |}.


Section Case_1.
  (* Chapter 5 Case 1:
     b1=(100,1,1), b2=(90,1,2), b3=(95,1,3); s1=(85,1,1) *)
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

  Example Case1_UniformPrice :
    satisfies run_case_1 0 priceOK.
  Proof. apply uniform_price_fairness_LTL_initial. Qed.

  Example Case1_MatchFinality :
    satisfies run_case_1 0 finalityOK.
  Proof. apply match_finality_LTL. Qed.

  Example Case1_Maximality :
    satisfies run_case_1 0 maximal.
  Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.

End Case_1.

Section Case_2.
  (* Chapter 5 Case 2:
     b1=(80,1,1); s1=(85,1,1), s2=(90,1,2) *)
  Definition bs2 : list Bid := [B 1 80 1 1].
  Definition as2 : list Ask := [A 1 85 1 1; A 2 90 1 2].
  Definition s0_case_2 : State := initial_state bs2 as2.
  Definition run_case_2 : trace := mu_trace s0_case_2.

  Example Case2_Priority : satisfies run_case_2 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case2_Quantity : satisfies run_case_2 0 quantityOK.   Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case2_UniformPrice : satisfies run_case_2 0 priceOK. Proof. apply uniform_price_fairness_LTL_initial. Qed.
  Example Case2_MatchFinality :  satisfies run_case_2 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case2_Maximality: satisfies run_case_2 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
  Example Case2_Rejection :
    satisfies run_case_2 0 rejectionOK.
  Proof. apply justified_rejection_LTL_initial. Qed.
End Case_2.

Section Case_3.
  (* Chapter 5 Case 3:
     b1=(100,2,1), b2=(95,2,2); s1=(80,2,1), s2=(85,2,2) *)
  Definition bs3 : list Bid := [B 1 100 2 1; B 2 95 2 2].
  Definition as3 : list Ask := [A 1 80 2 1; A 2 85 2 2].
  Definition s0_case_3 : State := initial_state bs3 as3.
  Definition run_case_3 : trace := mu_trace s0_case_3.

  Example Case3_Priority : satisfies run_case_3 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case3_Quantity : satisfies run_case_3 0 quantityOK.   Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case3_UniformPrice : satisfies run_case_3 0 priceOK. Proof. apply uniform_price_fairness_LTL_initial. Qed.
  Example Case3_MatchFinality :  satisfies run_case_3 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case3_Maximality: satisfies run_case_3 0 maximal.
  Proof. apply maximality_from_P1_or_P2. left. reflexivity. Qed.
End Case_3.

Section Case_4.
  (* Chapter 5 Case 4:
     b1=(100,1,1), b2=(100,1,2); s1=(90,1,1) *)
  Definition bs4 : list Bid := [B 1 100 1 1; B 2 100 1 2].
  Definition as4 : list Ask := [A 1 90 1 1].
  Definition s0_case_4 : State := initial_state bs4 as4.
  Definition run_case_4 : trace := mu_trace s0_case_4.

  Example Case4_Priority : satisfies run_case_4 0 priorityOK.
  Proof. apply priority_fairness_LTL. Qed.
  Example Case4_Quantity : satisfies run_case_4 0 quantityOK.   Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case4_UniformPrice : satisfies run_case_4 0 priceOK. Proof. apply uniform_price_fairness_LTL_initial. Qed.
  Example Case4_MatchFinality :  satisfies run_case_4 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case4_Maximality: satisfies run_case_4 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
End Case_4.

Section Case_5.
  (* Chapter 5 Case 5:
     b1=(100,5,1); s1=(80,2,1) *)
  Definition bs5 : list Bid := [B 1 100 5 1].
  Definition as5 : list Ask := [A 1 80 2 1].
  Definition s0_case_5 : State := initial_state bs5 as5.
  Definition run_case_5 : trace := mu_trace s0_case_5.

  Example Case5_Priority : satisfies run_case_5 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case5_Quantity : satisfies run_case_5 0 quantityOK.
  Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case5_UniformPrice : satisfies run_case_5 0 priceOK. Proof. apply uniform_price_fairness_LTL_initial. Qed.
  Example Case5_MatchFinality :  satisfies run_case_5 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case5_Maximality: satisfies run_case_5 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
End Case_5.

Section Case_6.
  (* Chapter 5 Case 6:
     b1=(100,3,1), b2=(90,2,2); s1=(80,2,1), s2=(85,2,2) *)
  Definition bs6 : list Bid := [B 1 100 3 1; B 2 90 2 2].
  Definition as6 : list Ask := [A 1 80 2 1; A 2 85 2 2].
  Definition s0_case_6 : State := initial_state bs6 as6.
  Definition run_case_6 : trace := mu_trace s0_case_6.

  Example Case6_Priority : satisfies run_case_6 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case6_Quantity : satisfies run_case_6 0 quantityOK.
  Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case6_UniformPrice : satisfies run_case_6 0 priceOK. Proof. apply uniform_price_fairness_LTL_initial. Qed.
  Example Case6_MatchFinality :  satisfies run_case_6 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case6_Maximality: satisfies run_case_6 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
End Case_6.

Section Case_7.
  (* Chapter 5 Case 7:
     b1=(110,3,1), b2=(105,2,2), b3=(100,1,3);
     s1=(85,2,1), s2=(90,2,2), s3=(95,1,3) *)
  Definition bs7 : list Bid := [B 1 110 3 1; B 2 105 2 2; B 3 100 1 3].
  Definition as7 : list Ask := [A 1 85 2 1; A 2 90 2 2; A 3 95 1 3].
  Definition s0_case_7 : State := initial_state bs7 as7.
  Definition run_case_7 : trace := mu_trace s0_case_7.

  Example Case7_Priority : satisfies run_case_7 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case7_Quantity : satisfies run_case_7 0 quantityOK.   Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case7_UniformPrice : satisfies run_case_7 0 priceOK. Proof. apply uniform_price_fairness_LTL_initial. Qed.
  Example Case7_MatchFinality :  satisfies run_case_7 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case7_Maximality: satisfies run_case_7 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
  Example Case7_Rejection :
    satisfies run_case_7 0 rejectionOK.
  Proof. apply justified_rejection_LTL_initial. Qed.
End Case_7.
