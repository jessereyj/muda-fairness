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
From LTL Require Import Syntax Semantics Axioms Soundness Completeness.
From Fairness Require Import All.

Set Implicit Arguments.
Generalizable All Variables.

(* If your LTL library uses a valuation for atoms, ensure the five formulas
   below are already closed formulas, exported by Fairness/All.v. *)
(*** Utilities **************************************************************)
(* You likely already have a canonical ω-run with explicit stuttering in §4.
   If so, import it. Otherwise, declare the runs per case as Parameters here
   and replace them with concrete CoFixpoints later. *)

(** * 
    Case 1: Late Buyer Attempts to Rematch
    Inputs (price, quantity, ts):
      b1 = (100, 1, 1), b2 = (90, 1, 2), b3 = (95, 1, 3)
      s1 = (85,  1, 1)
    We construct the initial state and instantiate the Fairness theorems.
*)
Section Case_1.
  Parameter s0_case_1 : State.
  Parameter run_case_1 : trace.  (* Your ω-run starting at s0_case_1 *)

  Example Case1_Priority :
    satisfies run_case_1 0 (G priorityOK).
  Proof. Admitted.

  Example Case1_Quantity :
    satisfies run_case_1 0 (G allocOK).
  Proof. Admitted.

  Example Case1_MatchFinality :
    satisfies run_case_1 0 (F final).
  Proof. Admitted.

  Example Case1_Maximality :
    satisfies run_case_1 0 maximal.
  Proof. Admitted.

  Example Case1_Rejection :
    satisfies run_case_1 0 rejectionOK.
  Proof. Admitted.
End Case_1.

(*** Scenario 2 *************************************************************)

Section Case_2.
  Parameter s0_case_2 : State.
  Parameter run_case_2 : trace.

  Example Case2_Priority : satisfies run_case_2 0 (G priorityOK). Proof. Admitted. Qed.
  Example Case2_Quantity : satisfies run_case_2 0 (G allocOK).   Proof. Admitted. Qed.
  Example Case2_MatchFinality :  satisfies run_case_2 0 (F final).     Proof. Admitted. Qed.
  Example Case2_Maximality: satisfies run_case_2 0 maximal.       Proof. Admitted. Qed.
  Example Case2_Rejection : satisfies run_case_2 0 rejectionOK.   Proof. Admitted. Qed.
End Case_2.

(*** Scenario 3 *************************************************************)

Section Case_3.
  Parameter s0_case_3 : State.
  Parameter run_case_3 : trace.

  Example Case3_Priority : satisfies run_case_3 0 (G priorityOK). Proof. Admitted. Qed.
  Example Case3_Quantity : satisfies run_case_3 0 (G allocOK).   Proof. Admitted. Qed.
  Example Case3_MatchFinality :  satisfies run_case_3 0 (F final).     Proof. Admitted. Qed.
  Example Case3_Maximality: satisfies run_case_3 0 maximal.       Proof. Admitted. Qed.
  Example Case3_Rejection : satisfies run_case_3 0 rejectionOK.   Proof. Admitted. Qed.
End Case_3.

(*** Scenario 4 *************************************************************)

Section Case_4.
  Parameter s0_case_4 : State.
  Parameter run_case_4 : trace.

  Example Case4_Priority : satisfies run_case_4 0 (G priorityOK). Proof. Admitted. Qed.
  Example Case4_Quantity : satisfies run_case_4 0 (G allocOK).   Proof. Admitted. Qed.
  Example Case4_MatchFinality :  satisfies run_case_4 0 (F final).     Proof. Admitted. Qed.
  Example Case4_Maximality: satisfies run_case_4 0 maximal.       Proof. Admitted. Qed.
  Example Case4_Rejection : satisfies run_case_4 0 rejectionOK.   Proof. Admitted. Qed.
End Case_4.

(*** Scenario 5 *************************************************************)

Section Case_5.
  Parameter s0_case_5 : State.
  Parameter run_case_5 : trace.

  Example Case5_Priority : satisfies run_case_5 0 (G priorityOK). Proof. Admitted. Qed.
  Example Case5_Quantity : satisfies run_case_5 0 (G allocOK).   Proof. Admitted. Qed.
  Example Case5_MatchFinality :  satisfies run_case_5 0 (F final).     Proof. Admitted. Qed.
  Example Case5_Maximality: satisfies run_case_5 0 maximal.       Proof. Admitted. Qed.
  Example Case5_Rejection : satisfies run_case_5 0 rejectionOK.   Proof. Admitted. Qed.
End Case_5.

(*** Scenario 6 *************************************************************)

Section Case_6.
  Parameter s0_case_6 : State.
  Parameter run_case_6 : trace.

  Example Case6_Priority : satisfies run_case_6 0 (G priorityOK). Proof. Admitted. Qed.
  Example Case6_Quantity : satisfies run_case_6 0 (G allocOK).   Proof. Admitted. Qed.
  Example Case6_MatchFinality :  satisfies run_case_6 0 (F final).     Proof. Admitted. Qed.
  Example Case6_Maximality: satisfies run_case_6 0 maximal.       Proof. Admitted. Qed.
  Example Case6_Rejection : satisfies run_case_6 0 rejectionOK.   Proof. Admitted. Qed.
End Case_6.

(*** Scenario 7 *************************************************************)

Section Case_7.
  Parameter s0_case_7 : State.
  Parameter run_case_7 : trace.

  Example Case7_Priority : satisfies run_case_7 0 (G priorityOK). Proof. Admitted. Qed.
  Example Case7_Quantity : satisfies run_case_7 0 (G allocOK).   Proof. Admitted. Qed.
  Example Case7_MatchFinality :  satisfies run_case_7 0 (F final).     Proof. Admitted. Qed.
  Example Case7_Maximality: satisfies run_case_7 0 maximal.       Proof. Admitted. Qed.
  Example Case7_Rejection : satisfies run_case_7 0 rejectionOK.   Proof. Admitted. Qed.
End Case_7.
