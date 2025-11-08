(* Fairness/PriorityFairness.v *)
From Stdlib Require Import List Bool PeanoNat.
Import ListNotations.
From LTL  Require Import LTL.
From MUDA Require Import MUDA.
From Fairness Require Import Interpretation.

Local Open Scope LTL_scope.

Definition priorityOK : LTL_formula :=
  (G (Atom p_prioB_step)) ∧ (G (Atom p_prioS_step)).

(* assumes these props were defined and used in Interpretation.v *)
(* priorityB_step_ok_prop s and priorityS_step_ok_prop s *)

Lemma mu_trace_satisfies_prioB :
  forall s i,
    satisfies (mu_trace s) i (Atom p_prioB_step).
Proof.
  (* use Semantics.satisfies for Atom and Interpretation.interp_atom *)
Admitted.

Lemma mu_trace_satisfies_prioS :
  forall s i,
    satisfies (mu_trace s) i (Atom p_prioS_step).
Proof.
Admitted.

Theorem priority_fairness_LTL :
  forall s, satisfies (mu_trace s) 0 ((G (Atom p_prioB_step)) ∧ (G (Atom p_prioS_step))).
Proof.
  intro s. split.
  - (* G p_prioB_step *)
    unfold satisfies. simpl. intros j Hj.
    apply mu_trace_satisfies_prioB.
  - (* G p_prioS_step *)
    unfold satisfies. simpl. intros j Hj.
    apply mu_trace_satisfies_prioS.
Qed.
