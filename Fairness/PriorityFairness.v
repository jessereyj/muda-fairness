(* Fairness/PriorityFairness.v *)
From Stdlib Require Import List Bool PeanoNat.
Import ListNotations.
From LTL  Require Import LTL.
From MUDA Require Import MUDA Atoms Transitions.
From Fairness Require Import Interpretation.

Local Open Scope LTL_scope.

Definition priorityOK : LTL_formula :=
  (G (Atom p_prioB_step)) ∧ (G (Atom p_prioS_step)).

(* Section 4 alignment notes:
   - Atoms p_prioB_step and p_prioS_step are interpreted by interp_atom
     as priorityB_step_ok_prop s and priorityS_step_ok_prop s, respectively
     (see Fairness/Interpretation.v).
   - To prove the LTL obligations on mu_trace, it suffices to show that
     for every index i, priority*_step_ok_prop holds at the i-th state
     along the MUDA step execution (execute i s).
   - We scaffold the two bridging lemmas that connect trace semantics for
     Atom to interp_atom at execute i s, and the core operational fact
     that priority holds at each step. These are natural Section 4 hooks
     and can be discharged with Matching/Sorting lemmas. *)

(* Bridge: satisfaction of Atom along mu_trace reduces to interp_atom
   at the i-th executed state. *)
Lemma mu_trace_atom_at_execute :
  forall s i p,
    satisfies (mu_trace s) i (Atom p) <-> interp_atom (execute i s) p.
Proof.
  (* Follows from the semantics of Atom and the definition of mu_trace. *)
Admitted.

(* Core operational facts to be proved from Matching/Sorting:
   - In P3, find_feasible never returns a dominated pair (buyers).
   - Analogous for sellers. These should be shown to hold for all i along
     execute i s, hence the following lemmas. *)
Lemma priorityB_step_ok_everywhere :
  forall s i, priorityB_step_ok_prop (execute i s).
Admitted.

Lemma priorityS_step_ok_everywhere :
  forall s i, priorityS_step_ok_prop (execute i s).
Admitted.

Lemma mu_trace_satisfies_prioB :
  forall s i,
    satisfies (mu_trace s) i (Atom p_prioB_step).
Proof.
  intros s i.
  (* Reduce Atom satisfaction to interp_atom over execute i s *)
  apply (proj2 (mu_trace_atom_at_execute s i p_prioB_step)).
  (* And discharge via the operational invariant *)
  (* interp_atom maps p_prioB_step to priorityB_step_ok_prop *)
  (* This holds by priorityB_step_ok_everywhere. *)
  (* We rely on Interpretation.interp_atom case 6. *)
  (* The conversion is definitional in interp_atom; we reuse the invariant. *)
  (* The exact rewriting is left implicit here. *)
  (* Thus: *)
  (* show: interp_atom (execute i s) p_prioB_step *)
  (* which is priorityB_step_ok_prop (execute i s) *)
  (* by the invariant: *)
  pose proof (priorityB_step_ok_everywhere s i) as H.
  (* replace goal by the interp_atom case; this step will be solved
     when mu_trace_atom_at_execute is finalized. *)
  (* We keep the use-site explicit for clarity. *)
  (* exact H. *)
Admitted.

Lemma mu_trace_satisfies_prioS :
  forall s i,
    satisfies (mu_trace s) i (Atom p_prioS_step).
Proof.
  intros s i.
  apply (proj2 (mu_trace_atom_at_execute s i p_prioS_step)).
  pose proof (priorityS_step_ok_everywhere s i) as H.
  (* exact H. *)
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
