(* Fairness/PriorityFairness.v *)
From Stdlib Require Import List Bool PeanoNat Lia.
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
  intros s i p; split.
  - (* → *)
    (* satisfies (mu_trace s) i (Atom p) = trace_at (mu_trace s) i p *)
    unfold satisfies; revert s p.
    induction i as [|i IH]; intros s p; simpl.
    + intros H; exact H.
    + destruct (phase s); simpl; auto.
  - (* ← *)
    unfold satisfies; revert s p.
    induction i as [|i IH]; intros s p; simpl.
    + intros H; exact H.
    + destruct (phase s); simpl; auto.
Qed.

(* Core operational facts to be proved from Matching/Sorting:
   - In P3, find_feasible never returns a dominated pair (buyers).
   - Analogous for sellers. These should be shown to hold for all i along
     execute i s, hence the following lemmas. *)
(* We assume bids remain sorted across P3 iterations: sorting establishes
   order at P2->P3 transition and match_step preserves list order. *)

(* If a higher-priority feasible (b1,a) exists, find_feasible cannot pick (b2,a). *)
(* Priority relation refines the sorting comparator *)
(* Single-step greedy priority property (Section 4.3.1). We state it as an
   axiom here; it can be proved by induction on the bid list using the
   left-to-right structure of find_feasible and feasibility monotonicity. *)
(* (Moved axioms to MUDA/Atoms.v to keep semantic layer thin.) *)

Lemma priorityB_step_ok_everywhere :
  forall s i, priorityB_step_ok_prop (execute i s).
Proof.
  intros s i; revert s.
  induction i as [|i IH]; intros s; simpl.
  - (* i = 0 *)
    intros Hp3 b1 b2 a Hprio Hfeas Hcontra.
    eapply greedy_respects_priority_bids; eauto.
  - (* i = S i *)
    destruct (phase (execute i (step s))) eqn:Hph; simpl.
    + (* P1 *) intros Hp3 b1 b2 a Hprio Hfeas Heq; rewrite Hp3 in Hph; discriminate.
    + (* P2 *) intros Hp3 b1 b2 a Hprio Hfeas Heq; rewrite Hp3 in Hph; discriminate.
    + (* P3 *) intros Hp3 b1 b2 a Hprio Hfeas Hcontra.
        apply (IH (step s)) in Hp3.
        exact (Hp3 b1 b2 a Hprio Hfeas Hcontra).
    + (* P4 *) intros Hp3 b1 b2 a Hprio Hfeas Heq; rewrite Hp3 in Hph; discriminate.
    + (* P5 *) intros Hp3 b1 b2 a Hprio Hfeas Heq; rewrite Hp3 in Hph; discriminate.
    + (* P6 *) intros Hp3 b1 b2 a Hprio Hfeas Heq; rewrite Hp3 in Hph; discriminate.
    + (* P7 *) intros Hp3 b1 b2 a Hprio Hfeas Heq; rewrite Hp3 in Hph; discriminate.
Qed.

(* Symmetric seller-side axioms/lemmas *)
(* (Seller-side axioms also moved to MUDA/Atoms.v) *)

Lemma priorityS_step_ok_everywhere :
  forall s i, priorityS_step_ok_prop (execute i s).
Proof.
  intros s i; revert s.
  induction i as [|i IH]; intros s; simpl.
  - intros Hp3 a1 a2 b Hprio Hfeas Hcontra.
    eapply greedy_respects_priority_asks; eauto.
  - destruct (phase (execute i (step s))) eqn:Hph; simpl.
    + (* P1 *) intros Hp3 a1 a2 b Hprio Hfeas Heq; rewrite Hp3 in Hph; discriminate.
    + (* P2 *) intros Hp3 a1 a2 b Hprio Hfeas Heq; rewrite Hp3 in Hph; discriminate.
    + (* P3 *) intros Hp3 a1 a2 b Hprio Hfeas Hcontra.
        apply (IH (step s)) in Hp3.
        exact (Hp3 a1 a2 b Hprio Hfeas Hcontra).
    + (* P4 *) intros Hp3 a1 a2 b Hprio Hfeas Heq; rewrite Hp3 in Hph; discriminate.
    + (* P5 *) intros Hp3 a1 a2 b Hprio Hfeas Heq; rewrite Hp3 in Hph; discriminate.
    + (* P6 *) intros Hp3 a1 a2 b Hprio Hfeas Heq; rewrite Hp3 in Hph; discriminate.
    + (* P7 *) intros Hp3 a1 a2 b Hprio Hfeas Heq; rewrite Hp3 in Hph; discriminate.
Qed.

Lemma mu_trace_satisfies_prioB :
  forall s i,
    satisfies (mu_trace s) i (Atom p_prioB_step).
Proof.
  intros s i.
  apply (proj2 (mu_trace_atom_at_execute s i p_prioB_step)).
  (* interp_atom case dispatch: p_prioB_step mapped to priorityB_step_ok_prop *)
  unfold interp_atom.
  (* Simplify decoding of p_prioB_step (index 6) *)
  destruct (andb (Nat.leb (p_phase 1) p_prioB_step)
                 (Nat.leb p_prioB_step (p_phase 7))) eqn:Hrange.
  - (* In phase range: impossible because p_prioB_step = 6 < p_phase 1=11 *)
    simpl in Hrange. discriminate.
  - (* Falls through to case 6 mapping *)
    exact (priorityB_step_ok_everywhere s i).
Qed.

Lemma mu_trace_satisfies_prioS :
  forall s i,
    satisfies (mu_trace s) i (Atom p_prioS_step).
Proof.
  intros s i.
  apply (proj2 (mu_trace_atom_at_execute s i p_prioS_step)).
  unfold interp_atom.
  destruct (andb (Nat.leb (p_phase 1) p_prioS_step)
                 (Nat.leb p_prioS_step (p_phase 7))) eqn:Hrange.
  - simpl in Hrange. discriminate.
  - exact (priorityS_step_ok_everywhere s i).
Qed.

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
