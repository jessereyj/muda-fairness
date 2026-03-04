(** Chapter 5 (Results) — Justified Rejection

  Justified rejection is stated in Chapter 5 as a post-matching property:
  in phases P4–P7, any rejected agent has no feasible counterparty.
*)
From Stdlib Require Import List Arith.
Import ListNotations.
From LTL  Require Import LTL.
From MUDA Require Import MUDA Atoms Matching Transitions.
From Fairness Require Import Interpretation Maximality.
Local Open Scope LTL_scope.

Definition justified_rej : LTL_formula :=
  And (Atom (p_phase 4)) (Atom p_rejection_justified).

(* Chapter 5: justified rejection is a post-matching invariant: once the
  protocol is in phases P4–P7, every rejection is justified. *)
Definition rejectionOK : LTL_formula := G (phase_ge_4 → Atom p_rejection_justified).

Lemma rejection_justified_of_no_feasible_prop :
  forall s,
    no_feasible_prop s ->
    rejection_justified_prop s.
Proof.
  intros s Hnf.
  split.
  - intros b aa Hb_in Haa_in.
    destruct Hb_in as [Hb_in _].
    specialize (Hnf b aa Hb_in Haa_in).
    exact Hnf.
  - intros aa b Haa_in Hb_in.
    destruct Haa_in as [Haa_in _].
    specialize (Hnf b aa Hb_in Haa_in).
    exact Hnf.
Qed.

Lemma step_P5_inversion : forall t,
  phase (step t) = P5 -> phase t = P4.
Proof.
  intros t H.
  unfold step in H.
  remember (phase t) as ph eqn:Hp.
  destruct ph; simpl in H.
  - discriminate H.
  - discriminate H.
  - (* P3 *)
    destruct (match_step t) eqn:Hm; simpl in H.
    + (* Some s' *)
      pose proof (match_step_phase_invariant t s Hm) as Hph.
      symmetry in Hp. rewrite Hp in Hph. rewrite Hph in H. discriminate.
    + (* None *) discriminate H.
  - (* P4 *) reflexivity.
  - discriminate H.
  - discriminate H.
  - symmetry in Hp; rewrite Hp in H; discriminate H.
Qed.

Lemma step_P6_inversion : forall t,
  phase (step t) = P6 -> phase t = P5.
Proof.
  intros t H.
  unfold step in H.
  remember (phase t) as ph eqn:Hp.
  destruct ph; simpl in H.
  - discriminate H.
  - discriminate H.
  - (* P3 *)
    destruct (match_step t) eqn:Hm; simpl in H.
    + pose proof (match_step_phase_invariant t s Hm) as Hph.
      symmetry in Hp. rewrite Hp in Hph. rewrite Hph in H. discriminate H.
    + discriminate H.
  - discriminate H.
  - (* P5 *) reflexivity.
  - discriminate H.
  - (* P7 *) symmetry in Hp; rewrite Hp in H; discriminate H.
Qed.

Lemma step_P7_inversion : forall t,
  phase (step t) = P7 -> phase t = P6 \/ phase t = P7.
Proof.
  intros t H.
  unfold step in H.
  remember (phase t) as ph eqn:Hp.
  destruct ph; simpl in H.
  - discriminate H.
  - discriminate H.
  - (* P3 *)
    destruct (match_step t) eqn:Hm; simpl in H.
    + pose proof (match_step_phase_invariant t s Hm) as Hph.
      symmetry in Hp. rewrite Hp in Hph. rewrite Hph in H. discriminate H.
    + discriminate H.
  - (* P4 *) discriminate H.
  - (* P5 *) discriminate H.
  - (* P6 *) now left.
  - (* P7 *) now right.
Qed.

Lemma no_feasible_preserved_after_P4 : forall t,
  (phase t = P4 \/ phase t = P5 \/ phase t = P6 \/ phase t = P7) ->
  no_feasible_prop t -> no_feasible_prop (step t).
Proof.
  intros t Hph Hnf.
  unfold no_feasible_prop in *.
  intros b a Hb Ha.
  pose proof (step_preserves_bids_asks t) as Hab.
  assert (phase t <> P2) as Hneq2.
  { intros Heq.
    destruct Hph as [H4|[H5|[H6|H7]]]; congruence. }
  assert (bids (step t) = bids t /\ asks (step t) = asks t) as [Hbids Hasks].
  { apply Hab. exact Hneq2. }
  rewrite Hbids in Hb. rewrite Hasks in Ha.
  (* matches unchanged from P4 onward *)
  unfold step.
  destruct (phase t) eqn:Hp; simpl in *.
  - destruct Hph as [H4|[H5|[H6|H7]]]; congruence.
  - destruct Hph as [H4|[H5|[H6|H7]]]; congruence.
  - destruct Hph as [H4|[H5|[H6|H7]]]; congruence.
  - apply Hnf; assumption.
  - apply Hnf; assumption.
  - apply Hnf; assumption.
  - apply Hnf; assumption.
Qed.

Lemma no_feasible_when_phase_ge4_initial :
  forall bs as_list k,
    (phase (execute (S k) (initial_state bs as_list)) = P4 \/
     phase (execute (S k) (initial_state bs as_list)) = P5 \/
     phase (execute (S k) (initial_state bs as_list)) = P6 \/
     phase (execute (S k) (initial_state bs as_list)) = P7) ->
    no_feasible_prop (execute (S k) (initial_state bs as_list)).
Proof.
  intros bs as_list k Hph.
  set (s0 := initial_state bs as_list) in *.
  induction k as [|k IH].
  - (* k = 0 *)
    simpl in Hph.
    destruct Hph as [H4|[H5|[H6|H7]]].
    all: unfold step in *; simpl in *; discriminate.
  - (* k = S k, goal state is execute (S (S k)) s0 *)
    set (t0 := execute (S k) s0).
    assert (Hexec : execute (S (S k)) s0 = step t0).
    { subst t0. rewrite execute_step_after. reflexivity. }

    (* Rewrite the phase hypothesis so it talks about phase (step t0) *)
    rewrite Hexec in Hph.

    destruct Hph as [H4|[H5|[H6|H7]]].
    + (* phase (step t0) = P4 *)
      destruct (step_P4_inversion t0 H4) as [Ht0P3 Hnone].
      rewrite Hexec.
      subst t0.
      apply no_feasible_step_from_None; assumption.
    + (* phase (step t0) = P5, so phase t0 = P4 *)
      pose proof (step_P5_inversion t0 H5) as Ht0P4.
      assert (Hnf_t0 : no_feasible_prop t0).
      { subst t0. eapply no_feasible_at_P4_index. exact Ht0P4. }
      rewrite Hexec.
      eapply no_feasible_preserved_after_P4.
      * left. exact Ht0P4.
      * exact Hnf_t0.
    + (* phase (step t0) = P6, so phase t0 = P5 *)
      pose proof (step_P6_inversion t0 H6) as Ht0P5.
      assert (Hnf_t0 : no_feasible_prop t0).
      { apply IH. right. left. subst t0. exact Ht0P5. }
      rewrite Hexec.
      eapply no_feasible_preserved_after_P4.
      * right. left. exact Ht0P5.
      * exact Hnf_t0.
    + (* phase (step t0) = P7, so phase t0 = P6 or P7 *)
      destruct (step_P7_inversion t0 H7) as [Ht0P6|Ht0P7].
      * assert (Hnf_t0 : no_feasible_prop t0).
        { apply IH. right. right. left. subst t0. exact Ht0P6. }
        rewrite Hexec.
        eapply no_feasible_preserved_after_P4.
        { right. right. left. exact Ht0P6. }
        exact Hnf_t0.
      * assert (Hnf_t0 : no_feasible_prop t0).
        { apply IH. right. right. right. subst t0. exact Ht0P7. }
        rewrite Hexec.
        eapply no_feasible_preserved_after_P4.
        { right. right. right. exact Ht0P7. }
        exact Hnf_t0.
Qed.

Theorem justified_rejection_LTL_initial :
  forall bs as_list,
    satisfies (mu_trace (initial_state bs as_list)) 0 rejectionOK.
Proof.
  intros bs as_list.
  unfold rejectionOK.
  rewrite satisfies_always_unfold.
  intros j Hj.
  (* Use maximality (now a post-matching invariant) to obtain no_feasible whenever phase_ge_4 holds. *)
  pose proof (maximality_from_P1_or_P2 (initial_state bs as_list)) as Hmax.
  assert (Hinit : phase (initial_state bs as_list) = P1 \/ phase (initial_state bs as_list) = P2).
  { left. reflexivity. }
  specialize (Hmax Hinit).
  unfold maximal in Hmax.
  rewrite satisfies_always_unfold in Hmax.
  pose proof (Hmax j Hj) as Hmax_j.
  simpl in Hmax_j.
  simpl.
  destruct Hmax_j as [Hnot_ge4 | Hnf_atom].
  - left. exact Hnot_ge4.
  - right.
    apply (proj2 (mu_trace_atom_at_execute (initial_state bs as_list) j p_rejection_justified)).
    unfold interp_atom. simpl.
    apply rejection_justified_of_no_feasible_prop.
    pose proof (proj1 (mu_trace_atom_at_execute (initial_state bs as_list) j p_no_feasible) Hnf_atom) as Hnf_interp.
    unfold interp_atom in Hnf_interp. simpl in Hnf_interp.
    exact Hnf_interp.
Qed.

