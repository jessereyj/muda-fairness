Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import MUDA.MUDA.State.
Require Import MUDA.MUDA.Matching.
Require Import MUDA.MUDA.Transitions.
Import ListNotations.

(* From Matching.v: measure strictly decreases when we take a match *)
Lemma step_P3_progress_or_exit : forall s,
  phase s = P3 ->
  (exists s', match_step s = Some s' /\ measure s' < measure s)
  \/ (match_step s = None).
Proof.
  intros s Hp.
  unfold match_step.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:HF.
  - left. eexists. split; [reflexivity|].
    eapply match_step_decreases; eauto.
  - right. reflexivity.
Qed.

Lemma reaches_P4_in_measure_steps : forall s,
  phase s = P3 ->
  exists k, phase (execute k s) = P4.
Proof.
  refine (well_founded_induction_type
            (wf_inverse_image _ _ _ lt_wf measure)
            (fun s => phase s = P3 -> exists k, phase (execute k s) = P4) _ s).
  intros s IH Hp3.
  destruct (step_P3_progress_or_exit s Hp3) as [[s' [Hsome Hlt]] | Hnone].
  - (* we make a matching step *)
    assert (Hp3' : phase s' = P3) by (inversion Hsome; reflexivity).
    specialize (IH s' Hlt Hp3').
    destruct IH as [k Hk]. exists (S k). simpl.
    rewrite Hp3. rewrite Hsome. exact Hk.
  - (* no feasible pair: we finish to P4 in one step *)
    exists 1%nat. simpl. rewrite Hp3. rewrite Hnone. reflexivity.
Qed.

Theorem termination : forall s,
  phase s = P3 -> exists fuel, phase (execute fuel s) = P4.
Proof. eapply reaches_P4_in_measure_steps. Qed.

Lemma no_feasible_at_P4 : forall s,
  phase s = P3 ->
  match_step s = None ->
  phase (finish_matching s) = P4.
Proof. intros; reflexivity. Qed.

(* At P4 we got there exactly because match_step was None at the last P3 *)
Lemma no_feasible_when_P4_reached : forall s k,
  phase s = P3 ->
  phase (execute k s) = P4 ->
  match_step (execute (pred k) s) = None.
Proof.
  destruct k; simpl; intros; try congruence.
  rewrite H in *. simpl in H0.
  destruct (match_step s) eqn:E; try discriminate.
  inversion H0; subst; auto.
Qed.
