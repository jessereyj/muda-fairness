(* Fairness/Maximality.v *)
From Stdlib Require Import Arith List.
Import ListNotations.

From MUDA Require Import Eqb Types State Sorting Matching ClearingPrice Transitions.

(* --- Local progress/exit at P3 ------------------------------------------- *)

Lemma step_P3_progress_or_exit : forall s,
  phase s = P3 ->
  (exists s', match_step s = Some s') \/ (match_step s = None).
Proof.
  intros s Hp.
  unfold match_step.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:HF.
  - left. eexists; reflexivity.
  - right. reflexivity.
Qed.

(* If we are in P3 and no feasible pair, the next phase is P4. *)
Lemma step_P4_from_P3_None : forall s,
  phase s = P3 ->
  match_step s = None ->
  phase (step s) = P4.
Proof.
  intros s Hp Hnone.
  unfold step. rewrite Hp. simpl. rewrite Hnone. reflexivity.
Qed.

(* Match-step keeps the phase (constructed state sets phase := phase s). *)
Lemma match_step_phase_invariant :
  forall s s', match_step s = Some s' -> phase s' = phase s.
Proof.
  intros s s' H.
  unfold match_step in H.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:?; try discriminate.
  inversion H; subst; reflexivity.
Qed.

Lemma step_P4_inversion : forall s,
  phase (step s) = P4 ->
  phase s = P3 /\ match_step s = None.
Proof.
  intros s H.
  (* Prove each part separately before any destructing *)
  assert (Hphase : phase s = P3).
  { unfold step in H.
    destruct (phase s) eqn:E; simpl in H.
    all: try discriminate H.
    all: try (rewrite E in H; discriminate H).
    reflexivity. }
  assert (Hmatch : match_step s = None).
  { unfold step in H. rewrite Hphase in H. simpl in H.
    destruct (match_step s) as [s'|] eqn:E.
    - (* H : phase s' = P4, E : match_step s = Some s' *)
      (* This case is impossible *)
      exfalso.
      (* Unfold match_step in E to see its structure *)
      unfold match_step in E.
      destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:HF; try discriminate E.
      (* Now E : Some {| ...; phase := phase s; ... |} = Some s' *)
      injection E as Heq_state.
      (* Heq_state : {| bids := bids s; ...; phase := phase s |} = s' *)
      (* Extract phase equality using f_equal *)
      assert (Hphase_eq : phase s' = phase s) by (rewrite <- Heq_state; reflexivity).
      rewrite Hphase_eq in H.
      rewrite Hphase in H.
      discriminate H.
    - reflexivity. }
  (* Now construct the final result *)
  split; [exact Hphase | exact Hmatch].
Qed.


Lemma execute_S : forall n s, execute (S n) s = execute n (step s).
Proof. reflexivity. Qed.

Lemma last_P3_predecessor :
  forall s n,
    phase (execute (S n) s) = P4 ->
    exists t, t = execute n s /\ phase t = P3 /\ match_step t = None.
Proof.
  intros s n H.
  induction n as [|n IH] in s, H |- *.
  - simpl in H. destruct (step_P4_inversion s H) as [Hp3 Hnone].
    exists s. repeat split; auto.
  - rewrite execute_S in H.
    specialize (IH (step s) H) as [t [Ht [Hp3 Hnone]]].
    exists (execute (S n) s). split; [reflexivity|].
    subst t. split; assumption.
Qed.

Lemma no_feasible_when_P4_reached :
  forall s n,
    phase (execute (S n) s) = P4 ->
    phase (execute n s) = P3 /\ match_step (execute n s) = None.
Proof.
  intros s n H. destruct (last_P3_predecessor s n H) as [t [-> [Hp3 Hnone]]].
  split; assumption.
Qed.

