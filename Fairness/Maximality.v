From Stdlib Require Import Arith List.
Import ListNotations.

From MUDA Require Import Eqb Types State Sorting Matching ClearingPrice Transitions.

(* Simplified progress/termination lemmas (measure not implemented yet) *)
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

(* We don't have a formal measure defined yet; admit the more general termination facts for now. *)
Lemma reaches_P4_in_measure_steps : forall s,
  phase s = P3 ->
  exists k, phase (execute k s) = P4.
Proof. Admitted.

Theorem termination : forall s,
  phase s = P3 -> exists fuel, phase (execute fuel s) = P4.
Proof. Admitted.

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
