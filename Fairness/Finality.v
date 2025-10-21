Require Import Coq.Lists.List.
Require Import MUDA.MUDA.State.
Require Import MUDA.MUDA.Matching.
Require Import MUDA.MUDA.Transitions.
Import ListNotations.

Lemma matches_monotone : forall s m,
  In m (matches s) -> In m (matches (step s)).
Proof.
  intros s m Hin.
  destruct (phase s); simpl; try assumption.
  (* P3 *)
  destruct (match_step s); simpl; auto; now right.
Qed.

Theorem match_finality_after_n : forall n s m,
  In m (matches s) -> In m (matches (execute n s)).
Proof.
  induction n; intros s m Hin; simpl; auto.
  apply IHn. eapply matches_monotone; eauto.
Qed.
