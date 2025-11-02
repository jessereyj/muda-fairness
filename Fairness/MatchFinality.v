(* Fairness/MatchFinality.v *)
From Stdlib Require Import List.
Import ListNotations.

From LTL Require Import Syntax Semantics Axioms.
From MUDA Require Import Eqb Types State Sorting Matching ClearingPrice Transitions.

Lemma matches_monotone : forall s m,
  In m (matches s) -> In m (matches (step s)).
Proof. Admitted.


Theorem match_finality_after_n : forall n s m,
  In m (matches s) -> In m (matches (execute n s)).
Proof.
  induction n; intros s m Hin; simpl; auto.
  apply IHn. eapply matches_monotone; eauto.
Qed.
