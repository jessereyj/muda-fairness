(* Fairness/MatchFinality.v *)
From Stdlib Require Import List.
Import ListNotations.
From LTL Require Import Syntax Semantics Axioms.
From MUDA Require Import Eqb Types State Sorting Matching ClearingPrice Transitions.

(* One-step: every existing match persists after step. *)
Lemma matches_monotone : forall s m,
  In m (matches s) -> In m (matches (step s)).
Proof.
  intros s m Hin.
  unfold step.
  destruct (phase s) eqn:Hp; simpl; try exact Hin.
  - (* P3 -> either match_step or finish_matching *)
    destruct (match_step s) eqn:Hms; simpl.
    + (* Some s' : use match_step_monotonic from Matching.v *)
      apply (match_step_monotonic s s0 Hms).
      exact Hin.
    + (* None : finish_matching; matches unchanged *)
      exact Hin.
Qed.

(* n-step: by simple induction using the one-step lemma. *)
Theorem match_finality_after_n : forall n s m,
  In m (matches s) -> In m (matches (execute n s)).
Proof.
  induction n as [|n IH]; intros s m Hin; simpl; [exact Hin|].
  apply IH. eapply matches_monotone; eauto.
Qed.
