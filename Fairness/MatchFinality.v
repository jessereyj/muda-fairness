(* Fairness/MatchFinality.v *)
From Stdlib Require Import List.
Import ListNotations.
From LTL  Require Import LTL.
From MUDA Require Import MUDA Atoms.
From Fairness Require Import Interpretation.

Local Open Scope LTL_scope.

Definition final : LTL_formula := Atom p_terminal.

Definition finalityOK : LTL_formula := G (Atom p_match_keep).

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

Lemma matches_monotone_1 : forall s, matches_monotone_1_prop s.
Proof.
  intros s m Hin. now apply matches_monotone.
Qed.

Theorem match_finality_LTL : forall s,
  satisfies (mu_trace s) 0 finalityOK.
Proof.
  intro s. unfold finalityOK.
  rewrite satisfies_always_unfold.
  intros j _.
  apply (proj2 (mu_trace_atom_at_execute s j p_match_keep)).
  unfold interp_atom. apply matches_monotone_1.
Qed.
