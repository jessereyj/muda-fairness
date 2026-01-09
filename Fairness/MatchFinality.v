(* Fairness/MatchFinality.v *)
From Stdlib Require Import List.
Import ListNotations.
From LTL  Require Import LTL.
From MUDA Require Import MUDA Atoms.
From Fairness Require Import Interpretation.

Local Open Scope LTL_scope.

Definition final : LTL_formula := Atom p_terminal.

Definition finalityOK : LTL_formula := G (Atom p_match_keep).

Lemma matches_prefix : forall s,
  prefix (matches s) (matches (step s)).
Proof.
  intros s.
  unfold step.
  destruct (phase s) eqn:Hp; simpl.
  - exists []; reflexivity.
  - exists []; reflexivity.
  - (* P3 -> either match_step or finish_matching *)
    destruct (match_step s) eqn:Hms; simpl.
    + (* Some s' : match_step appends one match *)
      apply match_step_head_is_create in Hms.
      destruct Hms as [b [a Hmatches]].
      rewrite Hmatches. exists [create_match b a (matches s)]. reflexivity.
    + (* None : finish_matching; matches unchanged *)
      exists []; reflexivity.
  - (* P4 *) exists []; reflexivity.
  - (* P5 *) exists []; reflexivity.
  - (* P6 *) exists []; reflexivity.
  - (* P7 *) exists []; reflexivity.
Qed.

(* n-step: by simple induction using the one-step lemma. *)
Theorem match_finality_after_n : forall n s,
  prefix (matches s) (matches (execute n s)).
Proof.
  induction n as [|n IH]; intros s; simpl.
  - exists []; reflexivity.
  - destruct (matches_prefix s) as [w' Hw'].
    rewrite Hw'.
    specialize (IH (step s)).
    destruct IH as [w'' Hw''].
    rewrite Hw''.
    exists (w' ++ w''). rewrite app_assoc. reflexivity.
Qed.

Lemma match_keep_prop_holds : forall s, match_keep_prop s.
Proof.
  intro s. apply matches_prefix.
Qed.

Theorem match_finality_LTL : forall s,
  satisfies (mu_trace s) 0 finalityOK.
Proof.
  intro s. unfold finalityOK.
  rewrite satisfies_always_unfold.
  intros j _.
  apply (proj2 (mu_trace_atom_at_execute s j p_match_keep)).
  unfold interp_atom. apply match_keep_prop_holds.
Qed.
