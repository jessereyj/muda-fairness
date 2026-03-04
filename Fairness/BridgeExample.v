(** Chapter 4 (Foundation Layer) — Meta-level Bridge Example

  Demonstrates using adequacy (⊢ implies ⊨) to move from derivability to
  semantic validity, mirroring the Chapter 4 meta-theory discussion.
*)
From Fairness Require Import All.

Local Open Scope LTL_scope.

Lemma example_bridge : forall φ, Provable φ -> valid φ.
Proof.
  intros φ Hprov.
  apply provable_implies_valid; exact Hprov.
Qed.
