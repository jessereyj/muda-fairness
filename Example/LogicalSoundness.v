(* Examples/LogicalSoundness.v — sanity checks for LTL/Soundness.v *)
From LTL Require Import Syntax Semantics Axioms Soundness.

Local Open Scope LTL_scope.

Example ex_Ax1_valid_implication : valid (Ax1 (Atom 0) (Atom 1)).
Proof. apply Ax1_valid. Qed.

Example ex_Ax2_valid_until : valid (Ax2 (Atom 0) (Atom 1)).
Proof. apply Ax2_valid. Qed.

Example ex_Ax3_valid_induction : valid (Ax3 (Atom 0)).
Proof. apply Ax3_valid. Qed.

Example ex_MP_valid : forall φ ψ, valid φ -> valid (φ → ψ) -> valid ψ.
Proof.
  intros φ ψ Hφ Himp.
  apply (MP_valid φ ψ); assumption.
Qed.

Example ex_Nec_valid_taut : forall φ, IsPropTaut φ -> valid (G φ).
Proof. intros; apply Nec_valid_taut; assumption. Qed.

Example ex_soundness_on_taut : forall φ, IsPropTaut φ -> valid φ.
Proof.
  intros φ Htaut.
  apply (A0_valid φ Htaut).
Qed.

Example ex_provable_implies_valid : forall φ, Provable φ -> valid φ.
Proof. intros φ H; apply soundness; exact H. Qed.
