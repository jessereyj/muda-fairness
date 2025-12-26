(* Example/LogicalCompleteness.v — sanity checks for LTL/Completeness.v *)
From LTL Require Import Syntax Semantics Axioms Soundness Completeness.

Local Open Scope LTL_scope.

Example ex_WeakCompleteness_on_taut : forall φ, IsPropTaut φ -> Provable φ.
Proof.
  intros φ Htaut.
  apply WeakCompleteness.
  apply (A0_valid φ Htaut).
Qed.

Example ex_Adequacy_forward : forall φ, Provable φ -> valid φ.
Proof.
  intros φ Hprov.
  apply soundness; exact Hprov.
Qed.

Example ex_Adequacy_backward : forall φ, valid φ -> Provable φ.
Proof.
  intros φ Hvalid.
  apply WeakCompleteness; exact Hvalid.
Qed.

Example ex_WC_Ax1 : Provable (Ax1 (Atom 0) (Atom 1)).
Proof.
  apply WeakCompleteness.
  apply Ax1_valid.
Qed.

Example ex_WC_Ax2 : Provable (Ax2 (Atom 0) (Atom 1)).
Proof.
  apply WeakCompleteness.
  apply Ax2_valid.
Qed.

Example ex_WC_Ax3 : Provable (Ax3 (Atom 0)).
Proof.
  apply WeakCompleteness.
  apply Ax3_valid.
Qed.
