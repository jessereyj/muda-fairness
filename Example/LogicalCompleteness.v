(* Example/LogicalCompleteness.v — sanity checks for LTL/Completeness.v *)
From LTL Require Import Syntax Semantics Axioms Soundness Completeness.

Local Open Scope LTL_scope.

(* Weak Completeness: validity implies provability. *)
Example ex_WeakCompleteness_on_taut : forall φ, IsPropTaut φ -> Provable φ.
Proof.
  intros φ Htaut.
  (* A0_valid gives validity; WeakCompleteness turns validity into derivability. *)
  apply WeakCompleteness.
  apply (A0_valid φ Htaut).
Qed.

(* Adequacy: provability iff validity. Forward direction via soundness. *)
Example ex_Adequacy_forward : forall φ, Provable φ -> valid φ.
Proof.
  intros φ Hprov.
  (* Either apply soundness directly or the Adequacy corollary from LTL/LTL.v *)
  apply soundness; exact Hprov.
Qed.

(* Adequacy: backward direction via Weak Completeness. *)
Example ex_Adequacy_backward : forall φ, valid φ -> Provable φ.
Proof.
  intros φ Hvalid.
  apply WeakCompleteness; exact Hvalid.
Qed.

(* Instance: If Ax1 instance is valid, it is provable by WeakCompleteness. *)
Example ex_WC_Ax1 : Provable (Ax1 (Atom 0) (Atom 1)).
Proof.
  apply WeakCompleteness.
  apply Ax1_valid.
Qed.

(* Instance: If Ax2 instance is valid, it is provable by WeakCompleteness. *)
Example ex_WC_Ax2 : Provable (Ax2 (Atom 0) (Atom 1)).
Proof.
  apply WeakCompleteness.
  apply Ax2_valid.
Qed.

(* Instance: If Ax3 instance is valid, it is provable by WeakCompleteness. *)
Example ex_WC_Ax3 : Provable (Ax3 (Atom 0)).
Proof.
  apply WeakCompleteness.
  apply Ax3_valid.
Qed.
