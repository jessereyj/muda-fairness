(* Examples/LogicalSoundness.v — sanity checks for LTL/Soundness.v *)
From LTL Require Import Syntax Semantics Axioms Soundness.

Local Open Scope LTL_scope.

(* Simple closed-form instances to exercise Ax1/Ax2/Ax3 validity lemmas. *)
Example ex_Ax1_valid_implication : valid (Ax1 (Atom 0) (Atom 1)).
Proof. apply Ax1_valid. Qed.

Example ex_Ax2_valid_until : valid (Ax2 (Atom 0) (Atom 1)).
Proof. apply Ax2_valid. Qed.

Example ex_Ax3_valid_induction : valid (Ax3 (Atom 0)).
Proof. apply Ax3_valid. Qed.

(* Rule soundness: Modus Ponens and Necessitation (restricted). *)
Example ex_MP_valid : forall φ ψ, valid φ -> valid (φ → ψ) -> valid ψ.
Proof.
  intros φ ψ Hφ Himp.
  apply (MP_valid φ ψ); assumption.
Qed.

Example ex_Nec_valid_taut : forall φ, IsPropTaut φ -> valid (G φ).
Proof. intros; apply Nec_valid_taut; assumption. Qed.

(* Main theorem: any derivable formula is valid. We demonstrate on a tautology. *)
Example ex_soundness_on_taut : forall φ, IsPropTaut φ -> valid φ.
Proof.
  intros φ Htaut.
  (* A0 gives Provable φ; soundness yields validity. *)
  (* In this development, A0_valid is assumed; alternatively show Provable φ and apply soundness. *)
  apply (A0_valid φ Htaut).
Qed.

(* Bridge demonstration: from Provable to valid via soundness. *)
Example ex_provable_implies_valid : forall φ, Provable φ -> valid φ.
Proof. intros φ H; apply soundness; exact H. Qed.

(* Note: Direct axiom-instance constructors (A1/A2/A3 : Provable ...) may be
   internal names in Axioms.v. Since they are not exported here, we validate
   A1/A2/A3 via their semantic lemmas Ax1_valid/Ax2_valid/Ax3_valid above. *)
