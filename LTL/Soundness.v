(** Chapter 4 (Foundation Layer) — Section 4.1.5 (Meta-theoretic Properties)

  Soundness: if ⊢ φ then ⊨ φ.

  The only meta-assumption is A0_valid, which treats propositional tautologies
  as semantically valid (as in the thesis discussion).
*)
From Stdlib Require Import Arith List Lia Classical.
Import ListNotations.
From LTL Require Import Syntax Semantics Axioms.

Local Open Scope LTL_scope.
Local Open Scope nat_scope.

Axiom A0_valid : forall φ, IsPropTaut φ -> valid φ.

Lemma Ax1_valid : forall φ ψ, valid (Ax1 φ ψ).
Proof.
  unfold valid, Ax1; intros φ ψ σ i; simpl; tauto.
Qed.

Lemma Ax2_valid : forall φ ψ, valid (Ax2 φ ψ).
Proof.
  unfold valid, Ax2; intros φ ψ σ i; simpl.
  destruct (classic (satisfies σ i (Until φ ψ))) as [HU|HnU].
  - right.
    (* Use the -> direction of the equivalence *)
    apply (proj1 (satisfies_until_unfold σ i φ ψ)) in HU.
    exact HU.
  - left; exact HnU.
Qed.

Lemma Ax3_valid : forall φ, valid (Ax3 φ).
Proof.
  unfold valid, Ax3; intros φ σ i; simpl.
  destruct (classic (satisfies σ i (And φ (Next (Always φ))))) as [H | Hnot].
  - (* antecedent holds: unpack and prove G φ *)
    simpl in H. destruct H as [Hφ HXG].
    right. intros j Hj.
    destruct (Nat.eq_dec j i) as [->|Hneq].
    + exact Hφ.
    + assert (j >= S i) by lia.
      (* HXG : satisfies σ (S i) (Always φ) ≡ forall k >= S i, satisfies σ k φ *)
      simpl in HXG. apply HXG; assumption.
  - (* antecedent false -> implication true *)
    left; exact Hnot.
Qed.

Lemma MP_valid :
  forall φ ψ, valid φ -> valid (φ → ψ) -> valid ψ.
Proof.
  unfold valid; intros φ ψ Hφ Himp σ i.
  specialize (Hφ σ i). specialize (Himp σ i).
  simpl in Himp. destruct Himp as [Hnot | Hpsi]; [contradiction|assumption].
Qed.

Lemma Nec_valid_taut :
  forall φ, IsPropTaut φ -> valid (G φ).
Proof.
  intros φ H σ i. simpl. intros j Hj.
  (* A0_valid gives validity at every index, hence G φ holds. *)
  apply (A0_valid φ H).
Qed.

Theorem soundness :
  forall φ, Provable φ -> valid φ.
Proof.
  intros φ H; induction H.
  - (* A0 *) now apply A0_valid.
  - (* A1 *) apply Ax1_valid.
  - (* A2 *) apply Ax2_valid.
  - (* A3 *) apply Ax3_valid.
  - (* MP *) eauto using MP_valid.
  - (* Nec (restricted) *) now apply Nec_valid_taut.
Qed.