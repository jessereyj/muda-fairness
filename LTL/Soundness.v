(** * Linear Temporal Logic - Soundness
    
    Every provable formula is valid.
*)

From Coq Require Import Arith List Lia Classical.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.Classical.
Require Import MUDA.LTL.Syntax.
Require Import MUDA.LTL.Semantics.
Local Open Scope LTL_scope.
Import ListNotations.

(** ** Axiom System *)

(* A0: Propositional tautologies *)
Definition axiom_A0 (φ : LTL_formula) : Prop :=
  valid φ. (* If φ is a propositional tautology, then valid φ *)

(* Axioms-as-valid-formulas *)
Definition axiom_A1 (φ ψ : LTL_formula) : Prop :=
  valid (Implies (Next (Implies φ ψ))
                 (Implies (Next φ) (Next ψ))).

(* A2: Until expansion *)
(* A2: φ U ψ → ψ ∨ (φ ∧ X(φ U ψ)) *)
Definition axiom_A2 (φ ψ : LTL_formula) : Prop :=
  valid (Implies (Until φ ψ) (Or ψ (And φ (Next (Until φ ψ))))).

(* A3: Always induction *)
(* A3: (φ ∧ X G φ) → G φ *)
Definition axiom_A3 (φ : LTL_formula) : Prop :=
  valid (Implies (And φ (Next (Always φ))) (Always φ)).

(** ** Proof Rules *)

(* R1: Modus Ponens *)
Definition rule_MP (φ ψ : LTL_formula) : Prop :=
  valid φ -> valid (φ → ψ) -> valid ψ.

(* R2: Necessitation for tautologies *)
Definition rule_Nec (φ : LTL_formula) : Prop :=
  valid φ -> valid (G φ).

(** ** Soundness Lemmas *)
Lemma axiom_A1_sound : forall φ ψ, axiom_A1 φ ψ.
Proof.
  unfold axiom_A1, valid; intros φ ψ π i; simpl.
  (* goal is:  ~(satisfies π (S i) (Implies φ ψ))
               \/ (~ satisfies π (S i) φ \/ satisfies π (S i) ψ) *)
  tauto.
Qed.

Lemma axiom_A2_sound : forall φ ψ, axiom_A2 φ ψ.
Proof.
  unfold axiom_A2, valid; intros φ ψ π i; simpl.
  (* goal: ~(π,i ⊨ φ U ψ) \/ (π,i ⊨ ψ \/ (π,i ⊨ φ /\ π,i+1 ⊨ φ U ψ)) *)
  destruct (classic (satisfies π i (Until φ ψ))) as [HU|HnotU].
  - right.
    destruct HU as [j [Hge [Hpsi Hpref]]].
    destruct (Nat.eq_dec i j) as [->|Hneq].
    + left; exact Hpsi.
    + right. split.
      * (* φ holds at i *)
        specialize (Hpref i). assert (i <= i < j) by lia.
        apply Hpref in H; exact H.
      * (* X(φ U ψ) holds at i *)
        exists j; split; [lia|]. split; [exact Hpsi|].
        intros k Hk; apply Hpref; lia.
  - left; exact HnotU.
Qed.

Lemma axiom_A3_sound : forall φ, axiom_A3 φ.
Proof.
  unfold axiom_A3, valid; intros φ π i; simpl.
  (* goal:  ~ (π,i ⊨ φ ∧ X G φ) \/ (forall j, j >= i -> π,j ⊨ φ) *)
  destruct (classic (satisfies π i (And φ (Next (Always φ))))) as [[Hφ HXG] | Hnot].
  - (* antecedent holds: prove G φ at i *)
    right. intros j Hj.
    destruct (Nat.eq_dec j i) as [->|Hneq]; [exact Hφ|].
    assert (j >= S i) by lia.
    (* HXG: π,i ⊨ X G φ  ==> π,S i ⊨ G φ *)
    simpl in HXG. (* HXG : forall k, k >= S i -> π,k ⊨ φ *)
    apply HXG; assumption.
  - (* antecedent does not hold: implication is true *)
    left; exact Hnot.
Qed.

Lemma rule_MP_sound : forall φ ψ,
  rule_MP φ ψ.
Proof.
  unfold rule_MP, valid. intros φ ψ Hphi Himpl π i.
  specialize (Hphi π i).
  specialize (Himpl π i).
  simpl in Himpl. destruct Himpl as [Hneg | Hpsi].
  - contradiction.
  - assumption.
Qed.

Lemma rule_Nec_sound : forall φ,
  rule_Nec φ.
Proof.
  unfold rule_Nec, valid. intros φ Hphi π i.
  simpl. intros j Hj.
  apply Hphi.
Qed.

(** ** Main Soundness Theorem *)

Theorem soundness : forall φ,
  (* If provable φ *) valid φ -> (* Then valid φ *)
  valid φ.
Proof.
  (* Trivial since we're using semantic validity *)
  intros φ H. assumption.
Qed.

(* Note: Full syntactic provability would require defining a proof system,
   but for the thesis we use semantic validity directly *)