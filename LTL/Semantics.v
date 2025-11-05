(* LTL/Semantics.v *)
From Stdlib Require Import List Bool Arith.
From Stdlib Require Import Lia.
Import List.ListNotations.

From LTL Require Import Syntax.    (* was MUDA.LTL or LTL.Syntax *)

Local Open Scope LTL_scope.
Local Open Scope nat_scope.

(* ----------------------------- *)
(* States and ω-traces           *)
(* ----------------------------- *)

Definition state := predicate -> Prop.

CoInductive trace : Type :=
| Trace : state -> trace -> trace.

Fixpoint trace_at (σ : trace) (i : nat) : state :=
  match σ with
  | Trace s σ' =>
      match i with
      | 0   => s
      | S j => trace_at σ' j
      end
  end.

(* ----------------------------- *)
(* Semantics                     *)
(* ----------------------------- *)

Fixpoint satisfies (σ : trace) (i : nat) (φ : LTL_formula) : Prop :=
  match φ with
  | Atom p             => trace_at σ i p
  | Not φ'             => ~ satisfies σ i φ'
  | And φ₁ φ₂          => satisfies σ i φ₁ /\ satisfies σ i φ₂
  | Or  φ₁ φ₂          => satisfies σ i φ₁ \/ satisfies σ i φ₂
  | Implies φ₁ φ₂      => ~ satisfies σ i φ₁ \/ satisfies σ i φ₂
  | Next φ'            => satisfies σ (S i) φ'
  | Always φ'          => forall j, j >= i -> satisfies σ j φ'
  | Eventually φ'      => exists j, j >= i /\ satisfies σ j φ'
  | Until φ₁ φ₂        =>
      exists j, j >= i /\ satisfies σ j φ₂ /\
                (forall k, i <= k < j -> satisfies σ k φ₁)
  end.

Definition models (σ : trace) (φ : LTL_formula) : Prop := satisfies σ 0 φ.
Definition valid  (φ : LTL_formula) : Prop := forall σ i, satisfies σ i φ.

Notation "σ ⊨ φ" := (models σ φ) (at level 70).
Notation "⊨ φ"    := (valid φ)     (at level 70).

(* ----------------------------- *)
(* Unfold and equivalence lemmas  *)
(* ----------------------------- *)

Lemma satisfies_eventually_unfold :
  forall σ i φ,
    satisfies σ i (Eventually φ)
    <-> exists j, j >= i /\ satisfies σ j φ.
Proof. intros; simpl; tauto. Qed.

Lemma satisfies_always_unfold :
  forall σ i φ,
    satisfies σ i (Always φ)
    <-> forall j, j >= i -> satisfies σ j φ.
Proof. intros; simpl; tauto. Qed.

Lemma satisfies_until_unfold :
  forall σ i φ ψ,
    satisfies σ i (Until φ ψ)
    <-> (satisfies σ i ψ \/
         (satisfies σ i φ /\ satisfies σ (S i) (Until φ ψ))).
Proof.
  intros σ i φ ψ; split.
  - (* → *)
    simpl. intros (j & Hj & Hψ & Hseg).
    destruct (Nat.eq_dec j i) as [Heq|Hneq].
    + subst; left; exact Hψ.
    + assert (i < j) as Hlt by lia.
      right. split.
      * specialize (Hseg i); apply Hseg; lia.
      * simpl. exists j. split; [lia|]. split; [assumption|].
        intros k Hk; apply Hseg; lia.
  - (* ← *)
    simpl. intros [Hψ | [Hφ Hnext]].
    + exists i; repeat split; try lia; exact Hψ.
    + simpl in Hnext.
      destruct Hnext as (j & Hj & Hψj & HsegSi).
      exists j; repeat split; try lia; [assumption|].
      intros k Hk.
      destruct (Nat.eq_dec k i) as [->|Hneq]; [exact Hφ|].
      apply HsegSi; lia.
Qed.


Lemma satisfies_shift_tail :
  forall (s : state) (σ' : trace) (i : nat) (φ : LTL_formula),
    satisfies (Trace s σ') (S i) φ <-> satisfies σ' i φ.
Proof.
  intros s σ' i φ; revert s σ' i.
  induction φ as
      [ p                                   (* Atom *)
      | φ IHφ                               (* Not  *)
      | φ1 IH1 φ2 IH2                       (* And  *)
      | φ1 IH1 φ2 IH2                       (* Or   *)
      | φ1 IH1 φ2 IH2                       (* Implies *)
      | φ IHφ                               (* Next *)
      | φ IHφ                               (* Always *)
      | φ IHφ                               (* Eventually *)
      | φ1 IH1 φ2 IH2                       (* Until *)
      ]; intros s0 σ0 i0; simpl.
  - (* Atom *)
    tauto.
  - (* Not *)
    rewrite IHφ; tauto.
  - (* And *)
    rewrite IH1, IH2; tauto.
  - (* Or *)
    rewrite IH1, IH2; tauto.
  - (* Implies *)
    rewrite IH1, IH2; tauto.
  - (* Next *)
    specialize (IHφ s0 σ0 (S i0)); exact IHφ.
  - (* Always (G) *)
    split.
    + (* → : head at S i0 ⟹ tail at i0 *)
      intros H j Hj.
  specialize (H (S j)).
  assert (S j >= S i0) as H0 by lia.
  specialize (H H0).
      now rewrite (IHφ s0 σ0 j) in H.
    + (* ← : tail at i0 ⟹ head at S i0 *)
      intros H j Hj.
  destruct j as [|k]; [lia|].
  assert (k >= i0) as H0 by (apply le_S_n; exact Hj).
  specialize (H k H0).
      apply (proj2 (IHφ s0 σ0 k)) in H.
      exact H.
  - (* Eventually (F) *)
    split.
    + (* → *)
      intros (j & Hj & Hsat).
      destruct j as [|k]; [lia|].
      exists k. split; [apply le_S_n in Hj; exact Hj|].
      simpl in Hsat.
      apply (proj1 (IHφ s0 σ0 k)) in Hsat. exact Hsat.
    + (* ← *)
      intros (k & Hk & Hsat0).
      exists (S k). split; [lia|].
      apply (proj2 (IHφ s0 σ0 k)); exact Hsat0.
  - (* Until (U) *)
    split.
    + (* → *)
      intros (j & Hj & Hψ & Hseg).
      destruct j as [|k]; [lia|].
      exists k. repeat split; try (apply le_S_n in Hj; exact Hj).
      * (* shift ψ from head at S k to tail at k *)
        simpl in Hψ. apply (proj1 (IH2 s0 σ0 k)) in Hψ. exact Hψ.
      * (* shift the segment *)
        intros k0 Hrange.
  specialize (Hseg (S k0)).
  assert (S i0 <= S k0 < S k) as H0 by lia.
  specialize (Hseg H0).
        apply (proj1 (IH1 s0 σ0 k0)) in Hseg. exact Hseg.
    + (* ← *)
      intros (k & Hk & Hψ0 & Hseg0).
      exists (S k). repeat split; try lia.
      * (* shift ψ from tail at k to head at S k *)
        apply (proj2 (IH2 s0 σ0 k)) in Hψ0. exact Hψ0.
      * (* for any j with i0 ≤ j < S k *)
        intros j Hj.
  destruct j as [|k']; [lia|].
  assert (i0 <= k' < k) as Hrange by lia.
  specialize (Hseg0 k' Hrange).
        apply (proj2 (IH1 s0 σ0 k')) in Hseg0. exact Hseg0.
Qed.