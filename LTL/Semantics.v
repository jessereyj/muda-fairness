(** Chapter 4 (Foundation Layer) — Section 4.1.2 (Semantics)

  This file defines satisfaction `satisfies` of LTL formulas over infinite
  traces and proves the standard unfold lemmas for F and G.

  Note: the thesis uses boolean valuations v : PROP -> {true,false}; this
  mechanization uses `state := predicate -> Prop`, which is equivalent for
  expressing truth of atomic propositions.
*)
From Stdlib Require Import List Bool Arith Lia.
Import List.ListNotations.
From LTL Require Import Syntax.

Local Open Scope LTL_scope.
Local Open Scope nat_scope.

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
  end.

Definition models (σ : trace) (φ : LTL_formula) : Prop := satisfies σ 0 φ.
Definition valid  (φ : LTL_formula) : Prop := forall σ i, satisfies σ i φ.

Notation "σ ⊨ φ" := (models σ φ) (at level 70).
Notation "⊨ φ"    := (valid φ)     (at level 70).

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
Qed.