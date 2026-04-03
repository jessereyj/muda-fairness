From Stdlib Require Import Arith.
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

Notation "σ ⊨[ i ] φ" := (satisfies σ i φ) (at level 70).
Notation "σ , i ⊨ φ" := (satisfies σ i φ) (at level 70, only printing).
Notation "σ ⊨ φ" := (models σ φ) (at level 70).
Notation "⊨ φ"    := (valid φ)     (at level 70).

Lemma satisfies_always_unfold :
  forall σ i φ,
    satisfies σ i (Always φ)
    <-> forall j, j >= i -> satisfies σ j φ.
Proof. intros; simpl; tauto. Qed.
