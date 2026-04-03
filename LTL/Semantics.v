From Stdlib Require Import Arith.
From LTL Require Import Syntax.

(** Panel index (thesis ↔ code)

  Chapter 4.1.2 (Semantics)
  - state: valuation v : PROP -> Prop
  - trace: infinite trace σ = (v0, v1, ...)
  - satisfies: satisfaction σ, i ⊨ φ
  - Notation σ ⊨ φ: shorthand for satisfaction at time 0
  - satisfies_always_unfold: unfolding rule for G/Always used in the Chapter 4 lift step
*)

Local Open Scope LTL_scope.
Local Open Scope nat_scope.

(* state: valuation v assigning truth to each predicate index. *)
Definition state := predicate -> Prop.

(* trace: infinite stream of states σ = (v0, v1, ...). *)
CoInductive trace : Type :=
| Trace : state -> trace -> trace.

(* trace_at: state at time i along σ (internal helper). *)
Local Fixpoint trace_at (σ : trace) (i : nat) : state :=
  match σ with
  | Trace s σ' =>
      match i with
      | 0   => s
      | S j => trace_at σ' j
      end
  end.

(* satisfies: semantic judgment σ, i ⊨ φ (Chapter 4 semantics). *)
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

(* models: satisfaction at time 0 (used for σ ⊨ φ). *)
Local Definition models (σ : trace) (φ : LTL_formula) : Prop := satisfies σ 0 φ.
Notation "σ ⊨ φ" := (models σ φ) (at level 70).

(* satisfies_always_unfold: unfolding principle for Always/G. *)
Lemma satisfies_always_unfold :
  forall σ i φ,
    satisfies σ i (Always φ)
    <-> forall j, j >= i -> satisfies σ j φ.
Proof. intros; simpl; tauto. Qed.
