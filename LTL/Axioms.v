(* LTL/Axioms.v *)

From Stdlib Require Import List.
From LTL Require Import Syntax.

(* Abstract marker for classical propositional tautologies *)
Parameter IsPropTaut : LTL_formula -> Prop.

(* Schematic axiom schemas (syntactic forms) available to the proof system.
   Use constructor names (Next, Implies, Until, Or, And, Always) rather
   than notations to avoid depending on scope opening during parallel
   compilation. *)
Definition Ax1 (φ ψ : LTL_formula) : LTL_formula :=
  Implies (Next (Implies φ ψ)) (Implies (Next φ) (Next ψ)).

Definition Ax2 (φ ψ : LTL_formula) : LTL_formula :=
  Implies (Until φ ψ) (Or ψ (And φ (Next (Until φ ψ)))).

Definition Ax3 (φ : LTL_formula) : LTL_formula :=
  Implies (And φ (Next (Always φ))) (Always φ).

(* Proof system: inductive derivability predicate *)
Inductive Provable : LTL_formula -> Prop :=
| Pr_A0  : forall φ, IsPropTaut φ -> Provable φ
| Pr_A1  : forall φ ψ, Provable (Ax1 φ ψ)
| Pr_A2  : forall φ ψ, Provable (Ax2 φ ψ)
| Pr_A3  : forall φ,   Provable (Ax3 φ)
| Pr_MP  : forall φ ψ, Provable φ -> Provable (Implies φ ψ) -> Provable ψ
| Pr_Nec : forall φ, IsPropTaut φ -> Provable (Always φ).

Notation "⊢ φ" := (Provable φ) (at level 70).
