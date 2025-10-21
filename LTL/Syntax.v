From Coq Require Import List Bool.
Import ListNotations.

(* ---- LTL syntax ---- *)

Definition predicate := nat.

Inductive LTL_formula : Type :=
  | Atom : predicate -> LTL_formula
  | Not  : LTL_formula -> LTL_formula
  | And  : LTL_formula -> LTL_formula -> LTL_formula
  | Or   : LTL_formula -> LTL_formula -> LTL_formula
  | Implies : LTL_formula -> LTL_formula -> LTL_formula
  | Next : LTL_formula -> LTL_formula
  | Always : LTL_formula -> LTL_formula
  | Eventually : LTL_formula -> LTL_formula
  | Until : LTL_formula -> LTL_formula -> LTL_formula.

(* Scoping & notations (use real symbols so at least one non-alnum is present) *)
Declare Scope LTL_scope.
Delimit Scope LTL_scope with LTL.

Notation "¬ φ"     := (Not φ)                   (at level 75, right associativity) : LTL_scope.
Notation "φ ∧ ψ"   := (And φ ψ)                 (at level 80, right associativity) : LTL_scope.
Notation "φ ∨ ψ"   := (Or φ ψ)                  (at level 85, right associativity) : LTL_scope.
Notation "φ → ψ"   := (Implies φ ψ)             (at level 90, right associativity) : LTL_scope.
Notation "'X' φ"     := (Next φ)                  (at level 75) : LTL_scope.
Notation "'G' φ"     := (Always φ)                (at level 75) : LTL_scope.
Notation "'F' φ"     := (Eventually φ)            (at level 75) : LTL_scope.
(* Avoid bare 'U'; give a symbolic wrapper so the notation has a symbol *)
Notation "φ ⟪U⟫ ψ" := (Until φ ψ)               (at level 85, right associativity) : LTL_scope.

(* (Optional) ASCII fallbacks, kept out of the default scope to avoid clashes *)
Notation "phi 'IMPLIES' psi" := (Implies phi psi) (at level 90, right associativity).
Notation "phi 'UNTIL' psi"   := (Until   phi psi) (at level 85, right associativity).
