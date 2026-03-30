(** Chapter 4 (Foundation Layer) — Section 4.1.1 (Syntax)

  This file defines the LTL language used throughout the development.

  Thesis: PROP = N, and formulas are built from atomic propositions using
  ¬, ∧, X, F, and G.

  Code: atomic propositions are indexed by `predicate := nat`.
*)
From Stdlib Require Import List Bool.
Import List.ListNotations.

Declare Scope LTL_scope.
Delimit Scope LTL_scope with LTL.

Definition predicate := nat.

Inductive LTL_formula : Type :=
  | Atom       : predicate -> LTL_formula
  | Not        : LTL_formula -> LTL_formula
  | And        : LTL_formula -> LTL_formula -> LTL_formula
  | Or         : LTL_formula -> LTL_formula -> LTL_formula
  | Implies    : LTL_formula -> LTL_formula -> LTL_formula
  | Next       : LTL_formula -> LTL_formula
  | Always     : LTL_formula -> LTL_formula
  | Eventually : LTL_formula -> LTL_formula.

Definition top : LTL_formula := Or (Atom 0) (Not (Atom 0)).


Notation "¬ φ"     := (Not φ)                   (at level 75, right associativity) : LTL_scope.
Notation "φ ∧ ψ"   := (And φ ψ)                 (at level 80, right associativity) : LTL_scope.
Notation "φ ∨ ψ"   := (Or φ ψ)                  (at level 85, right associativity) : LTL_scope.
Notation "φ → ψ"   := (Implies φ ψ)             (at level 90, right associativity) : LTL_scope.
Notation "'X' φ"   := (Next φ)                  (at level 75) : LTL_scope.
Notation "'G' φ"   := (Always φ)                (at level 75) : LTL_scope.
Notation "'F' φ"   := (Eventually φ)            (at level 75) : LTL_scope.

Notation "phi 'IMPLIES' psi" := (Implies phi psi) (at level 90, right associativity).

Local Open Scope LTL_scope.