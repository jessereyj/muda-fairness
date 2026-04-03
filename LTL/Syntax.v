(* No Stdlib imports needed here; this file defines the LTL AST and notations. *)

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

(* Chapter 4 core grammar uses ¬, ∧, X, F, G. For convenience in proofs and
  specifications, we also include ∨ and → as additional connectives with their
  standard semantics (not as axioms). *)

Notation "¬ φ"     := (Not φ)                   (at level 75, right associativity) : LTL_scope.
Notation "φ ∧ ψ"   := (And φ ψ)                 (at level 80, right associativity) : LTL_scope.
Notation "φ ∨ ψ"   := (Or φ ψ)                  (at level 85, right associativity) : LTL_scope.
Notation "φ → ψ"   := (Implies φ ψ)             (at level 90, right associativity) : LTL_scope.
Notation "'X' φ"   := (Next φ)                  (at level 75) : LTL_scope.
Notation "'G' φ"   := (Always φ)                (at level 75) : LTL_scope.
Notation "'F' φ"   := (Eventually φ)            (at level 75) : LTL_scope.

Notation "phi 'IMPLIES' psi" := (Implies phi psi) (at level 90, right associativity).

Local Open Scope LTL_scope.