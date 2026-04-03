(* No Stdlib imports needed here; this file defines the LTL AST and notations. *)

(** Panel index (thesis ↔ code)

  Chapter 4.1.1 (Syntax)
  - predicate: PROP implemented as nat indices
  - LTL_formula: LTL grammar (Atom, ¬, ∧, ∨, →, X, F, G)
  - Notation block: surface syntax used in docs and proofs
*)

Declare Scope LTL_scope.
Delimit Scope LTL_scope with LTL.

(* predicate: propositional variables (PROP) are represented by nat indices. *)
Definition predicate := nat.

(* LTL_formula: abstract syntax tree for LTL formulas over predicates. *)
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

(* Notation block: surface syntax used throughout Chapter 4 proofs/specs. *)
Notation "¬ φ"     := (Not φ)                   (at level 75, right associativity) : LTL_scope.
Notation "φ ∧ ψ"   := (And φ ψ)                 (at level 80, right associativity) : LTL_scope.
Notation "φ ∨ ψ"   := (Or φ ψ)                  (at level 85, right associativity) : LTL_scope.
Notation "φ → ψ"   := (Implies φ ψ)             (at level 90, right associativity) : LTL_scope.
Notation "'X' φ"   := (Next φ)                  (at level 75) : LTL_scope.
Notation "'G' φ"   := (Always φ)                (at level 75) : LTL_scope.
Notation "'F' φ"   := (Eventually φ)            (at level 75) : LTL_scope.

Notation "phi 'IMPLIES' psi" := (Implies phi psi) (at level 90, right associativity).

Local Open Scope LTL_scope.