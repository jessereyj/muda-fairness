From Stdlib Require Export Arith List Bool.
Local Open Scope bool_scope.

Class Eqb (A : Type) := {
  eqb : A -> A -> bool
}.

Class EqbSpec (A : Type) {eqb_instance : Eqb A} := {
  eqb_eq : forall a1 a2, eqb a1 a2 = true <-> a1 = a2
}.

Notation "x =? y" := (eqb x y) (at level 70) : bool_scope.

#[export] Instance nat_eqb : Eqb nat := { eqb := Nat.eqb }.
#[export] Instance nat_eqb_spec : EqbSpec nat.
Proof.
  constructor. apply Nat.eqb_eq.
Qed.
