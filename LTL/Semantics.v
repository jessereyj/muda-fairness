From Coq Require Import Arith List.
Import ListNotations.
Require Import LTL.Syntax.

(* States and traces *)
Definition state := predicate -> Prop.

CoInductive trace : Type :=
| Trace : state -> trace -> trace.

Fixpoint trace_at (pi : trace) (i : nat) : state :=
  match pi with
  | Trace s pi' =>
      match i with
      | 0 => s
      | S j => trace_at pi' j
      end
  end.

(* Semantics *)
Fixpoint satisfies (pi : trace) (i : nat) (phi : LTL_formula) : Prop :=
  match phi with
  | Atom p          => trace_at pi i p
  | Not phi'        => ~ satisfies pi i phi'
  | And phi1 phi2   => satisfies pi i phi1 /\ satisfies pi i phi2
  | Or  phi1 phi2   => satisfies pi i phi1 \/ satisfies pi i phi2
  | Implies phi1 phi2 => ~ satisfies pi i phi1 \/ satisfies pi i phi2
  | Next phi'       => satisfies pi (S i) phi'
  | Always phi'     => forall j, j >= i -> satisfies pi j phi'
  | Eventually phi' => exists j, j >= i /\ satisfies pi j phi'
  | Until phi1 phi2 =>
      exists j, j >= i /\ satisfies pi j phi2 /\
                (forall k, i <= k < j -> satisfies pi k phi1)
  end.

(* Validity *)
Definition valid (phi : LTL_formula) : Prop :=
  forall pi i, satisfies pi i phi.

(* ASCII helper lemmas (no Unicode tokens in binders) *)
Lemma satisfies_implies_equiv :
  forall (pi : trace) (i : nat) (phi psi : LTL_formula),
    satisfies pi i (Implies phi psi)
    <-> (~ satisfies pi i phi \/ satisfies pi i psi).
Proof. intros; simpl; tauto. Qed.

Lemma satisfies_eventually_unfold :
  forall (pi : trace) (i : nat) (phi : LTL_formula),
    satisfies pi i (Eventually phi)
    <-> (exists j, j >= i /\ satisfies pi j phi).
Proof. intros; simpl; firstorder. Qed.

Lemma satisfies_always_unfold :
  forall (pi : trace) (i : nat) (phi : LTL_formula),
    satisfies pi i (Always phi)
    <-> (forall j, j >= i -> satisfies pi j phi).
Proof. intros; simpl; firstorder. Qed.
