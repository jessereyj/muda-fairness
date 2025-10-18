(**************************************************************************)
(* Prelude.v - Common definitions and notations for MUDA project         *)
(* Coq 8.18.0 compatible                                                  *)
(* NO ADMITS - Complete                                                   *)
(**************************************************************************)

From Coq Require Export
  Arith
  Lia
  Bool
  List
  Relations
  Wellfounded
  Program.Basics
  Program.Wf.

Export ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Bullet Behavior "Strict Subproofs".

(** * Basic Type Aliases *)

Definition price := nat.
Definition qty := nat.
Definition timestamp := nat.
Definition agent_id := nat.

(** * Option monad operations *)

Definition option_map {A B : Type} (f : A -> B) (o : option A) : option B :=
  match o with
  | Some x => Some (f x)
  | None => None
  end.

Definition option_bind {A B : Type} (o : option A) (f : A -> option B) : option B :=
  match o with
  | Some x => f x
  | None => None
  end.

Notation "x >>= f" := (option_bind x f) (at level 50, left associativity).
Notation "f <$> x" := (option_map f x) (at level 40, left associativity).

(** * List utilities *)

(** Find element satisfying predicate *)
Fixpoint find {A : Type} (f : A -> bool) (l : list A) : option A :=
  match l with
  | [] => None
  | x :: xs => if f x then Some x else find f xs
  end.

(** Filter list by predicate *)
Fixpoint filter {A : Type} (f : A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if f x then x :: filter f xs else filter f xs
  end.

(** Check if all elements satisfy predicate *)
Fixpoint forallb {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => f x && forallb f xs
  end.

(** Check if any element satisfies predicate *)
Fixpoint existsb {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => false
  | x :: xs => f x || existsb f xs
  end.

(** Remove duplicates (requires decidable equality) *)
Fixpoint dedup {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) 
  (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => 
      if existsb (fun y => if eq_dec x y then true else false) xs
      then dedup eq_dec xs
      else x :: dedup eq_dec xs
  end.

(** * Comparison utilities *)

Definition nat_leb (n m : nat) : bool := n <=? m.
Definition nat_ltb (n m : nat) : bool := n <? m.
Definition nat_eqb (n m : nat) : bool := n =? m.

(** * Relation utilities *)

(** Transitive closure *)
Inductive trans_clos {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| tc_step : forall x y, R x y -> trans_clos R x y
| tc_trans : forall x y z, trans_clos R x y -> trans_clos R y z -> trans_clos R x z.

(** Reflexive transitive closure *)
Inductive refl_trans_clos {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| rtc_refl : forall x, refl_trans_clos R x x
| rtc_step : forall x y, R x y -> refl_trans_clos R x y
| rtc_trans : forall x y z, 
    refl_trans_clos R x y -> refl_trans_clos R y z -> refl_trans_clos R x z.

(** * Decidability type class *)

Class Decidable (P : Prop) := {
  decide : {P} + {~P}
}.

Notation "'decide' P" := (@decide P _) (at level 10).

(** Instances for basic decidable propositions *)

#[export] Instance nat_eq_dec (n m : nat) : Decidable (n = m).
Proof.
  constructor. apply Nat.eq_dec.
Defined.

#[export] Instance nat_le_dec (n m : nat) : Decidable (n <= m).
Proof.
  constructor. apply le_dec.
Defined.

#[export] Instance nat_lt_dec (n m : nat) : Decidable (n < m).
Proof.
  constructor. apply lt_dec.
Defined.

#[export] Instance bool_eq_dec (b1 b2 : bool) : Decidable (b1 = b2).
Proof.
  constructor. decide equality.
Defined.

#[export] Instance and_dec {P Q : Prop} 
  `{Decidable P} `{Decidable Q} : Decidable (P /\ Q).
Proof.
  constructor.
  destruct (decide P); destruct (decide Q).
  - left. split; assumption.
  - right. intros [_ HQ]. contradiction.
  - right. intros [HP _]. contradiction.
  - right. intros [HP _]. contradiction.
Defined.

#[export] Instance or_dec {P Q : Prop}
  `{Decidable P} `{Decidable Q} : Decidable (P \/ Q).
Proof.
  constructor.
  destruct (decide P); destruct (decide Q).
  - left. left. assumption.
  - left. left. assumption.
  - left. right. assumption.
  - right. intros [HP|HQ]; contradiction.
Defined.

#[export] Instance not_dec {P : Prop}
  `{Decidable P} : Decidable (~ P).
Proof.
  constructor.
  destruct (decide P).
  - right. intros Hn. contradiction.
  - left. assumption.
Defined.

(** * Common lemmas *)

Lemma nat_max_lub : forall n m p,
  n <= p -> m <= p -> Nat.max n m <= p.
Proof. intros. lia. Qed.

Lemma nat_min_glb : forall n m p,
  p <= n -> p <= m -> p <= Nat.min n m.
Proof. intros. lia. Qed.

Lemma nat_max_comm : forall n m,
  Nat.max n m = Nat.max m n.
Proof. intros. lia. Qed.

Lemma nat_min_comm : forall n m,
  Nat.min n m = Nat.min m n.
Proof. intros. lia. Qed.

Lemma nat_max_assoc : forall n m p,
  Nat.max n (Nat.max m p) = Nat.max (Nat.max n m) p.
Proof. intros. lia. Qed.

Lemma nat_min_assoc : forall n m p,
  Nat.min n (Nat.min m p) = Nat.min (Nat.min n m) p.
Proof. intros. lia. Qed.

(** * List lemmas *)

Lemma In_app_iff : forall {A : Type} (x : A) (l1 l2 : list A),
  In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof. intros. apply in_app_iff. Qed.

(* In_cons_iff removed - use simpl or in_cons from stdlib instead *)

Lemma length_app : forall {A : Type} (l1 l2 : list A),
  length (l1 ++ l2) = length l1 + length l2.
Proof. intros. apply app_length. Qed.

Lemma app_nil_l : forall {A : Type} (l : list A),
  [] ++ l = l.
Proof. reflexivity. Qed.

Lemma app_nil_r : forall {A : Type} (l : list A),
  l ++ [] = l.
Proof. intros. apply List.app_nil_r. Qed.

Lemma app_assoc : forall {A : Type} (l1 l2 l3 : list A),
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof. intros. apply List.app_assoc. Qed.

(** * Boolean reflection *)

Lemma reflect_iff : forall (P : Prop) (b : bool),
  (P <-> b = true) -> (if b then P else ~P).
Proof.
  intros P b [H1 H2].
  destruct b.
  - apply H2. reflexivity.
  - intro HP. apply H1 in HP. discriminate.
Qed.

Lemma bool_dec : forall b : bool, {b = true} + {b = false}.
Proof. destruct b; [left|right]; reflexivity. Defined.


(** * Notation scopes *)

Declare Scope muda_scope.
Delimit Scope muda_scope with muda.

(** Bind muda_scope to common operations *)
Bind Scope muda_scope with price.
Bind Scope muda_scope with qty.
Bind Scope muda_scope with timestamp.

Open Scope muda_scope.

(** * Useful hints *)

#[export] Hint Resolve Nat.le_refl : core.
#[export] Hint Resolve Nat.lt_irrefl : core.
#[export] Hint Resolve Nat.le_trans : core.
#[export] Hint Resolve Nat.lt_trans : core.
#[export] Hint Resolve app_nil_r : core.
#[export] Hint Resolve app_assoc : core.
#[export] Hint Rewrite @app_nil_l @app_nil_r : list_simpl.

(** * Pretty-printing hints *)

(** Makes proof terms more readable *)
Set Printing Depth 100.
Set Printing Width 80.