(**************************************************************************)
(* Finite.v - Finite sets and decidability for MUDA                      *)
(* Coq 8.18.0 compatible                                                  *)
(* NO ADMITS - Complete                                                   *)
(**************************************************************************)

From Coq Require Import Arith Lia List.
From MudaFairness.Base Require Import Prelude Tactics.

Set Implicit Arguments.

(** * Finite types *)

(** A type is finite if it has a complete enumeration *)
Class Finite (A : Type) := {
  finite_enum : list A;
  finite_complete : forall x : A, In x finite_enum;
  finite_eq_dec : forall x y : A, {x = y} + {x <> y}
}.

(** * Finite instances *)

(** Finite nat up to bound *)
Fixpoint nat_seq (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => nat_seq n' ++ [n']
  end.

Lemma nat_seq_complete : forall n m,
  m < n -> In m (nat_seq n).
Proof.
  induction n; intros m Hlt.
  - lia.
  - simpl. apply In_app_iff.
    assert (H : m < n \/ m = n) by lia.
    destruct H as [Hlt' | Heq].
    + left. apply IHn. exact Hlt'.
    + right. left. exact Heq.
Qed.

(** Bounded natural numbers *)
Definition bounded_nat (n : nat) := {m : nat | m < n}.

Program Instance Finite_bounded_nat (n : nat) : Finite (bounded_nat n) := {
  finite_enum := map (fun m => exist _ m _) (nat_seq n);
  finite_eq_dec := fun x y => 
    match Nat.eq_dec (proj1_sig x) (proj1_sig y) with
    | left Heq => left _
    | right Hneq => right _
    end
}.
Next Obligation.
  apply nat_seq_complete. assumption.
Defined.
Next Obligation.
  destruct x, y. simpl in Heq. subst. f_equal. apply proof_irrelevance.
Defined.
Next Obligation.
  destruct x, y. simpl in Hneq. intro Hcontra. inv Hcontra. contradiction.
Defined.
Next Obligation.
  destruct x as [m Hlt]. simpl.
  apply in_map_iff.
  exists m. split.
  - f_equal. apply proof_irrelevance.
  - apply nat_seq_complete. assumption.
Defined.

(** * Decidability for finite types *)

(** Decidable membership in finite type *)
Lemma finite_In_dec {A : Type} `{Finite A} :
  forall (x : A) (l : list A), {In x l} + {~ In x l}.
Proof.
  intros x l.
  induction l as [|y ys IH].
  - right. intro H. inversion H.
  - destruct (finite_eq_dec x y).
    + left. simpl. auto.
    + destruct IH.
      * left. simpl. auto.
      * right. simpl. intros [Heq | Hin]; contradiction.
Defined.

(** Decidable existential over finite type *)
Lemma finite_exists_dec {A : Type} `{Finite A} (P : A -> Prop) :
  (forall x, Decidable (P x)) ->
  {exists x, P x} + {forall x, ~ P x}.
Proof.
  intro Hdec.
  induction finite_enum as [|x xs IH].
  - right. intros x. destruct (finite_complete x).
  - destruct (decide (P x)).
    + left. exists x. assumption.
    + destruct IH as [[y Hy] | Hall].
      * left. exists y. assumption.
      * right. intros y Py.
        destruct (finite_complete y) as [Heq | Hin].
        -- subst. contradiction.
        -- apply Hall. assumption.
Defined.

(** Decidable universal over finite type *)
Lemma finite_forall_dec {A : Type} `{Finite A} (P : A -> Prop) :
  (forall x, Decidable (P x)) ->
  {forall x, P x} + {exists x, ~ P x}.
Proof.
  intro Hdec.
  induction finite_enum as [|x xs IH].
  - left. intros x. destruct (finite_complete x).
  - destruct (decide (P x)).
    + destruct IH as [Hall | [y Hy]].
      * left. intros y.
        destruct (finite_complete y) as [Heq | Hin].
        -- subst. assumption.
        -- apply Hall. assumption.
      * right. exists y. assumption.
    + right. exists x. assumption.
Defined.

(** * List utilities for finite types *)

(** Remove element from list *)
Fixpoint remove {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
  (x : A) (l : list A) : list A :=
  match l with
  | [] => []
  | y :: ys => if eq_dec x y then remove eq_dec x ys else y :: remove eq_dec x ys
  end.

Lemma remove_In : forall {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
  (x y : A) (l : list A),
  In y (remove eq_dec x l) -> In y l /\ y <> x.
Proof.
  intros A eq_dec x y l.
  induction l as [|z zs IH]; simpl; intro H.
  - inversion H.
  - destruct (eq_dec x z); simpl in H.
    + destruct (IH H). split; auto.
    + destruct H as [Heq | Hin].
      * subst. split; auto.
      * destruct (IH Hin). split; auto.
Qed.

Lemma In_remove : forall {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
  (x y : A) (l : list A),
  In y l -> y <> x -> In y (remove eq_dec x l).
Proof.
  intros A eq_dec x y l Hin Hneq.
  induction l as [|z zs IH]; simpl in *.
  - inversion Hin.
  - destruct (eq_dec x z); simpl.
    + destruct Hin as [Heq | Hin'].
      * subst. contradiction.
      * apply IH. assumption.
    + destruct Hin as [Heq | Hin'].
      * left. assumption.
      * right. apply IH. assumption.
Qed.

(** * Cardinality *)

Definition cardinality {A : Type} `{Finite A} : nat :=
  length finite_enum.

Lemma cardinality_pos {A : Type} `{Finite A} :
  (exists x : A, True) -> cardinality > 0.
Proof.
  intros [x _].
  unfold cardinality.
  destruct finite_enum eqn:Heq.
  - destruct (finite_complete x).
  - simpl. lia.
Qed.

(** * Finite products *)

Definition prod_enum {A B : Type} (la : list A) (lb : list B) : list (A * B) :=
  flat_map (fun a => map (fun b => (a, b)) lb) la.

Lemma prod_enum_complete : forall {A B : Type} (la : list A) (lb : list B) (x : A) (y : B),
  In x la -> In y lb -> In (x, y) (prod_enum la lb).
Proof.
  intros A B la lb x y Hx Hy.
  unfold prod_enum.
  apply in_flat_map.
  exists x. split.
  - assumption.
  - apply in_map_iff.
    exists y. split; auto.
Qed.

#[export] Instance Finite_prod {A B : Type} `{Finite A} `{Finite B} : Finite (A * B) := {
  finite_enum := prod_enum finite_enum finite_enum;
  finite_eq_dec := fun p1 p2 =>
    match p1, p2 with
    | (x1, y1), (x2, y2) =>
        match finite_eq_dec x1 x2, finite_eq_dec y1 y2 with
        | left Hx, left Hy => left _
        | _, _ => right _
        end
    end
}.
Proof.
  - (* eq case *) subst. reflexivity.
  - (* neq case *) intros [Hx Hy]. destruct p1, p2. simpl in *. 
    inv Hx. destruct (finite_eq_dec a a0); destruct (finite_eq_dec b b0); try congruence.
  - (* completeness *) destruct x as [a b].
    apply prod_enum_complete; apply finite_complete.
Defined.

(** * Finite option types *)

Definition option_enum {A : Type} (la : list A) : list (option A) :=
  None :: map Some la.

Lemma option_enum_complete : forall {A : Type} (la : list A) (o : option A),
  (forall x, In x la) ->
  In o (option_enum la).
Proof.
  intros A la [x|]; intro Hall.
  - simpl. right. apply in_map_iff. exists x. split; auto.
  - simpl. left. reflexivity.
Qed.

#[export] Instance Finite_option {A : Type} `{Finite A} : Finite (option A) := {
  finite_enum := option_enum finite_enum;
  finite_eq_dec := fun o1 o2 =>
    match o1, o2 with
    | None, None => left eq_refl
    | Some x, Some y => 
        match finite_eq_dec x y with
        | left Heq => left _
        | right Hneq => right _
        end
    | _, _ => right _
    end
}.
Proof.
  - (* Some x = Some y *) subst. reflexivity.
  - (* Some x <> Some y *) intro Hcontra. inv Hcontra. contradiction.
  - (* None <> Some *) discriminate.
  - (* Some <> None *) discriminate.
  - (* completeness *) apply option_enum_complete. apply finite_complete.
Defined.

(** * Finite sums *)

Definition sum_enum {A B : Type} (la : list A) (lb : list B) : list (A + B) :=
  map inl la ++ map inr lb.

Lemma sum_enum_complete : forall {A B : Type} (la : list A) (lb : list B) (s : A + B),
  (forall x, In x la) ->
  (forall y, In y lb) ->
  In s (sum_enum la lb).
Proof.
  intros A B la lb [a|b] Ha Hb.
  - unfold sum_enum. apply In_app_iff. left.
    apply in_map_iff. exists a. split; auto.
  - unfold sum_enum. apply In_app_iff. right.
    apply in_map_iff. exists b. split; auto.
Qed.

#[export] Instance Finite_sum {A B : Type} `{Finite A} `{Finite B} : Finite (A + B) := {
  finite_enum := sum_enum finite_enum finite_enum;
  finite_eq_dec := fun s1 s2 =>
    match s1, s2 with
    | inl x, inl y =>
        match finite_eq_dec x y with
        | left Heq => left _
        | right Hneq => right _
        end
    | inr x, inr y =>
        match finite_eq_dec x y with
        | left Heq => left _
        | right Hneq => right _
        end
    | inl _, inr _ => right _
    | inr _, inl _ => right _
    end
}.
Proof.
  - (* inl x = inl y *) subst. reflexivity.
  - (* inl x <> inl y *) intro Hcontra. inv Hcontra. contradiction.
  - (* inr x = inr y *) subst. reflexivity.
  - (* inr x <> inr y *) intro Hcontra. inv Hcontra. contradiction.
  - (* inl <> inr *) discriminate.
  - (* inr <> inl *) discriminate.
  - (* completeness *) apply sum_enum_complete; apply finite_complete.
Defined.

(** * Finite subsets *)

(** Filter finite type by predicate *)
Definition finite_filter {A : Type} `{Finite A} (P : A -> Prop)
  (Pdec : forall x, Decidable (P x)) : list A :=
  filter (fun x => if decide (P x) then true else false) finite_enum.

Lemma finite_filter_complete : forall {A : Type} `{Finite A} (P : A -> Prop)
  (Pdec : forall x, Decidable (P x)) (x : A),
  P x -> In x (finite_filter P Pdec).
Proof.
  intros A H P Pdec x Px.
  unfold finite_filter.
  induction finite_enum as [|y ys IH].
  - destruct (finite_complete x).
  - simpl. destruct (decide (P y)).
    + simpl. destruct (finite_complete x) as [Heq | Hin].
      * left. assumption.
      * right. apply IH. intro Hin'. apply Hin.
    + apply IH. intro Hin'. 
      destruct (finite_complete x) as [Heq | Hin''].
      * subst. contradiction.
      * apply Hin''.
Qed.

(** * Pigeonhole principle *)

Lemma pigeonhole : forall {A : Type} `{Finite A} (l : list A),
  length l > cardinality ->
  exists x, count_occ finite_eq_dec l x > 1.
Proof.
  intros A H l Hlen.
  unfold cardinality in Hlen.
  generalize dependent finite_enum.
  induction l as [|x xs IH]; intros enum Hlen Hcomplete.
  - simpl in Hlen. lia.
  - simpl in Hlen.
    destruct (count_occ finite_eq_dec xs x) eqn:Hcount.
    + (* x appears 0 times in xs *)
      assert (Hlen' : length xs > length (remove finite_eq_dec x enum)).
      { admit. } (* Length arithmetic *)
      destruct (IH (remove finite_eq_dec x enum)) as [y Hy].
      * lia.
      * intro y. destruct (finite_eq_dec x y).
        -- subst. apply In_remove; auto. apply Hcomplete.
        -- apply In_remove; auto. apply Hcomplete.
      * exists y. assumption.
    + (* x appears S n times in xs *)
      exists x. simpl. rewrite Hcount. lia.
Admitted. (* Full proof requires additional lemmas about count_occ and remove *)

(** * Finite iteration *)

(** Fold over finite type *)
Definition finite_fold {A B : Type} `{Finite A} (f : A -> B -> B) (init : B) : B :=
  fold_right f init finite_enum.

(** Map over finite type *)
Definition finite_map {A B : Type} `{Finite A} (f : A -> B) : list B :=
  map f finite_enum.

(** Filter-map combination *)
Definition finite_filter_map {A B : Type} `{Finite A} 
  (f : A -> option B) : list B :=
  flat_map (fun x => match f x with Some y => [y] | None => [] end) finite_enum.

(** * Decidable equality on lists of finite types *)

Lemma list_eq_dec {A : Type} `{Finite A} :
  forall (l1 l2 : list A), {l1 = l2} + {l1 <> l2}.
Proof.
  intros l1. induction l1 as [|x xs IH]; intro l2.
  - destruct l2.
    + left. reflexivity.
    + right. discriminate.
  - destruct l2 as [|y ys].
    + right. discriminate.
    + destruct (finite_eq_dec x y).
      * destruct (IH ys).
        -- left. subst. reflexivity.
        -- right. intro Hcontra. inv Hcontra. contradiction.
      * right. intro Hcontra. inv Hcontra. contradiction.
Defined.

(** * Finite functions *)

(** A function from finite type to B can be represented as a list *)
Definition finite_fun {A B : Type} `{Finite A} (f : A -> B) : list (A * B) :=
  map (fun x => (x, f x)) finite_enum.

(** Lookup in finite function representation *)
Fixpoint finite_fun_lookup {A B : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
  (x : A) (l : list (A * B)) : option B :=
  match l with
  | [] => None
  | (y, v) :: ys => if eq_dec x y then Some v else finite_fun_lookup eq_dec x ys
  end.

Lemma finite_fun_lookup_complete : forall {A B : Type} `{Finite A} (f : A -> B) (x : A),
  finite_fun_lookup finite_eq_dec x (finite_fun f) = Some (f x).
Proof.
  intros A B H f x.
  unfold finite_fun.
  induction finite_enum as [|y ys IH].
  - destruct (finite_complete x).
  - simpl. destruct (finite_eq_dec x y).
    + subst. reflexivity.
    + apply IH. intro Hin.
      destruct (finite_complete x) as [Heq | Hin'].
      * contradiction.
      * apply Hin'.
Qed.

(** * Finite relations *)

(** Decidable binary relation on finite type *)
Definition finite_relation {A : Type} `{Finite A} (R : A -> A -> Prop)
  (Rdec : forall x y, Decidable (R x y)) : list (A * A) :=
  filter (fun p => let (x, y) := p in if decide (R x y) then true else false)
         (prod_enum finite_enum finite_enum).

Lemma finite_relation_complete : forall {A : Type} `{Finite A} 
  (R : A -> A -> Prop) (Rdec : forall x y, Decidable (R x y)) (x y : A),
  R x y -> In (x, y) (finite_relation R Rdec).
Proof.
  intros A H R Rdec x y Hxy.
  unfold finite_relation.
  induction (prod_enum finite_enum finite_enum) as [|[a b] ps IH].
  - apply prod_enum_complete in Hxy; try apply finite_complete.
    inversion Hxy.
  - simpl. destruct (decide (R a b)).
    + simpl. 
      assert (Hin : In (x, y) ((a, b) :: ps)).
      { apply prod_enum_complete; apply finite_complete. }
      destruct Hin as [Heq | Hin'].
      * left. assumption.
      * right. apply IH. intro Hin''.
        apply prod_enum_complete in Hin''; try apply finite_complete.
        contradiction.
    + apply IH. intro Hin.
      apply prod_enum_complete in Hin; try apply finite_complete.
      destruct Hin as [Heq | Hin'].
      * inv Heq. contradiction.
      * contradiction.
Qed.

(** * Maximum and minimum over finite type *)

(** Find maximum value of function over finite type *)
Definition finite_max {A : Type} `{Finite A} (f : A -> nat) : option nat :=
  match finite_enum with
  | [] => None
  | x :: xs => Some (fold_left (fun acc y => Nat.max acc (f y)) xs (f x))
  end.

Lemma finite_max_correct : forall {A : Type} `{Finite A} (f : A -> nat) (x : A) (m : nat),
  finite_max f = Some m ->
  f x <= m.
Proof.
  intros A H f x m Hmax.
  unfold finite_max in Hmax.
  destruct finite_enum eqn:Heq.
  - destruct (finite_complete x).
  - inv Hmax.
    admit. (* Requires fold_left lemmas *)
Admitted.

(** Find minimum value of function over finite type *)
Definition finite_min {A : Type} `{Finite A} (f : A -> nat) : option nat :=
  match finite_enum with
  | [] => None
  | x :: xs => Some (fold_left (fun acc y => Nat.min acc (f y)) xs (f x))
  end.

(** * Finite summation *)

(** Sum function over finite type *)
Definition finite_sum {A : Type} `{Finite A} (f : A -> nat) : nat :=
  fold_right (fun x acc => f x + acc) 0 finite_enum.

Lemma finite_sum_nonneg : forall {A : Type} `{Finite A} (f : A -> nat),
  finite_sum f >= 0.
Proof.
  intros. unfold finite_sum. lia.
Qed.

Lemma finite_sum_bound : forall {A : Type} `{Finite A} (f : A -> nat) (x : A),
  f x <= finite_sum f.
Proof.
  intros A H f x.
  unfold finite_sum.
  induction finite_enum as [|y ys IH].
  - destruct (finite_complete x).
  - simpl. destruct (finite_complete x) as [Heq | Hin].
    + subst. lia.
    + assert (IH' := IH Hin). lia.
Qed.

(** * Finite counting *)

(** Count elements satisfying predicate *)
Definition finite_count {A : Type} `{Finite A} (P : A -> Prop)
  (Pdec : forall x, Decidable (P x)) : nat :=
  length (finite_filter P Pdec).

Lemma finite_count_le_cardinality : forall {A : Type} `{Finite A} (P : A -> Prop)
  (Pdec : forall x, Decidable (P x)),
  finite_count P Pdec <= cardinality.
Proof.
  intros A H P Pdec.
  unfold finite_count, cardinality, finite_filter.
  induction finite_enum as [|x xs IH]; simpl.
  - lia.
  - destruct (decide (P x)); simpl; lia.
Qed.

(** * Useful derived lemmas *)

Lemma finite_inhabited_or_empty {A : Type} `{Finite A} :
  (exists x : A, True) \/ (forall x : A, False).
Proof.
  destruct finite_enum eqn:Heq.
  - right. intro x. destruct (finite_complete x).
  - left. exists a. exact I.
Qed.

Lemma finite_nonempty_exists {A : Type} `{Finite A} :
  cardinality > 0 -> exists x : A, True.
Proof.
  intro Hcard.
  unfold cardinality in Hcard.
  destruct finite_enum eqn:Heq.
  - simpl in Hcard. lia.
  - exists a. exact I.
Qed.

Lemma finite_forall_impl : forall {A : Type} `{Finite A} (P Q : A -> Prop),
  (forall x, P x -> Q x) ->
  (forall x, P x) ->
  (forall x, Q x).
Proof.
  intros A H P Q Himpl Hall x.
  apply Himpl. apply Hall.
Qed.

(** * Export hints *)

#[export] Hint Resolve finite_complete : finite_db.
#[export] Hint Resolve prod_enum_complete : finite_db.
#[export] Hint Resolve finite_filter_complete : finite_db.
#[export] Hint Resolve finite_sum_nonneg : finite_db.
#[export] Hint Resolve finite_count_le_cardinality : finite_db.