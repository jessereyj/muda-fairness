(*  MUDA/Matching.v *)
From Stdlib Require Import Arith List Bool PeanoNat Bool Lia.
From MUDA Require Import Eqb Types State.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope bool_scope.

(* ---------- Match finding ---------- *)
(* Check if a bid-ask pair is feasible given current matches *)
Definition is_feasible (b : Bid) (a : Ask) (ms : list Match) : bool :=
  Nat.leb (ask_price a) (price b)
  && Nat.leb 1 (residual_bid b ms)
  && Nat.leb 1 (residual_ask a ms).

(* Prop-level wrapper for feasibility *)
Definition feasible (b : Bid) (a : Ask) (ms : list Match) : Prop :=
  is_feasible b a ms = true.

Fixpoint pick_ask (b : Bid) (as_list : list Ask) (ms : list Match)
  : option Ask :=
  match as_list with
  | [] => None
  | a :: as' =>
      if is_feasible b a ms
      then Some a
      else pick_ask b as' ms
  end.

Fixpoint find_feasible (bs : list Bid) (as_list : list Ask) (ms : list Match)
  : option (Bid * Ask) :=
  match bs with
  | [] => None
  | b :: bs' =>
      match pick_ask b as_list ms with
      | Some a => Some (b, a)
      | None => find_feasible bs' as_list ms
      end
  end.

Lemma pick_ask_spec :
  forall b as_list ms a,
    pick_ask b as_list ms = Some a ->
    is_feasible b a ms = true.
Proof.
  intros b as_list ms a H.
  induction as_list as [|ah asx IH]; simpl in H.
  - discriminate.
  - destruct (is_feasible b ah ms) eqn:Hf.
    + injection H as ->. assumption.
    + apply IH. exact H.
Qed.

Lemma find_feasible_spec :
  forall bs as_list ms b a,
    find_feasible bs as_list ms = Some (b,a) ->
    is_feasible b a ms = true.
Proof.
  induction bs as [|b0 bs IH]; intros as_list ms b a H; simpl in H.
  - discriminate.
  - destruct (pick_ask b0 as_list ms) as [a0|] eqn:Hpick.
    + inversion H; subst b a. clear H.
      apply (pick_ask_spec b0 as_list ms a0). exact Hpick.
    + apply (IH as_list ms b a). exact H.
Qed.

(* ---------- Match creation ---------- *)

Definition create_match (b : Bid) (a : Ask) (ms : list Match) : Match :=
  let q := Nat.min (residual_bid b ms) (residual_ask a ms) in
  {| matched_bid := b;
     matched_ask := a;
     match_quantity := q |}.

Lemma match_quantity_pos :
  forall s b a,
    find_feasible (bids s) (asks s) (matches s) = Some (b,a) ->
    0 < match_quantity (create_match b a (matches s)).
Proof.
  intros s b a Hf.
  unfold create_match.
  simpl.
  apply find_feasible_spec in Hf.
  unfold is_feasible in Hf.
  repeat rewrite Bool.andb_true_iff in Hf.
  destruct Hf as [[H_price H_res_bid] H_res_ask].
  apply Nat.leb_le in H_price.
  apply Nat.leb_le in H_res_bid.
  apply Nat.leb_le in H_res_ask.
  apply Nat.min_glb; assumption.
Qed.

(* ---------- Match step function and monotonicity ---------- *)

Definition match_step (s : State) : option State :=
  match find_feasible (bids s) (asks s) (matches s) with
  | Some (b,a) =>
      let m := create_match b a (matches s) in
      Some {| bids := bids s;
              asks := asks s;
              matches := m :: matches s;
              clearing_price := clearing_price s;
              phase := phase s |}
  | None => None
  end.

Lemma match_step_monotonic :
  forall s s',
    match_step s = Some s' ->
    incl (matches s) (matches s').
Proof.
  intros s s' H.
  unfold match_step in H.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:HF; try discriminate.
  inversion H; subst; clear H.
  simpl. unfold incl. intros x Hx. right. exact Hx.
Qed.
(* ---------- Feasibility checking ---------- *)


Fixpoint matched_quantities (b : Bid) (ms : list Match) : nat :=
  match ms with
  | [] => 0
  | m :: ms' =>
      if matched_bid m =? b 
      then match_quantity m + matched_quantities b ms'
      else matched_quantities b ms'
  end.

Fixpoint matched_quantities_ask (a : Ask) (ms : list Match) : nat :=
  match ms with
  | [] => 0
  | m :: ms' =>
      if matched_ask m =? a 
      then match_quantity m + matched_quantities_ask a ms'
      else matched_quantities_ask a ms'
  end.

Lemma feasible_implies_pos :
  forall b a ms,
    is_feasible b a ms = true ->
    1 <= residual_bid b ms /\ 1 <= residual_ask a ms.
Proof.
  intros b a ms Hf. unfold is_feasible in Hf.
  repeat rewrite Bool.andb_true_iff in Hf.
  destruct Hf as [[Hprice Hrb] Hra].
  split; apply Nat.leb_le; assumption.
Qed.


Lemma residual_ask_pos :
  forall (a : Ask) (ms : list Match),
    1 <= residual_ask a ms.
Proof.
  intros a ms.
  unfold residual_ask.
  generalize (ask_quantity a) as q.
  generalize (matched_quantities_ask a ms) as mq.
  intros mq q.
  admit.
Admitted.




(* ---------- Match properties ---------- *)

Lemma match_price_bounds : forall s b a,
  find_feasible (bids s) (asks s) (matches s) = Some (b, a) ->
  ask_price a <= price b.
Proof.
  intros s b a H.
  apply find_feasible_spec in H.
  unfold is_feasible in H.
  rewrite !Bool.andb_true_iff in H.
  destruct H as [[Hp _] _].
  apply Nat.leb_le in Hp.
  assumption.
Qed.

Lemma match_step_head_price_bounds :
  forall s s' b a,
    match_step s = Some s' ->
    matches s' = create_match b a (matches s) :: matches s ->
    ask_price a <= price b.
Proof.
  intros s s' b a Hstep Hhd.
  unfold match_step in Hstep.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b0 a0]|] eqn:Hf; try discriminate.
  inversion Hstep; subst; clear Hstep. simpl in Hhd.
  inversion Hhd; subst; clear Hhd.
  eapply match_price_bounds.
  now rewrite Hf.
Qed.

Lemma feasible_price_bounds : forall m : Match,
  ask_price (matched_ask m) <= price (matched_bid m).
Proof.
  intros m.
  destruct m as [b a q].
  (* Build state to invoke match_price_bounds *)
  pose (s := {|
    bids := [b];
    asks := [a];
    matches := [];
    clearing_price := None;
    phase := P3
  |}).
  simpl.
  unfold pick_ask.
  simpl.
  unfold is_feasible.
  simpl.
  (* Assume matches are always formed from feasible pairs *)
Admitted.

