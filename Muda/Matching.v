(*  MUDA/Matching.v *)
From Stdlib Require Import Arith List Bool PeanoNat Bool Lia.
From MUDA Require Import Eqb Types State Sorting.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope bool_scope.

Definition is_feasible (b : Bid) (a : Ask) (ms : list Match) : bool :=
  Nat.leb (ask_price a) (price b)
  && Nat.leb 1 (residual_bid b ms)
  && Nat.leb 1 (residual_ask a ms).

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


Lemma pick_ask_None_forall :
  forall b as_list ms,
    pick_ask b as_list ms = None ->
    forall a, In a as_list -> is_feasible b a ms = false.
Proof.
  intros b as_list ms Hnone a Hin.
  induction as_list as [|ah asx IH]; simpl in *.
  - contradiction.
  - destruct (is_feasible b ah ms) eqn:Hf.
    + discriminate Hnone.
    + destruct Hin as [Hin0|HinRest].
      * subst; exact Hf.
      * apply IH; assumption.
Qed.

Lemma pick_ask_None_all_false :
  forall b as_list ms,
    pick_ask b as_list ms = None ->
    forall a, In a as_list -> is_feasible b a ms = false.
Proof.
  intros b as_list ms Hnone a Hin.
  revert a Hin.
  induction as_list as [|ah asx IH]; simpl in *; intros a Hin; try contradiction.
  destruct (is_feasible b ah ms) eqn:Hf.
  - discriminate Hnone.
  - destruct Hin as [Hin0|HinRest].
    + subst; exact Hf.
    + eapply IH.
      * exact Hnone.
      * exact HinRest.
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

Lemma find_feasible_None_forall :
  forall bs as_list ms,
    find_feasible bs as_list ms = None ->
    forall b a, In b bs -> In a as_list -> is_feasible b a ms = false.
Proof.
  induction bs as [|b0 bs IH]; intros as_list ms Hnone b a Hb Ha.
  - contradiction.
  - simpl in Hnone.
    destruct (pick_ask b0 as_list ms) as [a0|] eqn:Hpick.
    + discriminate Hnone.
    + (* In this branch Hpick = None, and Hnone simplifies to find_feasible bs as_list ms = None *)
      destruct Hb as [Hb0|HbRest].
      * subst b. eapply pick_ask_None_all_false; eauto.
      * eapply IH; eauto.
Qed.


Definition create_match (b : Bid) (a : Ask) (ms : list Match) : Match :=
  let q := Nat.min (residual_bid b ms) (residual_ask a ms) in
  {| matched_bid := b; matched_ask := a; match_quantity := q |}.

Lemma match_quantity_pos :
  forall s b a,
    find_feasible (bids s) (asks s) (matches s) = Some (b,a) ->
    0 < match_quantity (create_match b a (matches s)).
Proof.
  intros s b a Hf.
  unfold create_match. simpl.
  apply find_feasible_spec in Hf.
  unfold is_feasible in Hf.
  repeat rewrite Bool.andb_true_iff in Hf.
  destruct Hf as [[_ Hb] Ha].
  apply Nat.leb_le in Hb.
  apply Nat.leb_le in Ha.
  (* min of two naturals >=1 is >=1, i.e., strictly positive *)
  apply Nat.min_glb_lt; lia.
Qed.


Definition match_step (s : State) : option State :=
  match find_feasible (bids s) (asks s) (matches s) with
  | Some (b,a) =>
      let m := create_match b a (matches s) in
      Some {| bids := bids s;
              asks := asks s;
              matches := matches s ++ [m];
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
  simpl. unfold incl. intros x Hx.
  rewrite in_app_iff. left. exact Hx.
Qed.

Lemma allocated_bid_app_single :
  forall b ms m,
    allocated_bid b (ms ++ [m]) =
      allocated_bid b ms +
      (if bid_eq_dec (matched_bid m) b then match_quantity m else 0).
Proof.
  induction ms as [|m0 ms IH]; intros m; simpl.
  - destruct (bid_eq_dec (matched_bid m) b); simpl; lia.
  - destruct (bid_eq_dec (matched_bid m0) b); simpl; rewrite IH; lia.
Qed.

Lemma allocated_ask_app_single :
  forall a ms m,
    allocated_ask a (ms ++ [m]) =
      allocated_ask a ms +
      (if ask_eq_dec (matched_ask m) a then match_quantity m else 0).
Proof.
  induction ms as [|m0 ms IH]; intros m; simpl.
  - destruct (ask_eq_dec (matched_ask m) a); simpl; lia.
  - destruct (ask_eq_dec (matched_ask m0) a); simpl; rewrite IH; lia.
Qed.

Lemma app_singleton_inj :
  forall (A : Type) (l : list A) x y,
    l ++ [x] = l ++ [y] -> x = y.
Proof.
  intros A l x y H.
  induction l as [|a l IH]; simpl in H.
  - inversion H. reflexivity.
  - inversion H. apply IH. assumption.
Qed.


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

Lemma pick_ask_price_bound :
  forall b as_list ms a,
    pick_ask b as_list ms = Some a ->
    ask_price a <= price b.
Proof.
  intros b as_list ms a H.
  apply pick_ask_spec in H.
  unfold is_feasible in H.
  repeat rewrite Bool.andb_true_iff in H.
  destruct H as [[Hp _] _]. now apply Nat.leb_le in Hp.
Qed.

Lemma find_feasible_price_bound :
  forall bs as_list ms b a,
    find_feasible bs as_list ms = Some (b,a) ->
    ask_price a <= price b.
Proof.
  intros bs as_list ms b a H.
  apply find_feasible_spec in H.
  unfold is_feasible in H.
  repeat rewrite Bool.andb_true_iff in H.
  destruct H as [[Hp _] _]. now apply Nat.leb_le in Hp.
Qed.


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
    matches s' = matches s ++ [create_match b a (matches s)] ->
    ask_price a <= price b.
Proof.
  intros s s' b a Hstep Hhd.
  unfold match_step in Hstep.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b0 a0]|] eqn:Hf; try discriminate.
  inversion Hstep; subst; clear Hstep. simpl in Hhd.
  apply app_singleton_inj in Hhd. inversion Hhd; subst; clear Hhd.
  eapply match_price_bounds.
  now rewrite Hf.
Qed.

Lemma feasible_price_bounds :
  forall ms b a,
    is_feasible b a ms = true ->
    ask_price a <= price b.
Proof.
  intros ms b a Hf.
  unfold is_feasible in Hf.
  repeat rewrite Bool.andb_true_iff in Hf.
  destruct Hf as [[Hp _] _].
  now apply Nat.leb_le in Hp.
Qed.

Lemma find_feasible_price_bounds :
  forall s b a,
    find_feasible (bids s) (asks s) (matches s) = Some (b,a) ->
    ask_price a <= price b.
Proof.
  intros s b a H.
  apply find_feasible_spec in H.
  eapply feasible_price_bounds; eauto.
Qed.

Lemma create_match_price_bounds :
  forall ms b a,
    is_feasible b a ms = true ->
    ask_price a <= price b.
Proof.
  apply feasible_price_bounds.
Qed.


Lemma find_feasible_in_lists :
  forall bs as_list ms b a,
    find_feasible bs as_list ms = Some (b,a) ->
    is_feasible b a ms = true /\
    In b bs /\ In a as_list.
Proof.
  induction bs as [|b0 bs IH]; intros as_list ms b a H; simpl in H.
  - discriminate.
  - destruct (pick_ask b0 as_list ms) as [a0|] eqn:Hpick.
    + inversion H; subst b a; clear H.
      split.
      * eapply pick_ask_spec; eauto.
      * split; [left; reflexivity|].
        (* pick_ask returns Some a0 means a0 ∈ as_list *)
        (* simple membership proof by scanning as_list as pick_ask does *)
        revert as_list Hpick; induction as_list as [|ah asx IHas]; simpl; intro Hpick.
        { discriminate. }
        destruct (is_feasible b0 ah ms) eqn:?; [inversion Hpick; subst; now left|].
        right. apply IHas; exact Hpick.
    + apply IH in H. destruct H as [Hf [HinB HinA]].
      split; [assumption|]. split; [right; exact HinB | exact HinA].
Qed.

Lemma match_step_head_is_create :
  forall s s',
    match_step s = Some s' ->
    exists b a, matches s' = matches s ++ [create_match b a (matches s)].
Proof.
  intros s s' H.
  unfold match_step in H.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf; try discriminate.
  inversion H; subst; clear H.
  eexists b, a; reflexivity.
Qed.

Lemma match_step_head_price_bound :
  forall s s' b a,
    match_step s = Some s' ->
    matches s' = matches s ++ [create_match b a (matches s)] ->
    ask_price a <= price b.
Proof.
  intros s s' b a Hstep Hhd.
  unfold match_step in Hstep.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b0 a0]|] eqn:Hf; try discriminate.
  inversion Hstep; subst; clear Hstep. simpl in Hhd.
  apply app_singleton_inj in Hhd. inversion Hhd; subst; clear Hhd.
  (* use the feasibility spec of find_feasible *)
  apply find_feasible_spec in Hf.
  unfold is_feasible in Hf.
  repeat rewrite Bool.andb_true_iff in Hf.
  destruct Hf as [[Hp _] _]. now apply Nat.leb_le in Hp.
Qed.

Lemma allocOK_after_match :
  forall s s',
    allocOK s ->
    match_step s = Some s' ->
    allocOK s'.
Proof.
  intros s s' [Hbid Hask] Hstep.
  unfold match_step in Hstep.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf; try discriminate.
  inversion Hstep; subst s'; clear Hstep.
  set (ms := matches s).
  set (m := create_match b a ms).
  (* membership facts for b and a, needed to reuse Hbid/Hask bounds *)
  (* Use earlier lemma find_feasible_in_lists (membership + feasibility) *)
  pose proof (find_feasible_in_lists (bids s) (asks s) ms b a Hf) as [Hfeas [Hb_in Ha_in]].
  split.
  - (* bids side *)
    intros b' Hb'in.
    fold ms.
    fold m.
    rewrite allocated_bid_app_single.
    destruct (bid_eq_dec (matched_bid m) b') as [Eeq|Eneq].
    + (* affected bid: matched_bid m = b' ; but matched_bid m = b *)
      symmetry in Eeq; assert (b' = b) as ->.
      { unfold m, create_match in Eeq; simpl in Eeq. exact Eeq. }
      (* abbreviations *)
      set (A := allocated_bid b ms).
      set (Q := quantity b).
      set (q := Nat.min (residual_bid b ms) (residual_ask a ms)).
      (* old bound *)
      assert (Hbound : A <= Q) by (eapply Hbid; eauto).
      (* q <= residual_bid b ms = Q - A *)
      assert (Hq_le_res : q <= residual_bid b ms).
      { unfold q.
        apply Nat.le_min_l. }
      unfold residual_bid, A, Q, q in *.
      (* show match_quantity m + allocated_bid b ms <= quantity b *)
      unfold match_quantity, create_match; simpl.
      (* Now: Nat.min ... + allocated_bid b ms <= quantity b *)
      (* We have: Nat.min ... <= quantity b - allocated_bid b ms *)
      (* and allocated_bid b ms <= quantity b *)
      apply PeanoNat.Nat.add_le_mono_r with (p := allocated_bid b ms) in Hq_le_res.
      rewrite PeanoNat.Nat.sub_add in Hq_le_res by exact Hbound.
      exact Hq_le_res.
    + (* unaffected bid: allocation unchanged; reuse old bound *)
      simpl. eapply Hbid; exact Hb'in.
  - (* asks side *)
    intros a' Ha'in.
    fold ms.
    fold m.
    rewrite allocated_ask_app_single.
    destruct (ask_eq_dec (matched_ask m) a') as [Eeq|Eneq].
    + (* affected ask: matched_ask m = a' ; matched_ask m = a *)
      symmetry in Eeq; assert (a' = a) as ->.
      { unfold m, create_match in Eeq; simpl in Eeq. exact Eeq. }
      set (A := allocated_ask a ms).
      set (Q := ask_quantity a).
      set (q := Nat.min (residual_bid b ms) (residual_ask a ms)).
      assert (Hbound : A <= Q) by (eapply Hask; eauto).
      assert (Hq_le_res : q <= residual_ask a ms).
      { unfold q.
        apply Nat.le_min_r. }
      unfold residual_ask, A, Q, q in *.
      unfold match_quantity, create_match; simpl.
      apply PeanoNat.Nat.add_le_mono_r with (p := allocated_ask a ms) in Hq_le_res.
      rewrite PeanoNat.Nat.sub_add in Hq_le_res by exact Hbound.
      exact Hq_le_res.
    + (* unaffected ask *)
      simpl. eapply Hask; exact Ha'in.
Qed.

Lemma pick_ask_in :
  forall b as_list ms a,
    pick_ask b as_list ms = Some a -> In a as_list.
Proof.
  intros b as_list ms a H.
  induction as_list as [|ah asx IH]; simpl in H; try discriminate.
  destruct (is_feasible b ah ms) eqn:Hf.
  - inversion H; subst; now left.
  - right; eauto.
Qed.

Lemma find_feasible_in :
  forall bs as_list ms b a,
    find_feasible bs as_list ms = Some (b,a) ->
    In b bs /\ In a as_list.
Proof.
  induction bs as [|b0 bs IH]; simpl; intros as_list ms b a H; try discriminate.
  destruct (pick_ask b0 as_list ms) as [a0|] eqn:Hpick.
  - inversion H; subst; split; [now left |].
    apply pick_ask_in in Hpick; exact Hpick.
  - apply IH in H; destruct H as [Hb Ha]; split; [right; exact Hb | exact Ha].
Qed.
