(** Chapter 3 (Methodology) — Section 3.5.1 (Phase P2: Sorting)

  Implements the priority relations (Definition-3) and axiomatizes sorting as
  a permutation that produces priority-sorted bid/ask lists.

  Note: sorting is axiomatized to keep focus on temporal verification.
*)
From Stdlib Require Import List Lia Arith Sorting Permutation Sorted.
Import ListNotations.
From MUDA Require Import Eqb Types State.

(** Definition-3 (Priority Ordering).

    Buyers are prioritized by higher bid price, then earlier timestamp.
    Sellers are prioritized by lower ask price, then earlier timestamp.

    The implementation refines tie-breaking further with unique identifiers to
    obtain strict total orders.
*)
Definition prioB (b1 b2 : Bid) : Prop :=
  price b1 > price b2 \/
  (price b1 = price b2 /\ ts b1 < ts b2).

Definition prioS (a1 a2 : Ask) : Prop :=
  ask_price a1 < ask_price a2 \/
  (ask_price a1 = ask_price a2 /\ ask_ts a1 < ask_ts a2).

(* Bids: price ↓, then ts ↑, then id ↑ *)
Definition bid_priority (b1 b2 : Bid) : Prop :=
  price b1 > price b2 \/
  (price b1 = price b2 /\
     (ts b1 < ts b2 \/
      (ts b1 = ts b2 /\ bid_id b1 < bid_id b2))).

(* Asks: ask_price ↑, then ask_ts ↑, then ask_id ↑ *)
Definition ask_priority (a1 a2 : Ask) : Prop :=
  ask_price a1 < ask_price a2 \/
  (ask_price a1 = ask_price a2 /\
     (ask_ts a1 < ask_ts a2 \/
      (ask_ts a1 = ask_ts a2 /\ ask_id a1 < ask_id a2))).


Lemma bid_priority_irrefl : forall b, ~ bid_priority b b.
Proof.
  intros b; unfold bid_priority; intros [Hgt|[Heq [Hlt|[Heqt Hid]]]]; try lia.
Qed.

Lemma ask_priority_irrefl : forall a, ~ ask_priority a a.
Proof.
  intros a; unfold ask_priority; intros [Hlt|[Heq [Hlt'|[Heqt Hid]]]]; try lia.
Qed.

Lemma bid_priority_trans :
  forall x y z, bid_priority x y -> bid_priority y z -> bid_priority x z.
Proof.
  intros x y z Hxy Hyz.
  unfold bid_priority in *.
  destruct Hxy as [Hx_gt | [Hxy_peq [Hxy_tslt | [Hxy_tseq Hxy_idlt]]]].
  - (* price x > price y *)
    destruct Hyz as [Hy_gt | [Hyz_peq _]].
    + left; lia.
    + left. rewrite <- Hyz_peq. exact Hx_gt.
  - (* price x = price y, ts x < ts y *)
    destruct Hyz as [Hy_gt | [Hyz_peq [Hyz_tslt | [Hyz_tseq Hyz_idlt]]]].
    + (* y price > z price *) left. rewrite Hxy_peq; exact Hy_gt.
    + (* equal price, ts y < ts z *)
      right; split.
      * (* price x = price z *) now rewrite Hxy_peq.
      * (* ts x < ts z by transitivity *)
        left; eapply Nat.lt_trans; eauto.
    + (* equal price, ts y = ts z and id y < id z *)
      right; split.
      * now rewrite Hxy_peq.
      * (* ts x < ts z since ts x < ts y = ts z *)
        left; rewrite Hyz_tseq in Hxy_tslt; exact Hxy_tslt.
  - (* price x = price y, ts x = ts y and id x < id y *)
    destruct Hyz as [Hy_gt | [Hyz_peq [Hyz_tslt | [Hyz_tseq Hyz_idlt]]]].
    + left. rewrite Hxy_peq; exact Hy_gt.
    + (* price y = price z, ts y < ts z *)
      right; split; [ now rewrite Hxy_peq, Hyz_peq |].
      left. rewrite Hxy_tseq; exact Hyz_tslt.
    + (* price y = price z, ts y = ts z, id y < id z *)
      right; split; [ now rewrite Hxy_peq, Hyz_peq |].
      right; split; [ now rewrite Hxy_tseq, Hyz_tseq | lia].
Qed.

Lemma ask_priority_trans :
  forall x y z, ask_priority x y -> ask_priority y z -> ask_priority x z.
Proof.
  intros x y z Hxy Hyz.
  unfold ask_priority in *.
  destruct Hxy as [Hx_lt | [Hxy_peq [Hxy_tslt | [Hxy_tseq Hxy_idlt]]]].
  - (* price x < price y *)
    destruct Hyz as [Hy_lt | [Hyz_peq _]].
    + left; lia.
    + left. rewrite <- Hyz_peq. exact Hx_lt.
  - (* price x = price y, ts x < ts y *)
    destruct Hyz as [Hy_lt | [Hyz_peq [Hyz_tslt | [Hyz_tseq Hyz_idlt]]]].
    + left. rewrite Hxy_peq; exact Hy_lt.
    + right; split; [ now rewrite Hxy_peq |]. left.
      eapply Nat.lt_trans; eauto.
    + right; split; [ now rewrite Hxy_peq |]. left.
      rewrite Hyz_tseq in Hxy_tslt; exact Hxy_tslt.
  - (* price x = price y, ts x = ts y and id x < id y *)
    destruct Hyz as [Hy_lt | [Hyz_peq [Hyz_tslt | [Hyz_tseq Hyz_idlt]]]].
    + left. rewrite Hxy_peq; exact Hy_lt.
    + (* price y = price z, ts y < ts z *)
      right; split; [ now rewrite Hxy_peq, Hyz_peq |].
      left. rewrite Hxy_tseq; exact Hyz_tslt.
    + (* price y = price z, ts y = ts z, id y < id z *)
      right; split; [ now rewrite Hxy_peq, Hyz_peq |].
      right; split; [ now rewrite Hxy_tseq, Hyz_tseq | lia].
Qed.

Lemma bid_priority_refines_prioB :
  forall x y,
    bid_priority x y ->
    prioB x y \/ (price x = price y /\ ts x = ts y /\ bid_id x < bid_id y).
Proof.
  intros x y H; unfold bid_priority in H; unfold prioB.
  destruct H as [Hp | [Hp [Ht | [Ht Hid]]]]; eauto 6.
Qed.

Lemma ask_priority_refines_prioS :
  forall x y,
    ask_priority x y ->
    prioS x y \/ (ask_price x = ask_price y /\ ask_ts x = ask_ts y /\ ask_id x < ask_id y).
Proof.
  intros x y H; unfold ask_priority in H; unfold prioS.
  destruct H as [Hp | [Hp [Ht | [Ht Hid]]]]; eauto 6.
Qed.

Definition bids_sorted (bs : list Bid) : Prop :=
  forall i j b1 b2,
    nth_error bs i = Some b1 ->
    nth_error bs j = Some b2 ->
    i < j ->
    bid_priority b1 b2.

Definition asks_sorted (as_list : list Ask) : Prop :=
  forall i j a1 a2,
    nth_error as_list i = Some a1 ->
    nth_error as_list j = Some a2 ->
    i < j ->
    ask_priority a1 a2.


Definition bids_strongly_sorted (bs : list Bid) : Prop :=
  StronglySorted bid_priority bs.

Definition asks_strongly_sorted (as_list : list Ask) : Prop :=
  StronglySorted ask_priority as_list.

Lemma StronglySorted__bids_sorted :
  forall bs, bids_strongly_sorted bs -> bids_sorted bs.
Proof.
  intros bs Hss.
  unfold bids_strongly_sorted in Hss.
  unfold bids_sorted.
  (* Stdlib `StronglySorted` is built from a sorted tail plus a head-vs-tail Forall. *)
  induction Hss as [|x xs Htail IHtail Hall];
    intros i j b1 b2 Hi Hj Hij.
  - (* [] *) destruct i; simpl in Hi; inversion Hi.
  - destruct i as [|i']; destruct j as [|j']; simpl in Hi, Hj.
    + (* i=0, j=0: impossible since 0 < 0 *)
      inversion Hi; inversion Hj; subst.
      pose proof (Nat.lt_irrefl 0 Hij) as Hfalse.
      contradiction.
    + (* i=0, j=S j': head is before tail *)
      inversion Hi; subst b1.
      assert (forall y, In y xs -> bid_priority x y) as Hhead.
      {
        intros y Hy.
        clear -Hall Hy.
        induction Hall; simpl in Hy.
        - contradiction.
        - destruct Hy as [->|Hy]; [assumption|].
          apply IHHall; assumption.
      }
      apply Hhead.
      apply nth_error_In with (n := j').
      exact Hj.
    + (* i=S i', j=0: impossible since S i' < 0 *)
      assert False by lia.
      contradiction.
    + (* i=S i', j=S j': reduce to tail *)
      eapply IHtail; eauto; lia.
Qed.

Lemma StronglySorted__asks_sorted :
  forall asx, asks_strongly_sorted asx -> asks_sorted asx.
Proof.
  intros asx Hss.
  unfold asks_strongly_sorted in Hss.
  unfold asks_sorted.
  induction Hss as [|x xs Htail IHtail Hall];
    intros i j a1 a2 Hi Hj Hij.
  - (* [] *) destruct i; simpl in Hi; inversion Hi.
  - destruct i as [|i']; destruct j as [|j']; simpl in Hi, Hj.
    + (* i=0, j=0: impossible since 0 < 0 *)
      inversion Hi; inversion Hj; subst.
      pose proof (Nat.lt_irrefl 0 Hij) as Hfalse.
      contradiction.
    + (* i=0, j=S j': head is before tail *)
      inversion Hi; subst a1.
      assert (forall y, In y xs -> ask_priority x y) as Hhead.
      {
        intros y Hy.
        clear -Hall Hy.
        induction Hall; simpl in Hy.
        - contradiction.
        - destruct Hy as [->|Hy]; [assumption|].
          apply IHHall; assumption.
      }
      apply Hhead.
      apply nth_error_In with (n := j').
      exact Hj.
    + (* i=S i', j=0: impossible since S i' < 0 *)
      assert False by lia.
      contradiction.
    + (* i=S i', j=S j': reduce to tail *)
      eapply IHtail; eauto; lia.
Qed.

Lemma bids_sorted__StronglySorted :
  forall bs, bids_sorted bs -> bids_strongly_sorted bs.
Proof.
  intros bs Hsorted.
  unfold bids_strongly_sorted.
  (* Helper: produce an index for an element known to be In a list. *)
  assert (Hin_nth : forall (A : Type) (l : list A) (x : A),
             In x l -> exists n, nth_error l n = Some x).
  {
    intros A l; induction l as [|a l IH]; intros x Hin.
    - contradiction.
    - simpl in Hin. destruct Hin as [->|Hin].
      + exists 0; reflexivity.
      + destruct (IH x Hin) as [n Hn]. exists (S n). exact Hn.
  }
  (* Helper: tail preserves the nth-error sortedness notion. *)
  assert (Htail : forall x xs, bids_sorted (x :: xs) -> bids_sorted xs).
  {
    intros x xs H i j b1 b2 Hi Hj Hij.
    eapply (H (S i) (S j) b1 b2); simpl; eauto.
    exact (proj1 (Nat.succ_lt_mono i j) Hij).
  }
  induction bs as [|x xs IH].
  - constructor.
  - constructor.
    + (* tail is strongly sorted *)
      apply IH.
      apply (Htail x xs).
      exact Hsorted.
    + (* head relates to every element in the tail *)
      assert (forall y, In y xs -> bid_priority x y) as Hhead.
      {
        intros y Hy.
        destruct (Hin_nth _ xs y Hy) as [n Hn].
        eapply Hsorted with (i := 0) (j := S n) (b1 := x) (b2 := y);
          simpl; try reflexivity; try exact Hn; lia.
      }
      clear -Hhead.
      revert Hhead.
      induction xs as [|y ys IHys]; intros Hhead.
      * constructor.
      * constructor.
        -- apply Hhead. simpl. left. reflexivity.
        -- apply IHys. intros z Hz.
           apply Hhead. simpl. right. exact Hz.
Qed.

Lemma asks_sorted__StronglySorted :
  forall asx, asks_sorted asx -> asks_strongly_sorted asx.
Proof.
  intros asx Hsorted.
  unfold asks_strongly_sorted.
  assert (Hin_nth : forall (A : Type) (l : list A) (x : A),
             In x l -> exists n, nth_error l n = Some x).
  {
    intros A l; induction l as [|a l IH]; intros x Hin.
    - contradiction.
    - simpl in Hin. destruct Hin as [->|Hin].
      + exists 0; reflexivity.
      + destruct (IH x Hin) as [n Hn]. exists (S n). exact Hn.
  }
  assert (Htail : forall x xs, asks_sorted (x :: xs) -> asks_sorted xs).
  {
    intros x xs H i j a1 a2 Hi Hj Hij.
    eapply (H (S i) (S j) a1 a2); simpl; eauto.
    exact (proj1 (Nat.succ_lt_mono i j) Hij).
  }
  induction asx as [|x xs IH].
  - constructor.
  - constructor.
    + (* tail is strongly sorted *)
      apply IH.
      apply (Htail x xs).
      exact Hsorted.
    + (* head relates to every element in the tail *)
      assert (forall y, In y xs -> ask_priority x y) as Hhead.
      {
        intros y Hy.
        destruct (Hin_nth _ xs y Hy) as [n Hn].
        eapply Hsorted with (i := 0) (j := S n) (a1 := x) (a2 := y);
          simpl; try reflexivity; try exact Hn; lia.
      }
      clear -Hhead.
      revert Hhead.
      induction xs as [|y ys IHys]; intros Hhead.
      * constructor.
      * constructor.
        -- apply Hhead. simpl. left. reflexivity.
        -- apply IHys. intros z Hz.
           apply Hhead. simpl. right. exact Hz.
Qed.


Axiom sort_bids      : list Bid -> list Bid.
Axiom sort_asks      : list Ask -> list Ask.

Axiom sort_bids_correct : forall bs, bids_sorted (sort_bids bs).
Axiom sort_asks_correct : forall asx, asks_sorted (sort_asks asx).

Axiom sort_bids_perm : forall bs, Permutation (sort_bids bs) bs.
Axiom sort_asks_perm : forall asx, Permutation (sort_asks asx) asx.

Definition do_sorting (s : State) : State :=
  {| bids := sort_bids (bids s);
     asks := sort_asks (asks s);
     matches := matches s;
     clearing_price := clearing_price s;
     phase := P3 |}.