(** Chapter 3 (Methodology) — Section 3.5.2 (Phase P3: Matching)

  Executable greedy matching rule (Definition-6) based on:
  - feasibility (Definition-1)
  - traded quantity q = min(residuals) (Definition-2)
  - match monotonicity (Definition-7)
*)
From Stdlib Require Import Arith List Bool PeanoNat Lia.
From MUDA Require Import Eqb Types State Sorting.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope bool_scope.

(** Definition-1 (Feasibility), boolean form.

    This is the executable feasibility test used by the greedy matcher.
*)
Definition is_feasible (b : Bid) (a : Ask) (ms : list Match) : bool :=
  Nat.leb (ask_price a) (price b)
  && Nat.leb 1 (residual_bid b ms)
  && Nat.leb 1 (residual_ask a ms).

Definition feasible (b : Bid) (a : Ask) (ms : list Match) : Prop :=
  is_feasible b a ms = true.

(* Greedy selection (Chapter 3 Definition 8):

   - select the highest-priority feasible buyer (using the deterministic
     tie-broken ordering from MUDA/Sorting.v)
   - then select the highest-priority feasible seller for that buyer
*)

Definition better_bid (b1 b2 : Bid) : Bid :=
  if bid_priorityb b1 b2 then b1 else b2.

Definition better_ask (a1 a2 : Ask) : Ask :=
  if ask_priorityb a1 a2 then a1 else a2.

Fixpoint best_feasible_ask (b : Bid) (as_list : list Ask) (ms : list Match)
  : option Ask :=
  match as_list with
  | [] => None
  | a :: as' =>
      let rest := best_feasible_ask b as' ms in
      if is_feasible b a ms then
        match rest with
        | None => Some a
        | Some a' => Some (better_ask a a')
        end
      else rest
  end.

Fixpoint find_feasible (bs : list Bid) (as_list : list Ask) (ms : list Match)
  : option (Bid * Ask) :=
  match bs with
  | [] => None
  | b :: bs' =>
      let rest := find_feasible bs' as_list ms in
      match best_feasible_ask b as_list ms with
      | None => rest
      | Some a =>
          match rest with
          | None => Some (b, a)
          | Some (b2, a2) =>
        if bid_priorityb b b2 then Some (b, a) else Some (b2, a2)
          end
      end
  end.

Lemma best_feasible_ask_spec :
  forall b as_list ms a,
    best_feasible_ask b as_list ms = Some a ->
    is_feasible b a ms = true.
Proof.
  intros b as_list ms.
  induction as_list as [|ah asx IH]; intros a H; simpl in H.
  - discriminate.
  - remember (best_feasible_ask b asx ms) as rest eqn:Hrest.
    destruct (is_feasible b ah ms) eqn:Hf.
    + destruct rest as [a0|].
      * inversion H; subst a; clear H.
        unfold better_ask.
        destruct (ask_priorityb ah a0) eqn:Hprio; [exact Hf|].
        apply (IH a0). reflexivity.
      * inversion H; subst a; exact Hf.
    + apply (IH a). exact H.
Qed.

Lemma find_feasible_spec :
  forall bs as_list ms b a,
    find_feasible bs as_list ms = Some (b,a) ->
    is_feasible b a ms = true.
Proof.
  induction bs as [|b0 bs IH]; intros as_list ms b a H; simpl in H.
  - discriminate.
  - destruct (best_feasible_ask b0 as_list ms) as [a0|] eqn:Hask.
    + destruct (find_feasible bs as_list ms) as [[b2 a2]|] eqn:Hrest.
      * destruct (bid_priorityb b0 b2) eqn:Hprio.
        -- inversion H; subst b a; clear H.
           apply (best_feasible_ask_spec b0 as_list ms a0). exact Hask.
        -- inversion H; subst b a; clear H.
           eapply (IH as_list ms b2 a2). exact Hrest.
      * inversion H; subst b a; clear H.
        apply (best_feasible_ask_spec b0 as_list ms a0). exact Hask.
    + eapply (IH as_list ms b a). exact H.

Qed.



(** Definition-2 (Traded Unit Quantity).

    A trade quantity is the maximum feasible trade between the chosen buyer and
    seller: q = min(residual_bid, residual_ask).
*)
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


(** Definition-6 (Greedy Matching Rule).

  One greedy round either appends exactly one trade to the match record, or
  returns `None` to signal that no feasible pair exists.
*)
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

(** Definition-7 (Match Monotonicity).

    During matching, the match record grows monotonically.
*)
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
  split.
  - (* bids side *)
    intro b'.
    change (allocated_bid b' (ms ++ [m]) <= quantity b').
    rewrite (allocated_bid_app_single b' ms m).
    destruct (bid_eq_dec (matched_bid m) b') as [Heq|Hneq].
    + subst b'.
      unfold m, create_match; simpl.
      set (A := allocated_bid b ms).
      set (rb := residual_bid b ms).
      set (ra := residual_ask a ms).
      assert (Hq_le_rb : Nat.min rb ra <= rb) by apply Nat.le_min_l.
      assert (HA : A <= quantity b) by apply Hbid.
      assert (Hrb_def : rb = quantity b - A).
      { unfold rb, residual_bid, A. reflexivity. }
      rewrite Hrb_def in Hq_le_rb.
      lia.
    + unfold m, create_match; simpl.
      destruct (bid_eq_dec b b') as [Heq'|Hneq']; [subst; contradiction|].
      unfold ms.
      rewrite Nat.add_0_r.
      apply Hbid.
  - (* asks side *)
    intro a'.
    change (allocated_ask a' (ms ++ [m]) <= ask_quantity a').
    rewrite (allocated_ask_app_single a' ms m).
    destruct (ask_eq_dec (matched_ask m) a') as [Heq|Hneq].
    + subst a'.
      unfold m, create_match; simpl.
      set (A := allocated_ask a ms).
      set (rb := residual_bid b ms).
      set (ra := residual_ask a ms).
      assert (Hq_le_ra : Nat.min rb ra <= ra) by apply Nat.le_min_r.
      assert (HA : A <= ask_quantity a) by apply Hask.
      assert (Hra_def : ra = ask_quantity a - A).
      { unfold ra, residual_ask, A. reflexivity. }
      rewrite Hra_def in Hq_le_ra.
      lia.
    + unfold m, create_match; simpl.
      destruct (ask_eq_dec a a') as [Heq'|Hneq']; [subst; contradiction|].
      unfold ms.
      rewrite Nat.add_0_r.
      apply Hask.
Qed.


