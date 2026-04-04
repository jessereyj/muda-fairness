From Stdlib Require Import Arith List Bool PeanoNat Lia.
From MUDA Require Import Types State Sorting.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope bool_scope.

(** Panel index (thesis ↔ code)

  Chapter 3 (Greedy matching)
  - is_feasible/feasible: feasibility test (Definition 1)
  - best_feasible_ask, find_feasible: greedy selection under priority (Definition 8)
  - create_match: traded quantity q = min(residual_bid, residual_ask) (Definition 9)
  - match_step: one greedy matching round (appends at most one match)

  Chapter 4 (Invariant preservation)
  - allocOK_after_match: allocOK preserved when match_step succeeds
*)

(** Definition-1 (Feasibility), boolean form.

    This is the executable feasibility test used by the greedy matcher.
*)
(* is_feasible: executable feasibility test (ask_price <= bid_price and positive residuals). *)
Definition is_feasible (b : Bid) (a : Ask) (ms : list Match) : bool :=
  Nat.leb (ask_price a) (price b)
  && Nat.leb 1 (residual_bid b ms)
  && Nat.leb 1 (residual_ask a ms).

(* feasible: Prop-level wrapper for is_feasible = true. *)
Definition feasible (b : Bid) (a : Ask) (ms : list Match) : Prop :=
  is_feasible b a ms = true.

(* Greedy selection (Chapter 3 Definition 8):

   - select the highest-priority feasible buyer (using the deterministic
     tie-broken ordering from MUDA/Sorting.v)
   - then select the highest-priority feasible seller for that buyer
*)

(* better_ask: pick the higher-priority ask under ask_priorityb. *)
Definition better_ask (a1 a2 : Ask) : Ask :=
  if ask_priorityb a1 a2 then a1 else a2.

(* best_feasible_ask: highest-priority feasible ask for a given bid. *)
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

(* find_feasible: pick a feasible (bid,ask) pair by greedy priority search. *)
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

(* best_feasible_ask_spec: selected ask is indeed feasible (boolean form). *)
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

(* find_feasible_spec: selected (bid,ask) pair is feasible (boolean form). *)
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

(** Definition-9 (Traded Unit Quantity).

    A trade quantity is the maximum feasible trade between the chosen buyer and
    seller: q = min(residual_bid, residual_ask).
*)
(* create_match: construct a Match with q = min(residual_bid, residual_ask). *)
Definition create_match (b : Bid) (a : Ask) (ms : list Match) : Match :=
  let q := Nat.min (residual_bid b ms) (residual_ask a ms) in
  {| matched_bid := b; matched_ask := a; match_quantity := q |}.

(** Definition-8 (Greedy Matching Rule).

  One greedy round either appends exactly one trade to the match record, or
  returns `None` to signal that no feasible pair exists.
*)
(* match_step: one greedy round (append one match if feasible, else return None). *)
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

(* match_step_preserves_clearing_price: a successful match_step does not change clearing_price. *)
Lemma match_step_preserves_clearing_price :
  forall s s',
    match_step s = Some s' ->
    clearing_price s' = clearing_price s.
Proof.
  intros s s' Hm.
  unfold match_step in Hm.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf; try discriminate.
  inversion Hm; subst s'; simpl; reflexivity.
Qed.

(* allocated_bid_app_single: effect on allocated_bid of appending one match. *)
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

(* allocated_ask_app_single: effect on allocated_ask of appending one match. *)
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


(* allocOK_after_match: allocOK is preserved by one successful match_step. *)
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


