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

(* ---------- Feasibility: keep positivity guarded ---------- *)
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

(* ---------- Price bounds, stated only for feasible pairs ---------- *)
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
  (* You already proved the feasibility spec. *)
  apply find_feasible_spec in H.
  unfold is_feasible in H.
  repeat rewrite Bool.andb_true_iff in H.
  destruct H as [[Hp _] _]. now apply Nat.leb_le in Hp.
Qed.

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

(* 1) From feasibility directly *)
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

(* 2) From find_feasible (state-level) *)
Lemma find_feasible_price_bounds :
  forall s b a,
    find_feasible (bids s) (asks s) (matches s) = Some (b,a) ->
    ask_price a <= price b.
Proof.
  intros s b a H.
  apply find_feasible_spec in H.
  eapply feasible_price_bounds; eauto.
Qed.

(* 3) For a match constructed from a feasible pair *)
Lemma create_match_price_bounds :
  forall ms b a,
    is_feasible b a ms = true ->
    ask_price a <= price b.
Proof.
  (* identical to (1); separated for readability/use sites *)
  apply feasible_price_bounds.
Qed.

(** Core, provable hooks for Priority Fairness (Section 3 & 4) *)
(* 1) If find_feasible returns (b,a), then (a) the pair is feasible,
      (b) b ∈ bids, and (c) a ∈ asks. *)
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

(* 2) Shape of match_step on success: it conses the created match *)
Lemma match_step_head_is_create :
  forall s s',
    match_step s = Some s' ->
    exists b a, matches s' = create_match b a (matches s) :: matches s.
Proof.
  intros s s' H.
  unfold match_step in H.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf; try discriminate.
  inversion H; subst; clear H.
  eexists b, a; reflexivity.
Qed.

(* 3) Price bound of the chosen head match after a successful step *)
Lemma match_step_head_price_bound :
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
  (* use the feasibility spec of find_feasible *)
  apply find_feasible_spec in Hf.
  unfold is_feasible in Hf.
  repeat rewrite Bool.andb_true_iff in Hf.
  destruct Hf as [[Hp _] _]. now apply Nat.leb_le in Hp.
Qed.