(* Fairness/QuantityFairness.v *)
From Stdlib Require Import Arith List Lia Sorting Permutation.
Import ListNotations.
From MUDA Require Import Eqb Types State Sorting Matching ClearingPrice Transitions.

(* =============== Initial state =============== *)
Theorem quantity_fairness_initial : forall bs as_list,
  allocOK (initial_state bs as_list).
Proof.
  intros bs as_list; unfold allocOK, initial_state; simpl; split; intros; lia.
Qed.

(* =============== Small membership helpers for find_feasible =============== *)
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

(* =============== Core preservation lemmas =============== *)
(* Adding one match preserves allocation bounds.
   Shape: on success, match_step conses m = create_match b a ms at the head. *)
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
  pose proof (find_feasible_in (bids s) (asks s) ms b a Hf) as [Hb_in Ha_in].
  split.
  - (* bids side *)
    intros b' Hb'in. simpl.
    destruct (bid_eq_dec (matched_bid m) b') as [Eeq|Eneq].
    + (* affected bid: matched_bid m = b' ; but matched_bid m = b *)
      symmetry in Eeq; assert (b' = b) as ->.
      { unfold m, create_match in Eeq; simpl in Eeq. exact Eeq. }
      (* Now the "then" branch is selected; simplify *)
      simpl.
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
      simpl.
      unfold match_quantity, create_match; simpl.
      (* Now: Nat.min ... + allocated_bid b ms <= quantity b *)
      (* We have: Nat.min ... <= quantity b - allocated_bid b ms *)
      (* and allocated_bid b ms <= quantity b *)
      destruct (bid_eq_dec b b) as [_|]; [|congruence].
      apply PeanoNat.Nat.add_le_mono_r with (p := allocated_bid b ms) in Hq_le_res.
      rewrite PeanoNat.Nat.sub_add in Hq_le_res by exact Hbound.
      exact Hq_le_res.
    + (* unaffected bid: allocation unchanged; reuse old bound *)
      simpl. destruct (bid_eq_dec (matched_bid m) b') as [|Hneq']; [congruence|].
      destruct (bid_eq_dec b b') as [Heqb|Hneqb].
      * (* b = b' contradicts Eneq: matched_bid m <> b' and matched_bid m = b *)
        unfold m, create_match in Eneq; simpl in Eneq.
        subst b'. congruence.
      * eapply Hbid; exact Hb'in.
  - (* asks side *)
    intros a' Ha'in. simpl.
    destruct (ask_eq_dec (matched_ask m) a') as [Eeq|Eneq].
    + (* affected ask: matched_ask m = a' ; matched_ask m = a *)
      symmetry in Eeq; assert (a' = a) as ->.
      { unfold m, create_match in Eeq; simpl in Eeq. exact Eeq. }
      simpl.
      set (A := allocated_ask a ms).
      set (Q := ask_quantity a).
      set (q := Nat.min (residual_bid b ms) (residual_ask a ms)).
      assert (Hbound : A <= Q) by (eapply Hask; eauto).
      assert (Hq_le_res : q <= residual_ask a ms).
      { unfold q.
        apply Nat.le_min_r. }
      unfold residual_ask, A, Q, q in *.
      simpl.
      unfold match_quantity, create_match; simpl.
      destruct (ask_eq_dec a a) as [_|]; [|congruence].
      apply PeanoNat.Nat.add_le_mono_r with (p := allocated_ask a ms) in Hq_le_res.
      rewrite PeanoNat.Nat.sub_add in Hq_le_res by exact Hbound.
      exact Hq_le_res.
    + (* unaffected ask *)
      simpl. destruct (ask_eq_dec (matched_ask m) a') as [|Hneq']; [congruence|].
      destruct (ask_eq_dec a a') as [Heqa|Hneqa].
      * (* a = a' contradicts Eneq: matched_ask m <> a' and matched_ask m = a *)
        unfold m, create_match in Eneq; simpl in Eneq.
        subst a'. congruence.
      * eapply Hask; exact Ha'in.
Qed.

(* Sorting only reorders bids/asks; matches are unchanged. *)
Lemma allocOK_after_sorting :
  forall s,
    phase s = P2 ->
    allocOK s ->
    allocOK (step s).
Proof.
  intros s Hp2 [Hbid Hask].
  unfold step; rewrite Hp2; unfold do_sorting; simpl.
  split.
  - intros b Hb_in_sorted.
    pose proof (sort_bids_perm (bids s)) as Hperm.
    assert (In b (bids s)).
    { now apply (Permutation_in b Hperm). }
    exact (Hbid b H).
  - intros a Ha_in_sorted.
    pose proof (sort_asks_perm (asks s)) as Hperm.
    assert (In a (asks s)).
    { now apply (Permutation_in a Hperm). }
    exact (Hask a H).
Qed.

(* =============== One-step preservation across the pipeline =============== *)
Theorem quantity_fairness_step :
  forall s, allocOK s -> allocOK (step s).
Proof.
  intros s H.
  destruct (phase s) eqn:Hp.
  - (* P1 → P2: other fields unchanged wrt allocOK *)
    unfold step. rewrite Hp. exact H.
  - (* P2: sorting preserves bounds *)
    apply (allocOK_after_sorting s Hp H).
  - (* P3: either add a match or finish *)
    unfold step. rewrite Hp.
    destruct (match_step s) eqn:Hs.
    + eapply allocOK_after_match; eauto.
    + exact H.
  - (* P4 *) unfold step. rewrite Hp. exact H.
  - (* P5 *) unfold step. rewrite Hp. exact H.
  - (* P6 *) unfold step. rewrite Hp. exact H.
  - (* P7 *) unfold step. rewrite Hp. exact H.
Qed.