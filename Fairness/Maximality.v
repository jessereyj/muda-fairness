(** Chapter 5 (Results) — Maximality

  Maximality is stated in Chapter 5 as a post-matching property: once MUDA
  has terminated matching (P4–P7), there is no feasible buyer–seller pair.
*)
From Stdlib Require Import Arith List Lia.
Import ListNotations.
From LTL Require Import LTL.
From Fairness Require Import Interpretation.
From MUDA Require Import Types State Matching Sorting Transitions Atoms.

Local Open Scope LTL_scope.

(* Chapter 5: maximality is a post-matching invariant: once the protocol has
   terminated matching (P4–P7), no feasible buyer–seller pair remains. *)
Definition maximal : LTL_formula := G (phase_ge_4 → Atom p_no_feasible).
Fixpoint sum_residual_bids (bs:list Bid) (ms:list Match) : nat :=
  match bs with
  | [] => 0
  | b::bs' => residual_bid b ms + sum_residual_bids bs' ms
  end.

Fixpoint sum_residual_asks (as_list:list Ask) (ms:list Match) : nat :=
  match as_list with
  | [] => 0
  | a::as' => residual_ask a ms + sum_residual_asks as' ms
  end.

Definition mu (s:State) : nat :=
  sum_residual_bids (bids s) (matches s) + sum_residual_asks (asks s) (matches s).

Lemma residual_bid_drop : forall s s' b a,
  match_step s = Some s' ->
  find_feasible (bids s) (asks s) (matches s) = Some (b,a) ->
  residual_bid b (matches s') < residual_bid b (matches s).
Proof.
  intros s s' b a Hstep Hf.
  unfold match_step in Hstep; rewrite Hf in Hstep; inversion Hstep; subst s'; clear Hstep.
  set (ms := matches s).
  set (m := create_match b a ms).
  unfold residual_bid; simpl.
  rewrite (allocated_bid_app_single b ms m).
  unfold m, create_match; simpl.
  destruct (bid_eq_dec b b) as [_|Hneq]; [|congruence].
  simpl.
  (* get residual bounds from feasibility *)
  pose proof (find_feasible_spec (bids s) (asks s) ms b a Hf) as Hfeas.
  unfold is_feasible in Hfeas.
  repeat rewrite Bool.andb_true_iff in Hfeas.
  destruct Hfeas as [[_ Hrb] Hra].
  apply Nat.leb_le in Hrb.
  apply Nat.leb_le in Hra.
  assert (Hmin1: 1 <= match_quantity (create_match b a ms)).
  { unfold match_quantity, create_match; simpl.
    destruct (Nat.le_ge_cases (residual_bid b ms) (residual_ask a ms)) as [Hle|Hge].
    - rewrite Nat.min_l by exact Hle. lia.
    - rewrite Nat.min_r by lia. lia. }
  (* Rewrite goal using rb := residual_bid b ms *)
  remember (residual_bid b ms) as rb.
  remember (residual_ask a ms) as ra.
  (* let A denote the prior allocation of b and q the matched quantity *)
  set (A := allocated_bid b ms).
  unfold match_quantity, create_match in *; simpl in *.
  set (q := Nat.min rb ra) in *.
  assert (Hqpos: 0 < q) by lia.
  (* Rewrite to X - q < X with X := quantity b - A *)
  rewrite Nat.sub_add_distr.
  set (XB := quantity b - A).
  replace (quantity b - A) with XB by reflexivity.
  assert (Hq_le_rb: q <= rb) by (subst q; apply Nat.le_min_l).
  assert (HeqXB: XB = rb) by (subst XB rb A; unfold residual_bid; reflexivity).
  assert (Hq_leXB: q <= XB) by (rewrite HeqXB; exact Hq_le_rb).
  lia.
Qed.

Lemma residual_ask_drop : forall s s' b a,
  match_step s = Some s' ->
  find_feasible (bids s) (asks s) (matches s) = Some (b,a) ->
  residual_ask a (matches s') < residual_ask a (matches s).
Proof.
  intros s s' b a Hstep Hf.
  unfold match_step in Hstep; rewrite Hf in Hstep; inversion Hstep; subst s'; clear Hstep.
  set (ms := matches s).
  set (m := create_match b a ms).
  unfold residual_ask; simpl.
  rewrite (allocated_ask_app_single a ms m).
  unfold m, create_match; simpl.
  destruct (ask_eq_dec a a) as [_|Hneq]; [|congruence].
  simpl.
  pose proof (find_feasible_spec (bids s) (asks s) ms b a Hf) as Hfeas.
  unfold is_feasible in Hfeas.
  repeat rewrite Bool.andb_true_iff in Hfeas.
  destruct Hfeas as [[_ Hrb] Hra].
  apply Nat.leb_le in Hrb.
  apply Nat.leb_le in Hra.
  assert (Hmin1: 1 <= match_quantity (create_match b a ms)).
  { unfold match_quantity, create_match; simpl.
    destruct (Nat.le_ge_cases (residual_bid b ms) (residual_ask a ms)) as [Hle|Hge].
    - rewrite Nat.min_l by exact Hle. lia.
    - rewrite Nat.min_r by lia. lia. }
  remember (residual_bid b ms) as rb.
  remember (residual_ask a ms) as ra.
  (* let A denote the prior allocation of a and q the matched quantity *)
  set (A := allocated_ask a ms).
  replace (ask_quantity a - A) with ra by (subst A ra; unfold residual_ask; lia).
  unfold match_quantity, create_match in *; simpl in *.
  set (q := Nat.min rb ra) in *.
  assert (Hqpos: 0 < q) by lia.
  (* Rewrite to Y - q < Y with Y := ask_quantity a - A *)
  rewrite Nat.sub_add_distr.
  set (YA := ask_quantity a - A).
  replace (ask_quantity a - A) with YA by reflexivity.
  assert (Hq_le_ra: q <= ra) by (subst q; apply Nat.le_min_r).
  assert (HeqYA: YA = ra) by (subst YA A ra; unfold residual_ask; reflexivity).
  assert (Hq_leYA: q <= YA) by (rewrite HeqYA; exact Hq_le_ra).
  lia.
Qed.

Lemma residual_bid_unchanged : forall s s' b0 a b,
  match_step s = Some s' ->
  find_feasible (bids s) (asks s) (matches s) = Some (b0,a) ->
  b <> b0 ->
  residual_bid b (matches s') = residual_bid b (matches s).
Proof.
  intros s s' b0 a b Hstep Hf Hbneq.
  unfold match_step in Hstep; rewrite Hf in Hstep; inversion Hstep; subst s'; clear Hstep.
  set (ms := matches s).
  set (m := create_match b0 a ms).
  unfold residual_bid. simpl.
  rewrite (allocated_bid_app_single b ms m).
  unfold m, create_match; simpl.
  change (matched_bid (create_match b0 a ms)) with b0.
  destruct (bid_eq_dec b0 b) as [Eeq|Eneq].
  - subst b. contradiction.
  - simpl. lia.
Qed.

Lemma residual_ask_unchanged : forall s s' b a0 a,
  match_step s = Some s' ->
  find_feasible (bids s) (asks s) (matches s) = Some (b,a0) ->
  a <> a0 ->
  residual_ask a (matches s') = residual_ask a (matches s).
Proof.
  intros s s' b a0 a Hstep Hf Hneq.
  unfold match_step in Hstep; rewrite Hf in Hstep; inversion Hstep; subst s'; clear Hstep.
  set (ms := matches s).
  set (m := create_match b a0 ms).
  unfold residual_ask. simpl.
  rewrite (allocated_ask_app_single a ms m).
  unfold m, create_match; simpl.
  change (matched_ask (create_match b a0 ms)) with a0.
  destruct (ask_eq_dec a0 a) as [Eeq|Eneq].
  - subst a. contradiction.
  - simpl. lia.
Qed.

(* Membership of the chosen bid in the bid list. *)
Lemma find_feasible_In_b : forall bs as_list ms b a,
  find_feasible bs as_list ms = Some (b,a) -> In b bs.
Proof.
  induction bs as [|b0 bs IH]; intros as_list ms b a H; simpl in H.
  - discriminate.
  - destruct (pick_ask b0 as_list ms) as [a0|] eqn:Hpick.
    + inversion H; subst b a. left; reflexivity.
    + right. eauto.
Qed.

(* Membership of the chosen ask in the ask list. *)
Lemma find_feasible_In_a : forall bs as_list ms b a,
  find_feasible bs as_list ms = Some (b,a) -> In a as_list.
Proof.
  induction bs as [|b0 bs IH]; intros as_list ms b a H; simpl in H.
  - discriminate.
  - destruct (pick_ask b0 as_list ms) as [a0|] eqn:Hpick.
    + inversion H; subst b a.
      (* Now we need to show pick_ask implies membership *)
      clear IH H. revert b0 ms a0 Hpick.
      induction as_list as [|ah asx IHas]; intros b0 ms a0 Hpick; simpl in Hpick.
      * discriminate.
      * destruct (is_feasible b0 ah ms) eqn:Hf.
        -- injection Hpick as <-. left; reflexivity.
        -- right. apply IHas with b0 ms. exact Hpick.
    + eapply IH. exact H.
Qed.

(* Helper: match_step preserves bids *)
Lemma match_step_bids_unchanged : forall s s',
  match_step s = Some s' -> bids s' = bids s.
Proof.
  intros s s' H.
  unfold match_step in H.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|]; try discriminate.
  inversion H; reflexivity.
Qed.

(* Helper: match_step preserves asks *)
Lemma match_step_asks_unchanged : forall s s',
  match_step s = Some s' -> asks s' = asks s.
Proof.
  intros s s' H.
  unfold match_step in H.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|]; try discriminate.
  inversion H; reflexivity.
Qed.

Lemma sum_residual_bids_pointwise_le : forall bs ms ms',
  (forall x, In x bs -> residual_bid x ms' <= residual_bid x ms) ->
  sum_residual_bids bs ms' <= sum_residual_bids bs ms.
Proof.
  intros bs ms ms' Hle.
  induction bs as [|b bs IH]; simpl; [lia|].
  assert (Hb_le : residual_bid b ms' <= residual_bid b ms) by (apply Hle; left; reflexivity).
  assert (Htail_le : sum_residual_bids bs ms' <= sum_residual_bids bs ms).
  { apply IH. intros x Hx. apply Hle. right; exact Hx. }
  lia.
Qed.

Lemma sum_residual_bids_pointwise_strict : forall bs ms ms' b,
  In b bs ->
  (forall x, In x bs -> residual_bid x ms' <= residual_bid x ms) ->
  residual_bid b ms' < residual_bid b ms ->
  sum_residual_bids bs ms' < sum_residual_bids bs ms.
Proof.
  intros bs ms ms' b Hin Hle Hlt.
  induction bs as [|x xs IH]; simpl in *; [contradiction|].
  destruct Hin as [Hx|HinTail].
  - subst x.
    assert (Htail_le: sum_residual_bids xs ms' <= sum_residual_bids xs ms).
    { apply sum_residual_bids_pointwise_le. intros y Hy. apply Hle. right; exact Hy. }
    apply Nat.add_lt_le_mono; [exact Hlt|exact Htail_le].
  - assert (Hx_le: residual_bid x ms' <= residual_bid x ms) by (apply Hle; left; reflexivity).
    assert (Htail_strict: sum_residual_bids xs ms' < sum_residual_bids xs ms).
    { apply IH; [assumption|]. intros y Hy. apply Hle. right; exact Hy. all:assumption. }
    apply Nat.add_le_lt_mono; [exact Hx_le|exact Htail_strict].
Qed.

Lemma sum_residual_asks_pointwise_le : forall asx ms ms',
  (forall x, In x asx -> residual_ask x ms' <= residual_ask x ms) ->
  sum_residual_asks asx ms' <= sum_residual_asks asx ms.
Proof.
  intros asx ms ms' Hle.
  induction asx as [|a asx IH]; simpl; [lia|].
  assert (Ha_le : residual_ask a ms' <= residual_ask a ms) by (apply Hle; left; reflexivity).
  assert (Htail_le : sum_residual_asks asx ms' <= sum_residual_asks asx ms).
  { apply IH. intros x Hx. apply Hle. right; exact Hx. }
  lia.
Qed.

Lemma sum_residual_asks_pointwise_strict : forall asx ms ms' a,
  In a asx ->
  (forall x, In x asx -> residual_ask x ms' <= residual_ask x ms) ->
  residual_ask a ms' < residual_ask a ms ->
  sum_residual_asks asx ms' < sum_residual_asks asx ms.
Proof.
  intros asx ms ms' a Hin Hle Hlt.
  induction asx as [|x xs IH]; simpl in *; [contradiction|].
  destruct Hin as [Hx|HinTail].
  - subst x.
    assert (Htail_le: sum_residual_asks xs ms' <= sum_residual_asks xs ms).
    { apply sum_residual_asks_pointwise_le. intros y Hy. apply Hle. right; exact Hy. }
    apply Nat.add_lt_le_mono; [exact Hlt|exact Htail_le].
  - assert (Hx_le: residual_ask x ms' <= residual_ask x ms) by (apply Hle; left; reflexivity).
    assert (Htail_strict: sum_residual_asks xs ms' < sum_residual_asks xs ms).
    { apply IH; [assumption|]. intros y Hy. apply Hle. right; exact Hy. all:assumption. }
    apply Nat.add_le_lt_mono; [exact Hx_le|exact Htail_strict].
Qed.

Lemma sum_residual_bids_drop : forall s s' b a,
  match_step s = Some s' ->
  find_feasible (bids s) (asks s) (matches s) = Some (b,a) ->
  sum_residual_bids (bids s') (matches s') < sum_residual_bids (bids s) (matches s).
Proof.
  intros s s' b a Hstep Hf.
  pose proof (match_step_bids_unchanged s s' Hstep) as Hbids.
  pose proof (residual_bid_drop s s' b a Hstep Hf) as Hstrict_b.
  pose proof (find_feasible_In_b (bids s) (asks s) (matches s) b a Hf) as Hin_b.
  assert (Hpoint: forall x, In x (bids s) -> residual_bid x (matches s') <= residual_bid x (matches s)) by
    (intros x Hx; destruct (bid_eq_dec x b) as [->|Hneq]; [apply Nat.lt_le_incl; exact Hstrict_b|
       rewrite (residual_bid_unchanged s s' b a x Hstep Hf Hneq); lia]).
  rewrite Hbids.
  eapply sum_residual_bids_pointwise_strict; eauto.
Qed.


Lemma sum_residual_asks_drop : forall s s' b a,
  match_step s = Some s' ->
  find_feasible (bids s) (asks s) (matches s) = Some (b,a) ->
  sum_residual_asks (asks s') (matches s') < sum_residual_asks (asks s) (matches s).
Proof.
  intros s s' b a Hstep Hf.
  pose proof (match_step_asks_unchanged s s' Hstep) as Hasks.
  pose proof (residual_ask_drop s s' b a Hstep Hf) as Hstrict_a.
  pose proof (find_feasible_In_a (bids s) (asks s) (matches s) b a Hf) as Hin_a.
  assert (Hpoint: forall x, In x (asks s) -> residual_ask x (matches s') <= residual_ask x (matches s)) by
    (intros x Hx; destruct (ask_eq_dec x a) as [->|Hneq]; [apply Nat.lt_le_incl; exact Hstrict_a|
       rewrite (residual_ask_unchanged s s' b a x Hstep Hf Hneq); lia]).
  rewrite Hasks.
  eapply sum_residual_asks_pointwise_strict; eauto.
Qed.

Lemma mu_decreases_on_match : forall s s',
  phase s = P3 -> match_step s = Some s' -> mu s' < mu s.
Proof.
  intros s s' Hp Hstep.
  unfold mu.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf;
    [|
     unfold match_step in Hstep; rewrite Hf in Hstep; discriminate].
  assert (Hsumb_strict: sum_residual_bids (bids s') (matches s') < sum_residual_bids (bids s) (matches s))
    by (eapply sum_residual_bids_drop; eauto).
  assert (Hsuma_strict: sum_residual_asks (asks s') (matches s') < sum_residual_asks (asks s) (matches s))
    by (eapply sum_residual_asks_drop; eauto).
  lia.
Qed.

Lemma step_P3_progress_or_exit : forall s,
  phase s = P3 ->
  (exists s', match_step s = Some s') \/ (match_step s = None).
Proof.
  intros s Hp.
  unfold match_step.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:HF.
  - left. eexists. reflexivity.
  - right. reflexivity.
Qed.

Lemma step_P4_from_P3_None : forall s,
  phase s = P3 ->
  match_step s = None ->
  phase (step s) = P4.
Proof.
  intros s Hp Hnone.
  unfold step. rewrite Hp. simpl. rewrite Hnone. reflexivity.
Qed.

Lemma match_step_phase_invariant :
  forall s s', match_step s = Some s' -> phase s' = phase s.
Proof.
  intros s s' H.
  unfold match_step in H.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:?; try discriminate.
  inversion H; subst; reflexivity.
Qed.

Lemma step_P4_inversion : forall s,
  phase (step s) = P4 ->
  phase s = P3 /\ match_step s = None.
Proof.
  intros s H.
  (* Prove each part separately before any destructing *)
  assert (Hphase : phase s = P3).
  { unfold step in H.
    destruct (phase s) eqn:E; simpl in H.
    all: try discriminate H.
    all: try (rewrite E in H; discriminate H).
    reflexivity. }
  assert (Hmatch : match_step s = None).
  { unfold step in H. rewrite Hphase in H. simpl in H.
    destruct (match_step s) as [s'|] eqn:E.
    - (* H : phase s' = P4, E : match_step s = Some s' *)
      (* This case is impossible *)
      exfalso.
      (* Unfold match_step in E to see its structure *)
      unfold match_step in E.
      destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:HF; try discriminate E.
      (* Now E : Some {| ...; phase := phase s; ... |} = Some s' *)
      injection E as Heq_state.
      (* Heq_state : {| bids := bids s; ...; phase := phase s |} = s' *)
      (* Extract phase equality using f_equal *)
      assert (Hphase_eq : phase s' = phase s) by (rewrite <- Heq_state; reflexivity).
      rewrite Hphase_eq in H.
      rewrite Hphase in H.
      discriminate H.
    - reflexivity. }
  (* Now construct the final result *)
  split; [exact Hphase | exact Hmatch].
Qed.

Lemma execute_S : forall n s, execute (S n) s = execute n (step s).
Proof. reflexivity. Qed.

Lemma step_execute_comm : forall n s, step (execute n s) = execute n (step s).
Proof.
  induction n as [|n IH]; intros s.
  - reflexivity.
  - (* inductive case: goal step (execute (S n) s) = execute (S n) (step s) *)
    rewrite execute_S. rewrite execute_S.
    (* goal: step (execute n (step s)) = execute n (step (step s)) *)
    rewrite IH. reflexivity.
Qed.

Lemma execute_step_after : forall n s, execute (S n) s = step (execute n s).
Proof.
  intros n s. rewrite execute_S. symmetry. apply step_execute_comm.
Qed.

Lemma execute_add_tail : forall n m s, execute m (execute n s) = execute (n + m) s.
Proof.
  intros n m s. revert n s.
  induction m as [|m IH]; intros n s; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - (* m -> S m *)
    (* LHS *)
    rewrite step_execute_comm.
    (* step (execute n s) becomes execute n (step s) *)
    simpl.
    rewrite IH.
    rewrite Nat.add_succ_r.
    reflexivity.
Qed.

(* If match_step fails, there is no feasible pair in the current state. *)
Lemma no_feasible_from_None : forall s,
  match_step s = None -> no_feasible_prop s.
Proof.
  intros s Hnone.
  unfold match_step in Hnone.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf; try discriminate.
  unfold no_feasible_prop.
  intros b0 a0 Hb Ha.
  eapply find_feasible_None_forall; eauto.
Qed.

Lemma no_feasible_step_from_None : forall t,
  phase t = P3 -> match_step t = None -> no_feasible_prop (step t).
Proof.
  intros t Hp3 Hnone.
  unfold step; rewrite Hp3; simpl; rewrite Hnone.
  (* step t = finish_matching t; lists unchanged *)
  unfold no_feasible_prop; simpl; intros b a Hb Ha.
  (* Reduce to the property on t itself, which follows from None *)
  unfold match_step in Hnone.
  destruct (find_feasible (bids t) (asks t) (matches t)) as [[bb aa]|] eqn:Hf; [discriminate|].
  eapply find_feasible_None_forall; eauto.
Qed.

Lemma step_P5_inversion : forall t,
  phase (step t) = P5 -> phase t = P4.
Proof.
  intros t H.
  unfold step in H.
  remember (phase t) as ph eqn:Hp.
  destruct ph; simpl in H.
  - discriminate H.
  - discriminate H.
  - destruct (match_step t) eqn:Hm; simpl in H.
    + pose proof (match_step_phase_invariant t s Hm) as Hph.
      symmetry in Hp. rewrite Hp in Hph. rewrite Hph in H. discriminate.
    + discriminate H.
  - reflexivity.
  - discriminate H.
  - discriminate H.
  - symmetry in Hp; rewrite Hp in H; discriminate.
Qed.

Lemma step_P6_inversion : forall t,
  phase (step t) = P6 -> phase t = P5.
Proof.
  intros t H.
  unfold step in H.
  remember (phase t) as ph eqn:Hp.
  destruct ph; simpl in H.
  - discriminate H.
  - discriminate H.
  - destruct (match_step t) eqn:Hm; simpl in H.
    + pose proof (match_step_phase_invariant t s Hm) as Hph.
      symmetry in Hp. rewrite Hp in Hph. rewrite Hph in H. discriminate.
    + discriminate H.
  - discriminate H.
  - reflexivity.
  - discriminate H.
  - symmetry in Hp; rewrite Hp in H; discriminate.
Qed.

Lemma step_P7_inversion : forall t,
  phase (step t) = P7 -> phase t = P6 \/ phase t = P7.
Proof.
  intros t H.
  unfold step in H.
  remember (phase t) as ph eqn:Hp.
  destruct ph; simpl in H.
  - discriminate H.
  - discriminate H.
  - destruct (match_step t) eqn:Hm; simpl in H.
    + pose proof (match_step_phase_invariant t s Hm) as Hph.
      symmetry in Hp. rewrite Hp in Hph. rewrite Hph in H. discriminate.
    + discriminate H.
  - discriminate H.
  - discriminate H.
  - now left.
  - now right.
Qed.

Lemma no_feasible_preserved_after_P4 : forall t,
  (phase t = P4 \/ phase t = P5 \/ phase t = P6 \/ phase t = P7) ->
  no_feasible_prop t -> no_feasible_prop (step t).
Proof.
  intros t Hph Hnf.
  unfold no_feasible_prop in *.
  intros b a Hb Ha.
  pose proof (step_preserves_bids_asks t) as Hab.
  assert (phase t <> P2) as Hneq2.
  { intros Heq.
    destruct Hph as [H4|[H5|[H6|H7]]]; congruence. }
  assert (bids (step t) = bids t /\ asks (step t) = asks t) as [Hbids Hasks].
  { apply Hab. exact Hneq2. }
  rewrite Hbids in Hb. rewrite Hasks in Ha.
  unfold step.
  destruct (phase t) eqn:Hp; simpl in *.
  - destruct Hph as [H4|[H5|[H6|H7]]]; congruence.
  - destruct Hph as [H4|[H5|[H6|H7]]]; congruence.
  - destruct Hph as [H4|[H5|[H6|H7]]]; congruence.
  - apply Hnf; assumption.
  - apply Hnf; assumption.
  - apply Hnf; assumption.
  - apply Hnf; assumption.
Qed.

Lemma no_feasible_at_P4_index : forall s n,
  phase (execute (S n) s) = P4 -> no_feasible_prop (execute (S n) s).
Proof.
  intros s n H.
  (* Infer predecessor phase and None using step_P4_inversion *)
  set (t := execute n s).
  assert (phase (step t) = P4) as HstepP4.
  { subst t. pose proof H as H'. rewrite (execute_step_after n s) in H'. exact H'. }
  destruct (step_P4_inversion t HstepP4) as [Hp3 Hnone].
  subst t.
  (* Produce no_feasible on step (execute n s) then rewrite into goal form *)
  pose proof (no_feasible_step_from_None (execute n s) Hp3 Hnone) as Hnf.
  rewrite <- (execute_step_after n s) in Hnf.
  exact Hnf.
Qed.

Lemma no_feasible_when_phase_ge4_from_P3 :
  forall s k,
    phase s = P3 ->
    (phase (execute (S k) s) = P4 \/
     phase (execute (S k) s) = P5 \/
     phase (execute (S k) s) = P6 \/
     phase (execute (S k) s) = P7) ->
    no_feasible_prop (execute (S k) s).
Proof.
  intros s k Hp3 Hph.
  induction k as [|k IH].
  - simpl in Hph.
    destruct Hph as [H4|[H5|[H6|H7]]].
    + (* step s is P4 *)
      destruct (step_P4_inversion s H4) as [_ Hnone].
      apply no_feasible_step_from_None; assumption.
    + (* step s cannot be P5 directly from P3 *)
      unfold step in H5; rewrite Hp3 in H5; simpl in H5.
      destruct (match_step s) eqn:Hm; simpl in H5.
      * (* Some s0: phase stays P3 *)
        pose proof (match_step_phase_invariant s s0 Hm) as Hph.
        rewrite Hp3 in Hph. rewrite Hph in H5. discriminate.
      * (* None: finish_matching -> P4 *)
        discriminate.
    + (* step s cannot be P6 directly from P3 *)
      unfold step in H6; rewrite Hp3 in H6; simpl in H6.
      destruct (match_step s) eqn:Hm; simpl in H6.
      * pose proof (match_step_phase_invariant s s0 Hm) as Hph.
        rewrite Hp3 in Hph. rewrite Hph in H6. discriminate.
      * discriminate.
    + (* step s cannot be P7 directly from P3 *)
      unfold step in H7; rewrite Hp3 in H7; simpl in H7.
      destruct (match_step s) eqn:Hm; simpl in H7.
      * pose proof (match_step_phase_invariant s s0 Hm) as Hph.
        rewrite Hp3 in Hph. rewrite Hph in H7. discriminate.
      * discriminate.
  - set (t0 := execute (S k) s).
    assert (Hexec : execute (S (S k)) s = step t0).
    { subst t0. rewrite execute_step_after. reflexivity. }
    rewrite Hexec in Hph.
    destruct Hph as [H4|[H5|[H6|H7]]].
    + destruct (step_P4_inversion t0 H4) as [Ht0P3 Hnone].
      rewrite Hexec. subst t0.
      apply no_feasible_step_from_None; assumption.
    + pose proof (step_P5_inversion t0 H5) as Ht0P4.
      assert (Hnf_t0 : no_feasible_prop t0).
      { subst t0. eapply no_feasible_at_P4_index. exact Ht0P4. }
      rewrite Hexec.
      eapply no_feasible_preserved_after_P4.
      * left. exact Ht0P4.
      * exact Hnf_t0.
    + pose proof (step_P6_inversion t0 H6) as Ht0P5.
      assert (Hnf_t0 : no_feasible_prop t0).
      { apply IH. right. left. subst t0. exact Ht0P5. }
      rewrite Hexec.
      eapply no_feasible_preserved_after_P4.
      * right. left. exact Ht0P5.
      * exact Hnf_t0.
    + destruct (step_P7_inversion t0 H7) as [Ht0P6|Ht0P7].
      * assert (Hnf_t0 : no_feasible_prop t0).
        { apply IH. right. right. left. subst t0. exact Ht0P6. }
        rewrite Hexec.
        eapply no_feasible_preserved_after_P4.
        { right. right. left. exact Ht0P6. }
        exact Hnf_t0.
      * assert (Hnf_t0 : no_feasible_prop t0).
        { apply IH. right. right. right. subst t0. exact Ht0P7. }
        rewrite Hexec.
        eapply no_feasible_preserved_after_P4.
        { right. right. right. exact Ht0P7. }
        exact Hnf_t0.
Qed.

Lemma eventually_P4_with_None : forall s,
  phase s = P3 -> exists n, phase (execute (S n) s) = P4 /\ match_step (execute n s) = None.
Proof.
  intros s Hp3.
  remember (mu s) as k.
  assert (Hle: mu s <= k) by (subst; lia).
  clear Heqk.
  revert s Hp3 Hle.
  induction k as [|k IH]; intros s Hp3 Hle.
  - (* k = 0: mu s <= 0 implies mu s = 0; thus no match and immediate P4 *)
    exists 0. simpl. split.
    + unfold step; rewrite Hp3.
      destruct (match_step s) as [s'|] eqn:Hm.
      * exfalso. pose proof (mu_decreases_on_match s s' Hp3 Hm) as Hlt.
        (* Contradiction with mu s <= 0 *)
        lia.
      * reflexivity.
    + unfold execute; simpl.
      destruct (match_step s) as [s'|] eqn:Hm; [|reflexivity].
      exfalso. pose proof (mu_decreases_on_match s s' Hp3 Hm) as Hlt. lia.
  - (* k = S k: either progress with smaller measure or None *)
    destruct (match_step s) as [s'|] eqn:Hm.
    + (* progress case *)
      assert (Hlt : mu s' < mu s) by (apply mu_decreases_on_match; assumption).
      (* derive mu s' <= k from mu s = S k and Hlt *)
      assert (Hle' : mu s' <= k) by lia.
      assert (Hp3' : phase s' = P3).
      { pose proof (match_step_phase_invariant s s' Hm) as Hph.
        rewrite Hp3 in Hph. exact Hph. }
      destruct (IH s' Hp3' Hle') as [n [HP4 Hnone]].
      exists (S n). split.
      * rewrite execute_S. unfold step; rewrite Hp3; simpl. rewrite Hm. exact HP4.
      * rewrite execute_S. unfold step; rewrite Hp3; simpl. rewrite Hm. exact Hnone.
    + (* None case *)
      exists 0. simpl. split.
      * unfold step; rewrite Hp3, Hm. reflexivity.
      * unfold execute; simpl. rewrite Hm. reflexivity.
Qed.

Theorem maximality_eventually : forall s,
  phase s = P3 -> satisfies (mu_trace s) 0 maximal.
Proof.
  intros s Hp3.
  unfold maximal.
  rewrite satisfies_always_unfold.
  intros j _.
  destruct j as [|k].
  - (* phase_ge_4 is false at P3 *)
    left.
    intro Hge.
    simpl in Hge.
    destruct Hge as [H4|[H5|[H6|H7]]].
    + apply (proj1 (mu_trace_atom_at_execute s 0 (p_phase 4))) in H4.
      apply (proj1 (interp_atom_phase_4 s)) in H4. congruence.
    + apply (proj1 (mu_trace_atom_at_execute s 0 (p_phase 5))) in H5.
      apply (proj1 (interp_atom_phase_5 s)) in H5. congruence.
    + apply (proj1 (mu_trace_atom_at_execute s 0 (p_phase 6))) in H6.
      apply (proj1 (interp_atom_phase_6 s)) in H6. congruence.
    + apply (proj1 (mu_trace_atom_at_execute s 0 (p_phase 7))) in H7.
      apply (proj1 (interp_atom_phase_7 s)) in H7. congruence.
  - (* post-matching indices: if in P4..P7 then no_feasible holds *)
    destruct (phase (execute (S k) s)) eqn:Hph.
    + left.
      intro Hge.
      simpl in Hge.
      destruct Hge as [H4|[H5|[H6|H7]]].
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 4))) in H4.
        apply (proj1 (interp_atom_phase_4 (execute (S k) s))) in H4. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 5))) in H5.
        apply (proj1 (interp_atom_phase_5 (execute (S k) s))) in H5. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 6))) in H6.
        apply (proj1 (interp_atom_phase_6 (execute (S k) s))) in H6. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 7))) in H7.
        apply (proj1 (interp_atom_phase_7 (execute (S k) s))) in H7. congruence.
    + left.
      intro Hge.
      simpl in Hge.
      destruct Hge as [H4|[H5|[H6|H7]]].
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 4))) in H4.
        apply (proj1 (interp_atom_phase_4 (execute (S k) s))) in H4. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 5))) in H5.
        apply (proj1 (interp_atom_phase_5 (execute (S k) s))) in H5. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 6))) in H6.
        apply (proj1 (interp_atom_phase_6 (execute (S k) s))) in H6. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 7))) in H7.
        apply (proj1 (interp_atom_phase_7 (execute (S k) s))) in H7. congruence.
    + left.
      intro Hge.
      simpl in Hge.
      destruct Hge as [H4|[H5|[H6|H7]]].
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 4))) in H4.
        apply (proj1 (interp_atom_phase_4 (execute (S k) s))) in H4. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 5))) in H5.
        apply (proj1 (interp_atom_phase_5 (execute (S k) s))) in H5. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 6))) in H6.
        apply (proj1 (interp_atom_phase_6 (execute (S k) s))) in H6. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 7))) in H7.
        apply (proj1 (interp_atom_phase_7 (execute (S k) s))) in H7. congruence.
    + right.
      apply (proj2 (mu_trace_atom_at_execute s (S k) p_no_feasible)).
      apply (no_feasible_when_phase_ge4_from_P3 s k Hp3).
      left; exact Hph.
    + right.
      apply (proj2 (mu_trace_atom_at_execute s (S k) p_no_feasible)).
      apply (no_feasible_when_phase_ge4_from_P3 s k Hp3).
      right; left; exact Hph.
    + right.
      apply (proj2 (mu_trace_atom_at_execute s (S k) p_no_feasible)).
      apply (no_feasible_when_phase_ge4_from_P3 s k Hp3).
      right; right; left; exact Hph.
    + right.
      apply (proj2 (mu_trace_atom_at_execute s (S k) p_no_feasible)).
      apply (no_feasible_when_phase_ge4_from_P3 s k Hp3).
      right; right; right; exact Hph.
Qed.

Lemma reach_P3_from_initial : forall s,
  phase s = P1 \/ phase s = P2 -> exists n, phase (execute n s) = P3.
Proof.
  intros s [Hp1|Hp2].
  - exists 2. simpl. unfold step; rewrite Hp1. simpl. reflexivity.
  - exists 1. simpl. unfold step; rewrite Hp2. simpl. reflexivity.
Qed.

Lemma no_feasible_when_phase_ge4_from_P1_or_P2 :
  forall s k,
    (phase s = P1 \/ phase s = P2) ->
    (phase (execute (S k) s) = P4 \/
     phase (execute (S k) s) = P5 \/
     phase (execute (S k) s) = P6 \/
     phase (execute (S k) s) = P7) ->
    no_feasible_prop (execute (S k) s).
Proof.
  intros s k Hinit Hph.
  induction k as [|k IH].
  - simpl in Hph.
    destruct Hinit as [Hp1|Hp2].
    + destruct Hph as [H4|[H5|[H6|H7]]]; unfold step in *; rewrite Hp1 in *; simpl in *; discriminate.
    + destruct Hph as [H4|[H5|[H6|H7]]]; unfold step in *; rewrite Hp2 in *; unfold do_sorting in *; simpl in *; discriminate.
  - set (t0 := execute (S k) s).
    assert (Hexec : execute (S (S k)) s = step t0).
    { subst t0. rewrite execute_step_after. reflexivity. }
    rewrite Hexec in Hph.
    destruct Hph as [H4|[H5|[H6|H7]]].
    + destruct (step_P4_inversion t0 H4) as [Ht0P3 Hnone].
      rewrite Hexec. subst t0.
      apply no_feasible_step_from_None; assumption.
    + pose proof (step_P5_inversion t0 H5) as Ht0P4.
      assert (Hnf_t0 : no_feasible_prop t0).
      { subst t0. eapply no_feasible_at_P4_index. exact Ht0P4. }
      rewrite Hexec.
      eapply no_feasible_preserved_after_P4.
      * left. exact Ht0P4.
      * exact Hnf_t0.
    + pose proof (step_P6_inversion t0 H6) as Ht0P5.
      assert (Hnf_t0 : no_feasible_prop t0).
      { apply IH. subst t0. right. left. exact Ht0P5. }
      rewrite Hexec.
      eapply no_feasible_preserved_after_P4.
      * right. left. exact Ht0P5.
      * exact Hnf_t0.
    + destruct (step_P7_inversion t0 H7) as [Ht0P6|Ht0P7].
      * assert (Hnf_t0 : no_feasible_prop t0).
        { apply IH. subst t0. right. right. left. exact Ht0P6. }
        rewrite Hexec.
        eapply no_feasible_preserved_after_P4.
        { right. right. left. exact Ht0P6. }
        exact Hnf_t0.
      * assert (Hnf_t0 : no_feasible_prop t0).
        { apply IH. subst t0. right. right. right. exact Ht0P7. }
        rewrite Hexec.
        eapply no_feasible_preserved_after_P4.
        { right. right. right. exact Ht0P7. }
        exact Hnf_t0.
Qed.

Theorem maximality_from_P1_or_P2 : forall s,
  (phase s = P1 \/ phase s = P2) -> satisfies (mu_trace s) 0 maximal.
Proof.
  intros s Hinit.
  unfold maximal.
  rewrite satisfies_always_unfold.
  intros j _.
  destruct j as [|k].
  - left.
    intro Hge.
    simpl in Hge.
    destruct Hge as [H4|[H5|[H6|H7]]].
    + apply (proj1 (mu_trace_atom_at_execute s 0 (p_phase 4))) in H4.
      apply (proj1 (interp_atom_phase_4 s)) in H4.
      destruct Hinit as [Hp1|Hp2]; congruence.
    + apply (proj1 (mu_trace_atom_at_execute s 0 (p_phase 5))) in H5.
      apply (proj1 (interp_atom_phase_5 s)) in H5.
      destruct Hinit as [Hp1|Hp2]; congruence.
    + apply (proj1 (mu_trace_atom_at_execute s 0 (p_phase 6))) in H6.
      apply (proj1 (interp_atom_phase_6 s)) in H6.
      destruct Hinit as [Hp1|Hp2]; congruence.
    + apply (proj1 (mu_trace_atom_at_execute s 0 (p_phase 7))) in H7.
      apply (proj1 (interp_atom_phase_7 s)) in H7.
      destruct Hinit as [Hp1|Hp2]; congruence.
  - destruct (phase (execute (S k) s)) eqn:Hph.
    + left; intro Hge; simpl in Hge.
      destruct Hge as [H4|[H5|[H6|H7]]].
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 4))) in H4.
        apply (proj1 (interp_atom_phase_4 (execute (S k) s))) in H4. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 5))) in H5.
        apply (proj1 (interp_atom_phase_5 (execute (S k) s))) in H5. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 6))) in H6.
        apply (proj1 (interp_atom_phase_6 (execute (S k) s))) in H6. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 7))) in H7.
        apply (proj1 (interp_atom_phase_7 (execute (S k) s))) in H7. congruence.
    + left; intro Hge; simpl in Hge.
      destruct Hge as [H4|[H5|[H6|H7]]].
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 4))) in H4.
        apply (proj1 (interp_atom_phase_4 (execute (S k) s))) in H4. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 5))) in H5.
        apply (proj1 (interp_atom_phase_5 (execute (S k) s))) in H5. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 6))) in H6.
        apply (proj1 (interp_atom_phase_6 (execute (S k) s))) in H6. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 7))) in H7.
        apply (proj1 (interp_atom_phase_7 (execute (S k) s))) in H7. congruence.
    + left; intro Hge; simpl in Hge.
      destruct Hge as [H4|[H5|[H6|H7]]].
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 4))) in H4.
        apply (proj1 (interp_atom_phase_4 (execute (S k) s))) in H4. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 5))) in H5.
        apply (proj1 (interp_atom_phase_5 (execute (S k) s))) in H5. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 6))) in H6.
        apply (proj1 (interp_atom_phase_6 (execute (S k) s))) in H6. congruence.
      * apply (proj1 (mu_trace_atom_at_execute s (S k) (p_phase 7))) in H7.
        apply (proj1 (interp_atom_phase_7 (execute (S k) s))) in H7. congruence.
    + right.
      apply (proj2 (mu_trace_atom_at_execute s (S k) p_no_feasible)).
      eapply no_feasible_when_phase_ge4_from_P1_or_P2; eauto.
    + right.
      apply (proj2 (mu_trace_atom_at_execute s (S k) p_no_feasible)).
      eapply no_feasible_when_phase_ge4_from_P1_or_P2; eauto.
    + right.
      apply (proj2 (mu_trace_atom_at_execute s (S k) p_no_feasible)).
      eapply no_feasible_when_phase_ge4_from_P1_or_P2; eauto.
    + right.
      apply (proj2 (mu_trace_atom_at_execute s (S k) p_no_feasible)).
      eapply no_feasible_when_phase_ge4_from_P1_or_P2; eauto.
Qed.

