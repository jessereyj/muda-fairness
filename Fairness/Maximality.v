(* Fairness/Maximality.v *)
From Stdlib Require Import Arith List Lia.
Import ListNotations.
From LTL Require Import LTL.
From Fairness Require Import Interpretation.
From MUDA Require Import Types State Matching Transitions Atoms.

Local Open Scope LTL_scope.

Definition maximal : LTL_formula := F (And (Atom (p_phase 4)) (Atom p_no_feasible)).

(* --- A simple size measure to reason about leaving P3 -------------------- *)
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

Lemma mu_ge_0 : forall s, mu s >= 0.
Proof. intros; unfold mu; lia. Qed.

(* Matching a positive quantity strictly decreases mu. *)
(* Helper: residual quantity strictly drops for the matched bid/ask *)
Lemma residual_bid_drop : forall s s' b a,
  match_step s = Some s' ->
  find_feasible (bids s) (asks s) (matches s) = Some (b,a) ->
  residual_bid b (matches s') < residual_bid b (matches s).
Proof.
  intros s s' b a Hstep Hf.
  unfold match_step in Hstep; rewrite Hf in Hstep; inversion Hstep; subst s'; clear Hstep.
  set (ms := matches s).
  unfold residual_bid; simpl.
  unfold create_match; simpl.
  destruct (bid_eq_dec b b) as [_|Hneq]; [|congruence].
  replace (quantity b - (Nat.min (residual_bid b ms) (residual_ask a ms) + allocated_bid b ms)) with
          (quantity b - allocated_bid b ms - Nat.min (residual_bid b ms) (residual_ask a ms)) by lia.
  (* get residual bounds from feasibility *)
  pose proof (find_feasible_spec (bids s) (asks s) ms b a Hf) as Hfeas.
  unfold is_feasible in Hfeas.
  repeat rewrite Bool.andb_true_iff in Hfeas.
  destruct Hfeas as [[_ Hrb] Hra].
  apply Nat.leb_le in Hrb.
  apply Nat.leb_le in Hra.
  assert (Hmin1: 1 <= Nat.min (residual_bid b ms) (residual_ask a ms)).
  { destruct (Nat.le_ge_cases (residual_bid b ms) (residual_ask a ms)) as [Hle|Hge].
    - rewrite Nat.min_l by exact Hle. lia.
    - rewrite Nat.min_r by lia. lia. }
  (* Rewrite goal using rb := residual_bid b ms *)
  remember (residual_bid b ms) as rb.
  remember (residual_ask a ms) as ra.
  replace (quantity b - allocated_bid b ms) with rb by (subst rb; unfold residual_bid; lia).
  replace (quantity b - allocated_bid b ms - Nat.min (residual_bid b ms) (residual_ask a ms))
    with (rb - Nat.min rb ra) by (subst rb ra; unfold residual_bid, residual_ask; lia).
  set (q := Nat.min rb ra) in *.
  assert (Hqpos: 0 < q) by lia.
  destruct q; [lia|]. simpl. lia.
Qed.

Lemma residual_ask_drop : forall s s' b a,
  match_step s = Some s' ->
  find_feasible (bids s) (asks s) (matches s) = Some (b,a) ->
  residual_ask a (matches s') < residual_ask a (matches s).
Proof.
  intros s s' b a Hstep Hf.
  unfold match_step in Hstep; rewrite Hf in Hstep; inversion Hstep; subst s'; clear Hstep.
  set (ms := matches s).
  unfold residual_ask; simpl.
  unfold create_match; simpl.
  destruct (ask_eq_dec a a) as [_|Hneq]; [|congruence].
  replace (ask_quantity a - (Nat.min (residual_bid b ms) (residual_ask a ms) + allocated_ask a ms)) with
          (ask_quantity a - allocated_ask a ms - Nat.min (residual_bid b ms) (residual_ask a ms)) by lia.
  pose proof (find_feasible_spec (bids s) (asks s) ms b a Hf) as Hfeas.
  unfold is_feasible in Hfeas.
  repeat rewrite Bool.andb_true_iff in Hfeas.
  destruct Hfeas as [[_ Hrb] Hra].
  apply Nat.leb_le in Hrb.
  apply Nat.leb_le in Hra.
  assert (Hmin1: 1 <= Nat.min (residual_bid b ms) (residual_ask a ms)).
  { destruct (Nat.le_ge_cases (residual_bid b ms) (residual_ask a ms)) as [Hle|Hge].
    - rewrite Nat.min_l by exact Hle. lia.
    - rewrite Nat.min_r by lia. lia. }
  remember (residual_bid b ms) as rb.
  remember (residual_ask a ms) as ra.
  replace (ask_quantity a - allocated_ask a ms) with ra by (subst ra; unfold residual_ask; lia).
  replace (ask_quantity a - allocated_ask a ms - Nat.min (residual_bid b ms) (residual_ask a ms))
    with (ra - Nat.min rb ra) by (subst rb ra; unfold residual_bid, residual_ask; lia).
  set (q := Nat.min rb ra) in *.
  assert (Hqpos: 0 < q) by lia.
  destruct q; [lia|]. simpl. lia.
Qed.

(* For other bids/asks, residuals unchanged. *)
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
  change (matched_bid m) with b0.
  destruct (bid_eq_dec b0 b) as [Eeq|Eneq].
  - subst b. contradiction.
  - reflexivity.
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
  change (matched_ask m) with a0.
  destruct (ask_eq_dec a0 a) as [Eeq|Eneq].
  - subst a. contradiction.
  - reflexivity.
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


(* Pointwise-to-sum lemmas (specialized, no fold_right rewrite needed) *)

(* Pointwise-to-sum lemmas specialized to our sum definitions *)
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
  (* Pointwise: matched bid strictly drops; others unchanged (hence <=). *)
  assert (Hpoint: forall x, In x (bids s) -> residual_bid x (matches s') <= residual_bid x (matches s)) by
    (intros x Hx; destruct (bid_eq_dec x b) as [->|Hneq]; [apply Nat.lt_le_incl; exact Hstrict_b|
       rewrite (residual_bid_unchanged s s' b a x Hstep Hf Hneq); lia]).
  rewrite Hbids.
  (* Apply specialized sum lemma without converting to fold_right *)
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
     (* Impossible: match_step s = Some s' but find_feasible returned None *)
     unfold match_step in Hstep; rewrite Hf in Hstep; discriminate].
  (* Use previously proven sum-drop lemmas directly on s -> s' *)
  assert (Hsumb_strict: sum_residual_bids (bids s') (matches s') < sum_residual_bids (bids s) (matches s))
    by (eapply sum_residual_bids_drop; eauto).
  assert (Hsuma_strict: sum_residual_asks (asks s') (matches s') < sum_residual_asks (asks s) (matches s))
    by (eapply sum_residual_asks_drop; eauto).
  lia.
Qed.

(* --- Local progress/exit at P3 ------------------------------------------- *)
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

(* If we are in P3 and no feasible pair, the next phase is P4. *)
Lemma step_P4_from_P3_None : forall s,
  phase s = P3 ->
  match_step s = None ->
  phase (step s) = P4.
Proof.
  intros s Hp Hnone.
  unfold step. rewrite Hp. simpl. rewrite Hnone. reflexivity.
Qed.

(* Match-step keeps the phase (constructed state sets phase := phase s). *)
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

(* Composition lemma: running n, then m steps equals n+m total steps. *)
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

(* We no longer need an explicit predecessor enumeration lemma; we derive
   predecessor state properties on demand using execute_step_after and
   step_P4_inversion. *)

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

(* Eventual exit from P3 using measure descent. *)

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

(* No feasible pair persists to the P4 state at entry. *)
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
  unfold maximal. rewrite satisfies_eventually_unfold.
  destruct (eventually_P4_with_None s Hp3) as [n [HP4 Hnone]].
  (* We'll produce witness (S n); need to transport atoms via mu_trace_atom_at_execute. *)
  exists (S n). split; [lia|].
  (* Show conjunction holds at index n: phase=4 and no_feasible *)
  split.
  - (* Atom (p_phase 4) *)
    (* Use bridge lemma instead of manual trace_at unfolding. *)
    apply (proj2 (mu_trace_atom_at_execute s (S n) (p_phase 4))).
    (* Convert HP4 (phase (execute (S n) s)=P4) into interp_atom fact *)
    unfold interp_atom.
    (* Phase decoding path: ensure p_phase 4 inside range; we rely on direct equality path. *)
    (* Evaluate phase predicate decoding condition *)
    destruct (andb (Nat.leb (p_phase 1) (p_phase 4)) (Nat.leb (p_phase 4) (p_phase 7))) eqn:Hrange.
    2:{ (* Unexpected fallthrough, but range holds; contradiction path *) discriminate. }
    (* Range true: match branch uses nth_phase logic *)
    simpl. (* nth_phase (p_phase 4 - 10) = P4 *)
    (* Show resulting equality from HP4 *)
    exact HP4.
  - (* Atom p_no_feasible *)
    apply (proj2 (mu_trace_atom_at_execute s (S n) p_no_feasible)).
    (* Derive no_feasible_prop (execute (S n) s) as before *)
    set (t := execute n s) in *.
    assert (HstepP4 : phase (step t) = P4) by (subst t; rewrite (execute_step_after n s) in HP4; exact HP4).
    destruct (step_P4_inversion t HstepP4) as [HtP3 HtNone].
    assert (Hnf_step : no_feasible_prop (step t)) by (apply no_feasible_step_from_None; assumption).
    subst t. rewrite <- (execute_step_after n s) in Hnf_step. exact Hnf_step.
Qed.

(* --- Reaching P3 from any earlier phase (pipeline progression) --------- *)
(* Reach P3 from P1/P2 initial pipeline *)
Lemma reach_P3_from_initial : forall s,
  phase s = P1 \/ phase s = P2 -> exists n, phase (execute n s) = P3.
Proof.
  intros s [Hp1|Hp2].
  - exists 2. simpl. unfold step; rewrite Hp1. simpl. reflexivity.
  - exists 1. simpl. unfold step; rewrite Hp2. simpl. reflexivity.
Qed.

Theorem maximality_from_P1_or_P2 : forall s,
  (phase s = P1 \/ phase s = P2) -> satisfies (mu_trace s) 0 maximal.
Proof.
  intros s Hinit.
  destruct (reach_P3_from_initial s Hinit) as [n Hn].
  pose proof (maximality_eventually (execute n s) Hn) as Hmax.
  unfold maximal in *.
  rewrite satisfies_eventually_unfold.
  rewrite satisfies_eventually_unfold in Hmax.
  destruct Hmax as [m [Hm_ge [Hph4 Hnf]]].
  (* Shift the trace starting at (execute n s) by m back to original trace using execute_add_tail. *)
  exists (n + m). split; [lia|]. split.
  - (* phase 4 atom *)
    apply (proj2 (mu_trace_atom_at_execute s (n+m) (p_phase 4))).
    pose proof (proj1 (mu_trace_atom_at_execute (execute n s) m (p_phase 4)) Hph4) as Hph4_interp.
    rewrite (execute_add_tail n m s) in Hph4_interp. exact Hph4_interp.
  - (* no feasible atom *)
    apply (proj2 (mu_trace_atom_at_execute s (n+m) p_no_feasible)).
    pose proof (proj1 (mu_trace_atom_at_execute (execute n s) m p_no_feasible) Hnf) as Hnf_interp.
    rewrite (execute_add_tail n m s) in Hnf_interp. exact Hnf_interp.
Qed.

