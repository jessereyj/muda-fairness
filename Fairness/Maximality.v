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
  intros s s' b a0 a Hstep Hf Haneq.
  unfold match_step in Hstep; rewrite Hf in Hstep; inversion Hstep; subst s'; clear Hstep.
  set (ms := matches s).
  set (m := create_match b a0 ms).
  unfold residual_ask. simpl.
  change (matched_ask m) with a0.
  destruct (ask_eq_dec a0 a) as [Eeq|Eneq].
  - subst a. contradiction.
  - reflexivity.
Qed.

Lemma sum_residual_bids_drop : forall s s' b a,
  match_step s = Some s' ->
  find_feasible (bids s) (asks s) (matches s) = Some (b,a) ->
  sum_residual_bids (bids s') (matches s') < sum_residual_bids (bids s) (matches s).
Proof.
  intros s s' b a Hstep Hf.
  unfold match_step in Hstep; rewrite Hf in Hstep; inversion Hstep; subst s'; clear Hstep.
  set (ms := matches s).
  set (m := create_match b a ms).
  simpl.
  (* Split sum: matched bid strictly drops; others unchanged. *)
  assert (Hd: residual_bid b (m :: ms) < residual_bid b ms) by
    (apply residual_bid_drop with (a:=a); auto; unfold match_step; rewrite Hf; reflexivity).
  (* Rewrite list fold as explicit recursion we already have (sum_residual_bids) *)
  induction (bids s) as [|b' bs IH]; simpl.
  - inversion Hf.
  - destruct (bid_eq_dec b' b) as [->|Hneq].
  + simpl. lia.
    + simpl.
      assert (Hunch: residual_bid b' (m :: ms) = residual_bid b' ms) by
        (apply residual_bid_unchanged with (b0:=b) (a:=a); auto; unfold match_step; rewrite Hf; reflexivity).
      rewrite Hunch.
      apply IH.
Qed.

Lemma sum_residual_asks_drop : forall s s' b a,
  match_step s = Some s' ->
  find_feasible (bids s) (asks s) (matches s) = Some (b,a) ->
  sum_residual_asks (asks s') (matches s') < sum_residual_asks (asks s) (matches s).
Proof.
  intros s s' b a Hstep Hf.
  unfold match_step in Hstep; rewrite Hf in Hstep; inversion Hstep; subst s'; clear Hstep.
  set (ms := matches s).
  set (m := create_match b a ms).
  simpl.
  assert (Hd: residual_ask a (m :: ms) < residual_ask a ms) by
      (apply residual_ask_drop with (b:=b); auto; unfold match_step; rewrite Hf; reflexivity).
  induction (asks s) as [|a' asx IH]; simpl.
  - inversion Hf.
  - destruct (ask_eq_dec a' a) as [->|Hneq].
    + simpl. lia.
    + simpl.
      assert (Hunch: residual_ask a' (m :: ms) = residual_ask a' ms) by
        (apply residual_ask_unchanged with (b:=b) (a0:=a); auto; unfold match_step; rewrite Hf; reflexivity).
      rewrite Hunch.
      apply IH.
Qed.

Lemma mu_decreases_on_match : forall s s',
  phase s = P3 -> match_step s = Some s' -> mu s' < mu s.
Proof.
  intros s s' Hp Hstep.
  unfold mu.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf;
    [|discriminate Hstep].
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
  - left. eexists; reflexivity.
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

Lemma last_P3_predecessor :
  forall s n,
    phase (execute (S n) s) = P4 ->
    exists t, t = execute n s /\ phase t = P3 /\ match_step t = None.
Proof.
  intros s n H.
  induction n as [|n IH] in s, H |- *.
  - simpl in H. destruct (step_P4_inversion s H) as [Hp3 Hnone].
    exists s. repeat split; auto.
  - rewrite execute_S in H.
    specialize (IH (step s) H) as [t [Ht [Hp3 Hnone]]].
    exists (execute (S n) s). split; [reflexivity|].
    subst t. split; assumption.
Qed.

Lemma no_feasible_when_P4_reached :
  forall s n,
    phase (execute (S n) s) = P4 ->
    phase (execute n s) = P3 /\ match_step (execute n s) = None.
Proof.
  intros s n H. destruct (last_P3_predecessor s n H) as [t [-> [Hp3 Hnone]]].
  split; assumption.
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

(* Eventual exit from P3 using measure descent. *)
Lemma eventually_P4_from_P3 : forall s,
  phase s = P3 -> exists n, phase (execute n s) = P4.
Proof.
  intros s Hp3.
  remember (mu s) as k.
  revert s Hp3 Heqk.
  induction k as [|k IH]; intros s Hp3 Hk.
  - (* No residual capacity left: cannot match; next step must be P4. *)
    exists 1. simpl. unfold step; rewrite Hp3.
    destruct (match_step s) as [s'|] eqn:Hm.
    + exfalso. pose proof (mu_decreases_on_match s s' Hp3 Hm) as Hlt.
      rewrite Hk in Hlt. lia.
    + reflexivity.
  - destruct (match_step s) as [s'|] eqn:Hm.
    + (* Successful match: decrease measure and continue. *)
  assert (Hlt : mu s' < mu s) by (apply mu_decreases_on_match; assumption).
      rewrite Hk in Hlt. assert (mu s' <= k) by lia.
      specialize (IH (mu s')) as IH'.
      assert (Hp3' : phase s' = P3).
      { unfold match_step in Hm.
        destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:?; try discriminate.
        inversion Hm; subst; reflexivity. }
      apply IH' in Hp3'. 2: reflexivity.
      destruct Hp3' as [n Hn]. exists (S n). simpl. exact Hn.
    + (* None: go to P4 next. *)
      exists 1. simpl. unfold step; rewrite Hp3, Hm. reflexivity.
Qed.

(* No feasible pair persists to the P4 state at entry. *)
Lemma no_feasible_at_P4_index : forall s n,
  phase (execute (S n) s) = P4 -> no_feasible_prop (execute (S n) s).
Proof.
  intros s n H.
  destruct (no_feasible_when_P4_reached s n H) as [Hp3 Hnone].
  (* predecessor t := execute n s has match_step None; step preserves bids/asks/matches when entering P4 *)
  unfold no_feasible_prop.
  intros b a Hb Ha.
  (* Use find_feasible_None_forall on t, then transport to step t *)
  (* t = execute n s *)
  pose (t := execute n s).
  assert (Ht_none : match_step t = None) by exact Hnone.
  (* In step t, bids/asks/matches are same lists; so infeasibility persists *)
  (* show by contradiction: if feasible at step t, then feasible at t *)
  (* Here we just reuse the fact that find_feasible returned None at t, which implies no feasible pair in t *)
  eapply find_feasible_None_forall.
  - (* find_feasible (bids t) (asks t) (matches t) = None *)
    unfold match_step in Ht_none.
    destruct (find_feasible (bids t) (asks t) (matches t)) as [[bb aa]|] eqn:Hf; [discriminate|]. exact Hf.
  - all: assumption.
Qed.

Lemma no_feasible_step_from_None : forall t,
  phase t = P3 -> match_step t = None -> no_feasible_prop (step t).
Proof.
  intros t Hp3 Hnone.
  unfold step; rewrite Hp3; simpl; rewrite Hnone.
  (* step t = finish_matching t; lists unchanged *)
  unfold no_feasible_prop; simpl; intros b a Hb Ha.
  (* Reduce to the property on t itself, which follows from None *)
  apply find_feasible_None_forall with (bs := bids t) (as_list := asks t) (ms := matches t).
  - (* show find_feasible ... = None on t *)
    unfold match_step in Hnone.
    destruct (find_feasible (bids t) (asks t) (matches t)) as [[bb aa]|] eqn:Hf; [discriminate|assumption].
  - all: assumption.
Qed.

Lemma eventually_P4_with_None : forall s,
  phase s = P3 -> exists n, phase (execute (S n) s) = P4 /\ match_step (execute n s) = None.
Proof.
  intros s Hp3.
  remember (mu s) as k; revert s Hp3 Heqk.
  induction k as [|k IH]; intros s Hp3 Hk.
  - (* No residual: immediate None then P4 *)
    exists 0. simpl. split.
    + unfold step; rewrite Hp3.
      destruct (match_step s) as [s'|] eqn:Hm.
      * exfalso. pose proof (mu_decreases_on_match s s' Hp3 Hm) as Hlt.
        rewrite Hk in Hlt. lia.
      * reflexivity.
    + unfold execute; simpl.
      unfold step; rewrite Hp3.
      destruct (match_step s) as [s'|] eqn:Hm; [|reflexivity].
      exfalso. pose proof (mu_decreases_on_match s s' Hp3 Hm) as Hlt.
      rewrite Hk in Hlt. lia.
  - destruct (match_step s) as [s'|] eqn:Hm.
    + (* progress case *)
      assert (Hlt : mu s' < mu s) by (apply mu_decreases_on_match; assumption).
      rewrite Hk in Hlt. assert (mu s' <= k) by lia.
      specialize (IH (mu s')) as IH'.
      assert (Hp3' : phase s' = P3).
      { unfold match_step in Hm.
        destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:?; try discriminate.
        inversion Hm; subst; reflexivity. }
      apply IH' in Hp3'. 2: reflexivity.
      destruct Hp3' as [n [HP4 Hnone]].
      exists (S n). split.
      * simpl. exact HP4.
      * simpl. exact Hnone.
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
  exists (S n). split; [lia|].
  (* Show conjunction holds at index n: phase=4 and no_feasible *)
  split.
  - (* Atom (p_phase 4) *)
    simpl. rewrite mu_trace_at_execute. unfold interp_atom.
    rewrite HP4. reflexivity.
  - (* Atom p_no_feasible *)
    simpl. rewrite mu_trace_at_execute. unfold interp_atom.
    set (t := execute n s) in *.
    assert (Ht : phase t = P3 /\ match_step t = None) by
      (apply no_feasible_when_P4_reached in HP4; exact HP4).
    destruct Ht as [HtP3 HtNone].
    (* no_feasible holds in step t, i.e., in execute (S n) s *)
  assert (Hnf : no_feasible_prop (step t)).
  { apply no_feasible_step_from_None; assumption. }
    (* rewrite execute (S n) s as step t *)
    assert (execute (S n) s = step t) as ->.
    { subst t.
      induction n as [|n IH].
      - simpl. reflexivity.
      - simpl. rewrite IH. reflexivity. }
    exact Hnf.
Qed.

