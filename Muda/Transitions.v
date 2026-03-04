(** * MUDA/Transitions.v*)
From Stdlib Require Import List Lia Sorting Permutation.
Import ListNotations.
From MUDA Require Import Types State Sorting Matching ClearingPrice.

(** Proposition-4 (Transition from P3 to P4).

    When matching terminates because no feasible buyer–seller pair exists,
    the protocol transitions from Phase P3 to Phase P4 without changing the
    submitted orders or the match record.

    Chapter 3 also specifies that the clearing price is determined in Phase P4;
    therefore the P3 -> P4 transition preserves `clearing_price`.
*)
Definition finish_matching (s : State) : State :=
  {| bids := bids s;
     asks := asks s;
     matches := matches s;
    (* Chapter 3: clearing price is determined in Phase P4.
      The P3 -> P4 transition preserves the other state components. *)
    clearing_price := clearing_price s;
     phase := P4 |}.

(** Structural Assumption-2 (Determinism) and Structural Assumption-3 (Terminal preservation).

    The deterministic STS transition function `delta` from Chapter 3 is modeled
    as `step : State -> State`. Determinism is by construction.

    For Phase P7 (terminal), Chapter 3 requires `delta(x) = x`; this is the
    `P7 => s` branch below.
*)
Definition step (s : State) : State :=
  match phase s with
  | P1 => {| bids := bids s;
             asks := asks s;
             matches := matches s;
             clearing_price := clearing_price s;
             phase := P2 |}
  | P2 => do_sorting s
  | P3 => match match_step s with
          | Some s' => s'
          | None => finish_matching s
          end
  | P4 => do_clearing_price s
    (* Proposition-5 (Clearing Price Stability After Matching).
       After Phase P4 computes `p*`, subsequent phases preserve it. *)
  | P5 => {| bids := bids s;
             asks := asks s;
             matches := matches s;
             clearing_price := clearing_price s;
             phase := P6 |}
  | P6 => {| bids := bids s;
             asks := asks s;
             matches := matches s;
             clearing_price := clearing_price s;
             phase := P7 |}
  | P7 => s (* Terminal state *)
  end.


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
    assert (In b (bids s)) by (now apply (Permutation_in b Hperm)).
    exact (Hbid b H).
  - intros a Ha_in_sorted.
    pose proof (sort_asks_perm (asks s)) as Hperm.
    assert (In a (asks s)) by (now apply (Permutation_in a Hperm)).
    exact (Hask a H).
Qed.


Fixpoint execute (fuel : nat) (s : State) : State :=
  match fuel with
  | 0 => s
  | S fuel' => execute fuel' (step s)
  end.


Lemma step_preserves_bids_asks : forall s,
  phase s <> P2 ->
  bids (step s) = bids s /\ asks (step s) = asks s.
Proof.
  intros s Hneq.
  unfold step.
  destruct (phase s) eqn:Hph.
  - (* P1 *)
    simpl; split; reflexivity.
  - (* P2: excluded by hypothesis *)
    exfalso. apply Hneq. reflexivity.
  - (* P3 *)
    destruct (match_step s) as [s'|] eqn:Hm; simpl.
    + (* match_step Some s' preserves bids/asks by definition *)
      unfold match_step in Hm.
      destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf; try discriminate.
      inversion Hm; subst; clear Hm; simpl; split; reflexivity.
    + (* None -> finish_matching preserves bids/asks *)
      simpl; split; reflexivity.
  - (* P4 *)
    unfold do_clearing_price; simpl; split; reflexivity.
  - (* P5 *) simpl; split; reflexivity.
  - (* P6 *) simpl; split; reflexivity.
  - (* P7 *) simpl; split; reflexivity.
Qed.

Lemma step_monotone_matches : forall s,
  length (matches s) <= length (matches (step s)).
Proof.
  intros s.
  unfold step.
  destruct (phase s) eqn:Hph; simpl; try lia.
  - (* P3 *)
    destruct (match_step s) as [s'|] eqn:Hm; simpl.
    + (* Some s' -> one new head match *)
      unfold match_step in Hm.
      destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:?; try discriminate.
      inversion Hm; subst; clear Hm.
      simpl.
      rewrite length_app. simpl. lia.
    + (* None -> finish_matching, no change *)
      lia.
Qed.


Lemma wf_state_step_preservation : forall s,
  wf_state s -> wf_state (step s).
Proof.
  intros s Hwf.
  unfold step.
  destruct (phase s) eqn:Hp; simpl.
  - (* P1 -> P2 *) exact Hwf.
  - (* P2 sorting — matches unchanged *) exact Hwf.
  - (* P3 matching *)
    destruct (match_step s) as [s'|] eqn:Hm.
    + (* successful match adds head respecting feasibility *)
      unfold match_step in Hm.
      destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf; try discriminate.
      inversion Hm; subst s'; clear Hm.
      intros m Hin.
      simpl in Hin.
      rewrite in_app_iff in Hin.
      destruct Hin as [Hin|Hin].
      * apply Hwf, Hin.
      * simpl in Hin. destruct Hin as [Hin|Hin]; [|contradiction].
        subst m. apply find_feasible_spec in Hf.
        unfold is_feasible in Hf.
        repeat rewrite Bool.andb_true_iff in Hf.
        destruct Hf as [[Hprice _] _].
        apply Nat.leb_le in Hprice. simpl. exact Hprice.
    + (* finish_matching; matches unchanged *) exact Hwf.
  - (* P4 clearing price *) exact Hwf.
  - (* P5 -> P6 *) exact Hwf.
  - (* P6 -> P7 *) exact Hwf.
  - (* P7 stays same *) exact Hwf.
Qed.

Lemma wf_state_execute_n : forall n s,
  wf_state s -> wf_state (execute n s).
Proof.
  induction n as [|n IH]; intros s Hwf; simpl.
  - exact Hwf.
  - apply IH. apply wf_state_step_preservation. exact Hwf.
Qed.
