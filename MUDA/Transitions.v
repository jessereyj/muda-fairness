From Stdlib Require Import List.
From MUDA Require Import Types State Sorting Matching ClearingPrice Atoms.

(** Panel index (thesis ↔ code)

  Chapter 3 (Deterministic STS)
  - step: one-step transition over phases
  - δ: thesis-level alias for the deterministic transition function
  - execute: finite execution by iterating δ

  Chapter 4 (Preservation lemmas for lifting)
  - allocOK_after_sorting: sorting preserves allocOK
  - wf_state_step_preservation, wf_state_execute_n: wf_state preserved along execute
*)

(* finish_matching: Phase P3 → P4 transition when no feasible pair remains. *)
Definition finish_matching (s : State) : State :=
  {| bids := bids s;
     asks := asks s;
     matches := matches s;
    (* Chapter 3: clearing price is determined in Phase P4.
      The P3 -> P4 transition preserves the other state components. *)
    clearing_price := clearing_price s;
     phase := P4 |}.

(* step: one deterministic protocol step (case split on current phase). *)
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

(* δ: thesis-level alias for the deterministic transition function step. *)
Definition δ : State -> State := step.

(* allocOK_after_sorting: sorting (P2) does not change matches, so allocOK is preserved. *)
Lemma allocOK_after_sorting :
  forall s,
    phase s = P2 ->
    allocOK s ->
    allocOK (step s).
Proof.
  intros s Hp2 H.
  unfold step; rewrite Hp2; unfold do_sorting; simpl.
  exact H.
Qed.


(* execute: iterate δ for a fixed number of steps (used in Chapter 4 bridge lemma). *)
Fixpoint execute (fuel : nat) (s : State) : State :=
  match fuel with
  | 0 => s
  | S fuel' => execute fuel' (δ s)
  end.


(* wf_state_step_preservation: wf_state is invariant under a single protocol step. *)
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

(* wf_state_execute_n: wf_state is invariant along n-step executions. *)
Lemma wf_state_execute_n : forall n s,
  wf_state s -> wf_state (execute n s).
Proof.
  induction n as [|n IH]; intros s Hwf; simpl.
  - exact Hwf.
  - apply IH. apply wf_state_step_preservation. exact Hwf.
Qed.

(* cprice_field_ok_step_preservation: if the state carries a clearing_price value,
   it agrees with determine_clearing_price after one step as well. *)
Lemma cprice_field_ok_step_preservation : forall s,
  cprice_field_ok_prop s -> cprice_field_ok_prop (step s).
Proof.
  intros s H.
  unfold cprice_field_ok_prop in *.
  unfold step.
  destruct (phase s) eqn:Hp; simpl.
  - (* P1 -> P2 *) exact H.
  - (* P2 -> P3 (sorting; clearing_price preserved) *) exact H.
  - (* P3 matching; clearing_price preserved by both branches *)
    destruct (match_step s) as [s'|] eqn:Hm; simpl.
    + (* successful match: resulting phase is P3, so the property is trivial *)
      unfold match_step in Hm.
      destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf; try discriminate.
      inversion Hm; subst s'.
      rewrite Hp.
      simpl.
      exact I.
    + (* no feasible pair: finish_matching; resulting phase is P4, so the property is trivial *)
      exact I.
  - (* P4 -> P5 (do_clearing_price stores determine_clearing_price) *)
    simpl.
    destruct (determine_clearing_price s) as [c|] eqn:Hdc; simpl.
    + rewrite determine_clearing_price_do_clearing_price. exact Hdc.
    + exact I.
  - (* P5 -> P6 (state fields unchanged except phase) *)
    destruct (clearing_price s) as [c|] eqn:Hcp; simpl; [|exact I].
    (* reduce to the corresponding fact about s *)
    change (determine_clearing_price s = Some c).
    exact H.
  - (* P6 -> P7 (state fields unchanged except phase) *)
    destruct (clearing_price s) as [c|] eqn:Hcp; simpl; [|exact I].
    change (determine_clearing_price s = Some c).
    exact H.
  - (* P7 stays same *)
    rewrite Hp.
    simpl.
    exact H.
Qed.

(* cprice_field_ok_execute_n: cprice_field_ok_prop holds along n-step executions. *)
Lemma cprice_field_ok_execute_n : forall n s,
  cprice_field_ok_prop s -> cprice_field_ok_prop (execute n s).
Proof.
  induction n as [|n IH]; intros s H; simpl.
  - exact H.
  - apply IH. apply cprice_field_ok_step_preservation. exact H.
Qed.

(* cprice_post_pricing: if the state carries a clearing_price value, it is already
   in a post-pricing phase (P5, P6, or P7). *)
Definition cprice_post_pricing (s : State) : Prop :=
  forall c, clearing_price s = Some c ->
    phase s = P5 \/ phase s = P6 \/ phase s = P7.

(* cprice_post_pricing_step_preservation: cprice_post_pricing is preserved by step. *)
Lemma cprice_post_pricing_step_preservation : forall s,
  cprice_post_pricing s -> cprice_post_pricing (step s).
Proof.
  intros s Hpost c Hcp.
  unfold step in Hcp.
  unfold step.
  destruct (phase s) eqn:Hp; simpl in Hcp; simpl.
  - (* P1 -> P2 *)
    exfalso.
    specialize (Hpost c Hcp).
    destruct Hpost as [H|[H|H]]; rewrite Hp in H; discriminate.
  - (* P2 -> P3 *)
    exfalso.
    specialize (Hpost c Hcp).
    destruct Hpost as [H|[H|H]]; rewrite Hp in H; discriminate.
  - (* P3 matching *)
    destruct (match_step s) as [s'|] eqn:Hm; simpl in Hcp.
    + exfalso.
      pose proof (match_step_preserves_clearing_price s s' Hm) as Hpres.
      rewrite Hpres in Hcp.
      specialize (Hpost c Hcp).
      destruct Hpost as [H|[H|H]]; rewrite Hp in H; discriminate.
    + exfalso.
      specialize (Hpost c Hcp).
      destruct Hpost as [H|[H|H]]; rewrite Hp in H; discriminate.
  - (* P4 -> P5 *)
    left; reflexivity.
  - (* P5 -> P6 *)
    right; left; reflexivity.
  - (* P6 -> P7 *)
    right; right; reflexivity.
  - (* P7 stays same *)
    rewrite Hp.
    right; right; reflexivity.
Qed.

(* cprice_post_pricing_execute_n: cprice_post_pricing holds along n-step executions. *)
Lemma cprice_post_pricing_execute_n : forall n s,
  cprice_post_pricing s -> cprice_post_pricing (execute n s).
Proof.
  induction n as [|n IH]; intros s H; simpl.
  - exact H.
  - apply IH. apply cprice_post_pricing_step_preservation. exact H.
Qed.
