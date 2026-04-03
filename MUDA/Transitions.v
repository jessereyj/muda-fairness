From Stdlib Require Import List.
From MUDA Require Import Types State Sorting Matching ClearingPrice.

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
