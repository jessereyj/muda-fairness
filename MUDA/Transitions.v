From Stdlib Require Import List.
From MUDA Require Import Types State Sorting Matching ClearingPrice.

Definition finish_matching (s : State) : State :=
  {| bids := bids s;
     asks := asks s;
     matches := matches s;
    (* Chapter 3: clearing price is determined in Phase P4.
      The P3 -> P4 transition preserves the other state components. *)
    clearing_price := clearing_price s;
     phase := P4 |}.

(** Chapter 3 properties: determinism and terminal preservation.

    The deterministic STS transition function `δ` from Chapter 3 is modeled
    as `δ : State -> State`. Determinism is by construction.

    For Phase P7 (terminal), Chapter 3 requires `δ(x) = x`; this is the
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

(** Thesis-level alias: δ is the deterministic transition function. *)
Definition δ : State -> State := step.


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


Fixpoint execute (fuel : nat) (s : State) : State :=
  match fuel with
  | 0 => s
  | S fuel' => execute fuel' (δ s)
  end.


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
