(** * MUDA/Transitions.v*)
From Stdlib Require Import List Lia.
Import ListNotations.
From MUDA Require Import Types State Sorting Matching ClearingPrice.

(* When matching finishes (no feasible pair), transition to P4 and set clearing price *)
Definition finish_matching (s : State) : State :=
  {| bids := bids s;
     asks := asks s;
     matches := matches s;
     clearing_price := determine_clearing_price s;
     phase := P4 |}.


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

(** ** Traces *)
(* Finite execution trace *)
Fixpoint execute (fuel : nat) (s : State) : State :=
  match fuel with
  | 0 => s
  | S fuel' => execute fuel' (step s)
  end.

(** ** Properties *)
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
      inversion Hm; subst; clear Hm; simpl; lia.
    + (* None -> finish_matching, no change *)
      lia.
Qed.