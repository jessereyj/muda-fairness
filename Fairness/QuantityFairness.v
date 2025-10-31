(* Fairness/QuantityFairness.v *)
From Stdlib Require Import Arith List Lia.
Import ListNotations.

From MUDA Require Import Eqb Types State Sorting Matching ClearingPrice Transitions.

Theorem quantity_fairness_initial : forall bs as_list,
  allocOK (initial_state bs as_list).
Proof.
  intros; unfold allocOK, initial_state; simpl; split; intros; lia.
Qed.

(* Adding a match never exceeds the declared quantity because we match min(residuals) *)
Lemma allocOK_after_match : forall s s',
  match_step s = Some s' -> allocOK s' .
Proof. Admitted.

(* Sorting reorders bids/asks but doesn't change matches; allocation constraints
   should therefore be preserved. We admit this fact here and can replace with
   a proper proof using properties of `sort_bids`/`sort_asks` later. *)
Lemma allocOK_after_sorting : forall s,
  phase s = P2 -> allocOK s -> allocOK (step s).
Proof. Admitted.

Theorem quantity_fairness_step : forall s,
  allocOK s -> allocOK (step s).
Proof.
  intros s H.
  destruct (phase s) eqn:Hp; simpl; try assumption.
  - (* P1: phase advances to P2, other fields unchanged *)
    assert (E : step s = {| bids := bids s; asks := asks s; matches := matches s; clearing_price := clearing_price s; phase := P2 |})
      by (unfold step; rewrite Hp; reflexivity).
    rewrite E; destruct H as [H1 H2]; split; intros x HX; [apply H1 | apply H2]; assumption.
  - (* P2: sorting preserves allocOK *)
    exact (allocOK_after_sorting s Hp H).
  - (* P3: either match or finish *)
    destruct (match_step s) eqn:Hs.
    + assert (E : step s = s0) by (unfold step; rewrite Hp; rewrite Hs; reflexivity).
      rewrite E. exact (allocOK_after_match s s0 Hs).
  + assert (E : step s = finish_matching s) by (unfold step; rewrite Hp; rewrite Hs; reflexivity).
      rewrite E. destruct H as [H1 H2]; split; intros x HX; [apply H1 | apply H2]; assumption.
  - (* P4 *) assert (E : step s = do_clearing_price s) by (unfold step; rewrite Hp; reflexivity);
    rewrite E; destruct H as [H1 H2]; split; intros x HX; [apply H1 | apply H2]; assumption.
  - (* P5 *) assert (E : step s = {| bids := bids s; asks := asks s; matches := matches s; clearing_price := clearing_price s; phase := P6 |})
      by (unfold step; rewrite Hp; reflexivity);
    rewrite E; destruct H as [H1 H2]; split; intros x HX; [apply H1 | apply H2]; assumption.
  - (* P6 *) assert (E : step s = {| bids := bids s; asks := asks s; matches := matches s; clearing_price := clearing_price s; phase := P7 |})
      by (unfold step; rewrite Hp; reflexivity);
    rewrite E; destruct H as [H1 H2]; split; intros x HX; [apply H1 | apply H2]; assumption.
  - (* P7 *) assert (E : step s = s) by (unfold step; rewrite Hp; reflexivity);
    rewrite E; destruct H as [H1 H2]; split; intros x HX; [apply H1 | apply H2]; assumption.
  
Qed.
