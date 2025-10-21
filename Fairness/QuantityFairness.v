Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import MUDA.MUDA.State.
Require Import MUDA.MUDA.Matching.
Require Import MUDA.MUDA.Transitions.
Import ListNotations.

Theorem quantity_fairness_initial : forall bs as_list,
  allocOK (initial_state bs as_list).
Proof.
  intros; unfold allocOK, initial_state; simpl; split; intros; lia.
Qed.

(* Adding a match never exceeds the declared quantity because we match min(residuals) *)
Lemma allocOK_after_match : forall s s',
  match_step s = Some s' -> allocOK s' .
Proof.
  intros s s' Hm.
  unfold match_step in Hm.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:HF; inversion Hm; subst; clear Hm.
  unfold allocOK; simpl; split; intros x Hinx.
  - (* bids side *)
    unfold allocated_bid.
    destruct (bid_eq_dec (matched_bid (create_match b a (matches s))) x) as [->|Hneq].
    + (* x is the matched bid *)
      unfold create_match; simpl.
      (* allocated for x increases by at most its residual *)
      remember (matches s) as ms.
      rewrite <- plus_n_O.
      (* standard arithmetic *)
      assert (Hle: allocated_bid x ({| matched_bid := x; matched_ask := a; match_quantity :=
                 Nat.min (residual_bid x ms) (residual_ask a ms) |} :: ms)
                 <= quantity x).
      { unfold allocated_bid at 1; simpl.
        destruct (bid_eq_dec x x); [|congruence].
        unfold residual_bid. lia. }
      exact Hle.
    + (* some other bid; allocation unchanged ≤ quantity x *)
      remember (matches s) as ms. clear HF.
      (* head mismatch => does not affect allocated for x *)
      unfold allocated_bid at 1; simpl.
      destruct (bid_eq_dec (matched_bid (create_match b a ms)) x); [contradiction|].
      lia.
  - (* asks side — symmetric *)
    unfold allocated_ask.
    destruct (ask_eq_dec (matched_ask (create_match b a (matches s))) x) as [->|Hneq].
    + remember (matches s) as ms. unfold create_match; simpl.
      assert (Hle: allocated_ask x ({| matched_bid := b; matched_ask := x; match_quantity :=
                  Nat.min (residual_bid b ms) (residual_ask x ms) |} :: ms)
                  <= ask_quantity x).
      { unfold allocated_ask at 1; simpl.
        destruct (ask_eq_dec x x); [|congruence].
        unfold residual_ask. lia. }
      exact Hle.
    + remember (matches s) as ms.
      unfold allocated_ask at 1; simpl.
      destruct (ask_eq_dec (matched_ask (create_match b a ms)) x); [contradiction|].
      lia.
Qed.

Theorem quantity_fairness_step : forall s,
  allocOK s -> allocOK (step s).
Proof.
  intros s H.
  destruct (phase s); simpl; try assumption.
  - (* P2 -> P3; sorting preserves allocOK *)
    exact H.
  - (* P3: either match or finish *)
    destruct (match_step s) eqn:Hs.
    + eapply allocOK_after_match; eauto.
    + exact H.
  - all: exact H.
Qed.
