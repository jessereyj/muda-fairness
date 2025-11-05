(* Fairness/PriorityFairness.v *)
From Stdlib Require Import List.
Import ListNotations.
From MUDA Require Import Eqb Types State Sorting Matching ClearingPrice Transitions.

(** Core, provable hooks for Priority Fairness (Section 3 & 4) *)
(* 1) If find_feasible returns (b,a), then (a) the pair is feasible,
      (b) b ∈ bids, and (c) a ∈ asks. *)
Lemma find_feasible_in_lists :
  forall bs as_list ms b a,
    find_feasible bs as_list ms = Some (b,a) ->
    is_feasible b a ms = true /\
    In b bs /\ In a as_list.
Proof.
  induction bs as [|b0 bs IH]; intros as_list ms b a H; simpl in H.
  - discriminate.
  - destruct (pick_ask b0 as_list ms) as [a0|] eqn:Hpick.
    + inversion H; subst b a; clear H.
      split.
      * eapply pick_ask_spec; eauto.
      * split; [left; reflexivity|].
        (* pick_ask returns Some a0 means a0 ∈ as_list *)
        (* simple membership proof by scanning as_list as pick_ask does *)
        revert as_list Hpick; induction as_list as [|ah asx IHas]; simpl; intro Hpick.
        { discriminate. }
        destruct (is_feasible b0 ah ms) eqn:?; [inversion Hpick; subst; now left|].
        right. apply IHas; exact Hpick.
    + apply IH in H. destruct H as [Hf [HinB HinA]].
      split; [assumption|]. split; [right; exact HinB | exact HinA].
Qed.

(* 2) Shape of match_step on success: it conses the created match *)
Lemma match_step_head_is_create :
  forall s s',
    match_step s = Some s' ->
    exists b a, matches s' = create_match b a (matches s) :: matches s.
Proof.
  intros s s' H.
  unfold match_step in H.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf; try discriminate.
  inversion H; subst; clear H.
  eexists b, a; reflexivity.
Qed.

(* 3) Price bound of the chosen head match after a successful step *)
Lemma match_step_head_price_bound :
  forall s s' b a,
    match_step s = Some s' ->
    matches s' = create_match b a (matches s) :: matches s ->
    ask_price a <= price b.
Proof.
  intros s s' b a Hstep Hhd.
  unfold match_step in Hstep.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b0 a0]|] eqn:Hf; try discriminate.
  inversion Hstep; subst; clear Hstep. simpl in Hhd.
  inversion Hhd; subst; clear Hhd.
  (* use the feasibility spec of find_feasible *)
  apply find_feasible_spec in Hf.
  unfold is_feasible in Hf.
  repeat rewrite Bool.andb_true_iff in Hf.
  destruct Hf as [[Hp _] _]. now apply Nat.leb_le in Hp.
Qed.
