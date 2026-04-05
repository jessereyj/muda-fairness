From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From LTL      Require Import Syntax Semantics.
From MUDA     Require Import Types State Sorting Matching Transitions Atoms.
From Fairness Require Import Interpretation.

(** Panel index (thesis ↔ code)

  Chapter 4 (Priority fairness)
  - priorityOK: LTL formula G(p_prioB_step) ∧ G(p_prioS_step)
  - priority_fairness_LTL_initial: main theorem (holds for all initial states)

  Note: the remaining Local lemmas relate thesis priority (prioB/prioS) to the
  deterministic refinement used by sorting/matching and establish the pointwise
  validity of the priority-step atoms.
*)

Local Open Scope LTL_scope.
Local Open Scope bool_scope.

(* priorityOK: LTL specification asserting priority-correct choice at every greedy step. *)
Definition priorityOK : LTL_formula :=
  (G (Atom p_prioB_step)) ∧ (G (Atom p_prioS_step)).

(* ------------------------------------------------------------------------- *)
(* Relating thesis priority (prioB/prioS) to the deterministic refinement. *)

(* prioB_implies_bid_priority: thesis prioB implies the deterministic refinement bid_priority. *)
Local Lemma prioB_implies_bid_priority : forall b1 b2,
  prioB b1 b2 -> bid_priority b1 b2.
Proof.
  intros b1 b2 H.
  exact (MUDA.Sorting.prioB_implies_bid_priority b1 b2 H).
Qed.

(* prioS_implies_ask_priority: thesis prioS implies the deterministic refinement ask_priority. *)
Local Lemma prioS_implies_ask_priority : forall a1 a2,
  prioS a1 a2 -> ask_priority a1 a2.
Proof.
  intros a1 a2 H.
  exact (MUDA.Sorting.prioS_implies_ask_priority a1 a2 H).
Qed.

(* Boolean comparators correspond to their Prop-level refinements. *)

(* bid_priorityb_sound: boolean comparator true ⇒ Prop-level bid_priority. *)
Local Lemma bid_priorityb_sound : forall b1 b2,
  bid_priorityb b1 b2 = true -> bid_priority b1 b2.
Proof.
  intros b1 b2 Hb.
  exact (MUDA.Sorting.bid_priorityb_true_priority b1 b2 Hb).
Qed.

(* ask_priorityb_sound: boolean comparator true ⇒ Prop-level ask_priority. *)
Local Lemma ask_priorityb_sound : forall a1 a2,
  ask_priorityb a1 a2 = true -> ask_priority a1 a2.
Proof.
  intros a1 a2 Hb.
  exact (MUDA.Sorting.ask_priorityb_true_priority a1 a2 Hb).
Qed.

(* bid_priorityb_complete: Prop-level bid_priority ⇒ boolean comparator returns true. *)
Local Lemma bid_priorityb_complete : forall b1 b2,
  bid_priority b1 b2 -> bid_priorityb b1 b2 = true.
Proof.
  intros b1 b2 Hb.
  unfold bid_priorityb.
  destruct Hb as [Hgt | [Heq Ht]].
  - apply Bool.orb_true_iff. left.
    apply Nat.ltb_lt. lia.
  - apply Bool.orb_true_iff. right.
    apply Bool.andb_true_iff. split.
    + apply Nat.eqb_eq. exact Heq.
    + apply Bool.orb_true_iff.
      destruct Ht as [Hts | [Htseq Hid]].
      * left. apply Nat.ltb_lt. exact Hts.
      * right. apply Bool.andb_true_iff. split.
        -- apply Nat.eqb_eq. exact Htseq.
        -- apply Nat.ltb_lt. exact Hid.
Qed.

(* ask_priorityb_complete: Prop-level ask_priority ⇒ boolean comparator returns true. *)
Local Lemma ask_priorityb_complete : forall a1 a2,
  ask_priority a1 a2 -> ask_priorityb a1 a2 = true.
Proof.
  intros a1 a2 Ha.
  unfold ask_priorityb.
  destruct Ha as [Hlt | [Heq Ht]].
  - apply Bool.orb_true_iff. left.
    apply Nat.ltb_lt. exact Hlt.
  - apply Bool.orb_true_iff. right.
    apply Bool.andb_true_iff. split.
    + apply Nat.eqb_eq. exact Heq.
    + apply Bool.orb_true_iff.
      destruct Ht as [Hts | [Htseq Hid]].
      * left. apply Nat.ltb_lt. exact Hts.
      * right. apply Bool.andb_true_iff. split.
        -- apply Nat.eqb_eq. exact Htseq.
        -- apply Nat.ltb_lt. exact Hid.
Qed.

(* Transitivity of the deterministic refinements. *)

(* bid_priority_trans: transitivity of the deterministic buyer refinement. *)
Local Lemma bid_priority_trans : forall b1 b2 b3,
  bid_priority b1 b2 -> bid_priority b2 b3 -> bid_priority b1 b3.
Proof.
  intros b1 b2 b3 H12 H23.
  destruct H12 as [H12p | [H12eq H12t]].
  - (* price1 > price2 *)
    left.
    destruct H23 as [H23p | [H23eq _]].
    + lia.
    + lia.
  - destruct H23 as [H23p | [H23eq H23t]].
    + left. lia.
    + right. split.
      * lia.
      * (* transitivity on (ts,id) lex *)
        destruct H12t as [H12ts | [H12tseq H12id]];
        destruct H23t as [H23ts | [H23tseq H23id]].
        -- left. lia.
        -- left. lia.
        -- left. lia.
        -- right. split; [lia|lia].
Qed.

(* ask_priority_trans: transitivity of the deterministic seller refinement. *)
Local Lemma ask_priority_trans : forall a1 a2 a3,
  ask_priority a1 a2 -> ask_priority a2 a3 -> ask_priority a1 a3.
Proof.
  intros a1 a2 a3 H12 H23.
  destruct H12 as [H12p | [H12eq H12t]].
  - (* price1 < price2 *)
    left.
    destruct H23 as [H23p | [H23eq _]].
    + lia.
    + lia.
  - destruct H23 as [H23p | [H23eq H23t]].
    + left. lia.
    + right. split.
      * lia.
      * destruct H12t as [H12ts | [H12tseq H12id]];
        destruct H23t as [H23ts | [H23tseq H23id]].
        -- left. lia.
        -- left. lia.
        -- left. lia.
        -- right. split; [lia|lia].
Qed.

(* ------------------------------------------------------------------------- *)
(* Basic existence facts about best_feasible_ask. *)

(* best_feasible_ask_none_no_feasible: if no best ask exists, all candidates are infeasible. *)
Local Lemma best_feasible_ask_none_no_feasible :
  forall b as_list ms,
    best_feasible_ask b as_list ms = None ->
    forall a', In a' as_list -> is_feasible b a' ms = false.
Proof.
  intros b as_list ms Hnone a' Hin.
  induction as_list as [|a0 asx IH]; simpl in *.
  - contradiction.
  - destruct (is_feasible b a0 ms) eqn:Hfeas.
    + destruct (best_feasible_ask b asx ms); discriminate.
    + destruct Hin as [->|Hin].
      * exact Hfeas.
      * eapply IH; eauto.
Qed.

(* best_feasible_ask_complete: existence of any feasible ask implies best_feasible_ask returns Some. *)
Local Lemma best_feasible_ask_complete :
  forall b as_list ms,
    (exists a, In a as_list /\ is_feasible b a ms = true) ->
    exists a_best, best_feasible_ask b as_list ms = Some a_best.
Proof.
  intros b as_list ms Hex.
  induction as_list as [|ah asx IH]; simpl in *.
  - destruct Hex as [a [Hin _]]. contradiction.
  - destruct Hex as [a [[Ha|Hin] Hf]].
    + subst a.
      destruct (is_feasible b ah ms) eqn:Hah; [|discriminate].
      destruct (best_feasible_ask b asx ms) as [a0|] eqn:Hrest; eauto.
    + specialize (IH (ex_intro _ a (conj Hin Hf))).
      destruct IH as [a_best Hbest].
      destruct (is_feasible b ah ms) eqn:Hah; eauto.
      rewrite Hbest. eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* Optimality of best_feasible_ask and find_feasible under the refined orders. *)

(* best_feasible_ask_best: returned best ask is maximal under ask_priority among feasible asks. *)
Local Lemma best_feasible_ask_best :
  forall b as_list ms a_best,
    best_feasible_ask b as_list ms = Some a_best ->
    forall a',
      In a' as_list ->
      is_feasible b a' ms = true ->
      ask_priority a' a_best ->
      False.
Proof.
  intros b as_list ms.
  induction as_list as [|ah asx IH];
    intros a_best Hbest a' Hin Hf Hprio; simpl in Hbest.
  - discriminate.
  - destruct (best_feasible_ask b asx ms) as [a0|] eqn:Hrest.
    + destruct (is_feasible b ah ms) eqn:Hah.
      * inversion Hbest; subst a_best; clear Hbest.
        unfold better_ask in *.
        destruct (ask_priorityb ah a0) eqn:Hcmp.
        -- (* chosen = ah *)
           destruct Hin as [->|Hin].
           ++ destruct Hprio as [Hlt | [Heq [Hts | [Htseq Hid]]]]; lia.
           ++ pose proof (ask_priorityb_sound ah a0 Hcmp) as Hah0.
              pose proof (ask_priority_trans a' ah a0 Hprio Hah0) as Ha0.
              eapply (IH a0 eq_refl a' Hin Hf Ha0).
        -- (* chosen = a0 *)
           destruct Hin as [->|Hin].
           ++ apply ask_priorityb_complete in Hprio.
              rewrite Hprio in Hcmp. discriminate.
           ++ eapply (IH a0 eq_refl a' Hin Hf Hprio).
      * inversion Hbest; subst a_best; clear Hbest.
        destruct Hin as [->|Hin].
        -- rewrite Hah in Hf. discriminate.
        -- eapply (IH a0 eq_refl a' Hin Hf Hprio).
    + destruct (is_feasible b ah ms) eqn:Hah.
      * inversion Hbest; subst a_best; clear Hbest.
        destruct Hin as [->|Hin].
        -- destruct Hprio as [Hlt | [Heq [Hts | [Htseq Hid]]]]; lia.
        -- pose proof (best_feasible_ask_none_no_feasible b asx ms Hrest a' Hin) as Hfalse.
           rewrite Hf in Hfalse. discriminate.
      * discriminate.
Qed.

(* find_feasible_none_no_feasible_bid: if no feasible pair exists, every bid has no feasible ask. *)
Local Lemma find_feasible_none_no_feasible_bid :
  forall bs as_list ms,
    find_feasible bs as_list ms = None ->
    forall b', In b' bs -> best_feasible_ask b' as_list ms = None.
Proof.
  induction bs as [|b0 bs IH]; intros as_list ms Hnone b' Hin; simpl in *.
  - contradiction.
  - destruct (best_feasible_ask b0 as_list ms) as [a0|] eqn:Hask.
    + (* if head has a feasible ask, find_feasible cannot be None *)
      simpl in Hnone.
      destruct (find_feasible bs as_list ms) as [[b2 a2]|] eqn:Hrest.
      * destruct (bid_priorityb b0 b2); discriminate Hnone.
      * discriminate Hnone.
    + destruct Hin as [->|Hin].
      * exact Hask.
      * eapply IH; eauto.
Qed.

(* find_feasible_best: chosen bid is maximal under bid_priority among bids with feasible asks. *)
Local Lemma find_feasible_best :
  forall bs as_list ms b a,
    find_feasible bs as_list ms = Some (b,a) ->
    forall b',
      In b' bs ->
      forall a',
        best_feasible_ask b' as_list ms = Some a' ->
        bid_priority b' b ->
        False.
Proof.
  induction bs as [|b0 bs IH]; intros as_list ms b a Hff b' Hin a' Hask Hprio; simpl in Hff.
  - contradiction.
  - destruct (best_feasible_ask b0 as_list ms) as [a0|] eqn:Hb0.
    + destruct (find_feasible bs as_list ms) as [[b2 a2]|] eqn:Hrest.
      * destruct (bid_priorityb b0 b2) eqn:Hcmp.
        -- inversion Hff; subst b a; clear Hff.
           destruct Hin as [->|Hin].
           ++ destruct Hprio as [Hgt | [Heq Ht]]; lia.
           ++ pose proof (bid_priorityb_sound b0 b2 Hcmp) as Hb02.
              pose proof (bid_priority_trans b' b0 b2 Hprio Hb02) as Hb'2.
              eapply (IH as_list ms b2 a2 Hrest b' Hin a' Hask Hb'2).
        -- inversion Hff; subst b a; clear Hff.
           destruct Hin as [Hin|Hin].
           ++ subst b'.
             pose proof (bid_priorityb_complete b0 b2 Hprio) as Hb.
             rewrite Hb in Hcmp. discriminate.
           ++ eapply (IH as_list ms b2 a2 Hrest b' Hin a' Hask Hprio).
      * inversion Hff; subst b a; clear Hff.
        destruct Hin as [->|Hin].
        -- destruct Hprio as [Hgt | [Heq Ht]]; lia.
        -- pose proof (find_feasible_none_no_feasible_bid bs as_list ms Hrest b' Hin) as Hnone.
           rewrite Hask in Hnone. discriminate.
    + destruct Hin as [->|Hin].
      * rewrite Hb0 in Hask. discriminate.
      * eapply (IH as_list ms b a Hff b' Hin a' Hask Hprio).
Qed.

(* ------------------------------------------------------------------------- *)
(* Priority atoms hold pointwise (hence globally on traces). *)

(* priorityB_step_ok_global: buyer-priority atom holds for every state s (pointwise). *)
Local Lemma priorityB_step_ok_global : forall s,
  priorityB_step_ok_prop s.
Proof.
  intros s Hp3.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hff; [|exact I].
  intros b' HinB Hprio Hex.
  destruct Hex as [a' [HinA Hfeas]].
  pose proof (prioB_implies_bid_priority _ _ Hprio) as Hbprio.
  destruct (best_feasible_ask_complete b' (asks s) (matches s)
            (ex_intro _ a' (conj HinA Hfeas))) as [a_best Hbest].
  eapply (find_feasible_best (bids s) (asks s) (matches s) b a); eauto.
Qed.

(* find_feasible_returns_best_ask: for the chosen bid, find_feasible returns its best feasible ask. *)
Local Lemma find_feasible_returns_best_ask :
  forall bs as_list ms b a,
    find_feasible bs as_list ms = Some (b,a) ->
    best_feasible_ask b as_list ms = Some a.
Proof.
  induction bs as [|b0 bs IH]; intros as_list ms b a H; simpl in H.
  - discriminate.
  - destruct (best_feasible_ask b0 as_list ms) as [a0|] eqn:Hask.
    + destruct (find_feasible bs as_list ms) as [[b2 a2]|] eqn:Hrest.
      * destruct (bid_priorityb b0 b2) eqn:Hprio.
        -- inversion H; subst; clear H. exact Hask.
        -- inversion H; subst b a; clear H.
           eapply (IH as_list ms b2 a2). exact Hrest.
      * inversion H; subst; clear H. exact Hask.
    + eapply (IH as_list ms b a). exact H.
Qed.

(* priorityS_step_ok_global: seller-priority atom holds for every state s (pointwise). *)
Local Lemma priorityS_step_ok_global : forall s,
  priorityS_step_ok_prop s.
Proof.
  intros s Hp3.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hff; [|exact I].
  intros a' HinA Hprio Hfeas.
  pose proof (prioS_implies_ask_priority _ _ Hprio) as Haprio.
  pose proof (find_feasible_returns_best_ask (bids s) (asks s) (matches s) b a Hff) as Hbest.
  eapply (best_feasible_ask_best b (asks s) (matches s) a); eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* LTL lift: priorityOK holds on the MUDA trace from the initial state. *)

(* priority_fairness_LTL_initial: LTL lift — priorityOK holds on μ(initial_state). *)
Theorem priority_fairness_LTL_initial :
  forall bs as_list,
    satisfies (mu_trace (initial_state bs as_list)) 0 priorityOK.
Proof.
  intros bs as_list.
  split.
  - rewrite satisfies_always_unfold.
    intros j _.
    apply (proj2 (mu_trace_atom_at_execute (initial_state bs as_list) j p_prioB_step)).
    unfold interp_atom.
    exact (priorityB_step_ok_global (execute j (initial_state bs as_list))).
  - rewrite satisfies_always_unfold.
    intros j _.
    apply (proj2 (mu_trace_atom_at_execute (initial_state bs as_list) j p_prioS_step)).
    unfold interp_atom.
    exact (priorityS_step_ok_global (execute j (initial_state bs as_list))).
Qed.
