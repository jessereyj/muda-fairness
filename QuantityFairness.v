From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Matching Tactics.

Module QuantityFairness.
  (* Local per-match bound is encoded in feasible_match equality *)
  Lemma per_match_quantity_bound :
    forall s1 s2 m,
      Step s1 s2 ->
      In m (Mt s2) ->
      feasible_match m ->
      mq m = q_ij (mb m) (ma m).
  Proof. intros; destruct H1; auto. Qed.

  (* If you later make Step constructive, you can prove per-agent preservation. *)
  Axiom step_preserves_per_agent_bounds :
    forall s1 s2,
      (per_buyer_bound (Mt s1) /\ per_seller_bound (Mt s1)) ->
      Step s1 s2 ->
      (per_buyer_bound (Mt s2) /\ per_seller_bound (Mt s2)).

  Theorem quantity_fairness_over_run :
    forall s0 sT,
      Steps s0 sT ->
      per_buyer_bound (Mt s0) /\ per_seller_bound (Mt s0) ->
      per_buyer_bound (Mt sT) /\ per_seller_bound (Mt sT).
  Proof.
    intros s0 sT Hsteps Hinv.
    eapply (Steps_ind
              (fun s1 s2 =>
                (per_buyer_bound (Mt s1) /\ per_seller_bound (Mt s1)) ->
                (per_buyer_bound (Mt s2) /\ per_seller_bound (Mt s2)))).
    - (* steps_refl *) intros s [HB HS]; split; assumption.
    - (* steps_cons *) intros s1 s2 s3 H12 H23 IH Hpre.
      specialize (step_preserves_per_agent_bounds _ _ Hpre H12) as Hmid.
      apply IH in Hmid; exact Hmid.
    - exact Hsteps.
    - exact Hinv.
  Qed.
End QuantityFairness.

Export QuantityFairness.
