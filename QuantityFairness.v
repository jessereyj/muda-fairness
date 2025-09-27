From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Matching Tactics.

Module QuantityFairness.
  Lemma per_match_quantity_bound :
    forall s1 s2 m,
      Step s1 s2 ->
      In m (Mt s2) ->
      feasible_match m ->
      mq m = q_ij (mb m) (ma m).
  Proof. intros; destruct H1; auto. Qed.

  Lemma step_preserves_per_agent_bounds :
    forall s1 s2,
      (per_buyer_bound (Mt s1) /\ per_seller_bound (Mt s1)) ->
      Step s1 s2 ->
      (per_buyer_bound (Mt s2) /\ per_seller_bound (Mt s2)).
  Proof.
    intros [Bs Ss M] [Bs' Ss' M'] [HB HS] H; inversion H; subst; simpl in *.
    split.
    - (* buyers *)
      unfold per_buyer_bound in *.
      intros b m HinM2 Uses.
      apply in_app_or in HinM2 as [HinOld|HinNew].
      + (* old matches keep their bounds *)
        eauto.
      + (* new match (the one we appended) *)
        destruct HinNew as [Hin|[]]; subst.
        simpl in Uses. subst b.
        cbn. unfold feasible_match.
        (* For the appended match, mq = min(q_b b, q_s a) <= q_b b *)
        lia.
    - (* sellers *)
      unfold per_seller_bound in *.
      intros a0 m HinM2 Uses.
      apply in_app_or in HinM2 as [HinOld|HinNew].
      + eauto.
      + destruct HinNew as [Hin|[]]; subst.
        simpl in Uses. subst a0. cbn. lia.
  Qed.

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
    - intros s [HB HS]; split; assumption.
    - intros s1 s2 s3 H12 H23 IH Hpre.
      specialize (step_preserves_per_agent_bounds _ _ Hpre H12) as Hmid.
      apply IH in Hmid; exact Hmid.
    - exact Hsteps.
    - exact Hinv.
  Qed.
End QuantityFairness.

Export QuantityFairness.
