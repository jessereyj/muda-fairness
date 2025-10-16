From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Matching Tactics.

Module QuantityFairness.

  (* Each match respects quantity bounds - Theorem 4.3.2 *)
  Lemma match_respects_quantities :
    forall b a,
      matchable b a ->
      q_ij b a <= q_b b /\ q_ij b a <= q_s a.
  Proof.
    intros b a Hm.
    unfold q_ij. split; apply Nat.le_min_l || apply Nat.le_min_r.
  Qed.

  (* All matches in state respect bounds *)
  Theorem quantity_fairness :
    forall s m,
      In m (Mt s) ->
      feasible_match m ->
      mq m <= q_b (mb m) /\ mq m <= q_s (ma m).
  Proof.
    intros s m Hin Hfeas.
    destruct Hfeas as [Hmatch Heq].
    rewrite Heq.
    apply match_respects_quantities.
    assumption.
  Qed.

End QuantityFairness.

Export QuantityFairness.