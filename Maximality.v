From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Matching Tactics.

Module Maximality.
  Theorem maximality_at_terminal :
    forall s0 sT,
      Steps s0 sT ->
      Terminal sT ->
      (forall b a, In b (Bids sT) -> In a (Asks sT) -> ~ matchable b a).
  Proof.
    intros s0 sT _ HT b a Hb Ha.
    eapply no_feasible_pairs_at_terminal; eauto.
  Qed.

  Theorem termination_exists_with_maximality :
    forall s0, exists sT, Steps s0 sT /\ Terminal sT /\
      (forall b a, In b (Bids sT) -> In a (Asks sT) -> ~ matchable b a).
  Proof.
    intros s0.
    destruct (termination_exists s0) as [sT [Hst HT]].
    exists sT; repeat split; auto.
    intros b a Hb Ha.
    eapply no_feasible_pairs_at_terminal; eauto.
  Qed.

End Maximality.

Export Maximality.
