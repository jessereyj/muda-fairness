From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import Tactics MudaCore Sorting Matching ClearingPrice Temporal
               PriorityFairness QuantityFairness Finality Maximality RejectionFairness.

Section MUDA_Fairness.
  Variable s0 : State.

  Theorem MUDA_fairness_summary :
    exists sT,
      Steps s0 sT /\
      Terminal sT /\
      monotone_Mt (Mt s0) (Mt sT) /\
      (forall b a, In b (Bids sT) -> In a (Asks sT) -> ~ matchable b a).
  Proof.
    destruct (termination_exists_with_maximality s0) as [sT [HS [HT Hmax]]].
    exists sT; repeat split; auto.
    now apply steps_monotone.
  Qed.
End MUDA_Fairness.

