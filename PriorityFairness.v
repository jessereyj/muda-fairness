From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Sorting Matching Tactics.

Module PriorityFairness.
  Theorem priority_fairness_selection :
    forall Bs Ss b a,
      HighestFeasibleB Bs Ss = Some b ->
      LowestFeasibleS  Bs Ss = Some a ->
      matchable b a ->
      forall b', In b' Bs ->
        (exists a', In a' Ss /\ matchable b' a') ->
        b' = b \/ PriorityB b b'.
  Proof.
    intros Bs Ss b a HB HA Hba b' Hin Hex.
    (* Keep the existential witness and all conjuncts to avoid dependent-elim issues *)
    destruct (HighestFeasibleB_sound _ _ _ HB)
      as [a0 [Hinb [Hina [HfeasB Hall]]]].
    (* Now use the “no lower outranks selected b” clause *)
    specialize (Hall b' Hin Hex).
    exact Hall.
  Qed.
End PriorityFairness.

Export PriorityFairness.
