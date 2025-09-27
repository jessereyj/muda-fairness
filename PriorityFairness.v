From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Sorting Matching Tactics.

Module PriorityFairness.
  Theorem priority_fairness_selection :
    forall Bs Ss b a,
      pick_best_pair Bs Ss = Some (b,a) ->
      matchable b a ->
      (* Buyer-side: among all feasible bidders, b is top (or equal). *)
      forall b', In b' Bs ->
        (exists a', In a' Ss /\ matchable b' a') ->
        b' = b \/ PriorityB b b' /\
      (* Seller-side (relative to b): among asks feasible with b, a is top (or equal). *)
      forall a', In a' Ss ->
        matchable b a' ->
        a' = a \/ PriorityS a a'.
  Proof.
    intros Bs Ss b a Hp Hba b' HinB Hex a' HinS Hba'.
    pose proof (pick_best_pair_sound _ _ _ _ Hp) as [Hinb [Hina [Hfeas [MaxB MaxS]]]].
    (* Buyer-side *)
    specialize (MaxB b' HinB Hex). destruct MaxB as [->|Hlt]; [left; reflexivity|right; exact Hlt].
    (* Seller-side (only for asks feasible with b) *)
    specialize (MaxS a' HinS (ex_intro _ b (conj Hinb Hba'))).
    destruct MaxS as [->|Hlt]; [left|right]; assumption.
  Qed.
End PriorityFairness.

Export PriorityFairness.
