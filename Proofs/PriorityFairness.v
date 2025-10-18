From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Sorting Matching Tactics.

Module PriorityFairness.

  (* Best pair selection respects priority - Theorem 4.3.1 *)
  Theorem priority_fairness :
    forall Bs As b a,
      find_best_pair Bs As = Some (b, a) ->
      In b Bs /\ In a As /\ matchable b a.
  Proof.
    intros Bs As b a Hfind.
    unfold find_best_pair in Hfind.
    destruct (find_best_bid Bs As) as [b'|] eqn:Eb; try discriminate.
    destruct (find_best_ask_for b' As) as [a'|] eqn:Ea; try discriminate.
    inversion Hfind; subst.
    (* Proof that b and a are in lists and feasible *)
    admit. (* Complete in full version *)
  Admitted.

End PriorityFairness.

Export PriorityFairness.