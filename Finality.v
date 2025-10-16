From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Matching Tactics.

Module Finality.

  (* Single step preserves monotonicity *)
  Lemma match_step_preserves_monotone :
    forall s, monotone_Mt (Mt s) (Mt (match_step s)).
  Proof.
    intros s.
    apply match_step_monotone.
  Qed.

  (* Full execution preserves monotonicity - Theorem 4.4.1 *)
  Theorem match_finality_monotone :
    forall fuel s0, 
      monotone_Mt (Mt s0) (Mt (greedy_match fuel s0)).
  Proof.
    intros fuel s0.
    apply greedy_match_monotone.
  Qed.

End Finality.

Export Finality.