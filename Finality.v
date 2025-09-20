From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Matching Temporal Tactics.

Module Finality.
  Theorem match_finality_monotone :
    forall s0 sT, Steps s0 sT -> monotone_Mt (Mt s0) (Mt sT).
  Proof. intros; now apply steps_monotone. Qed.
End Finality.

Export Finality.
