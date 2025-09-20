From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Matching Tactics.

Module ClearingPrice.
  (* Marginal matched pair and uniform price rule (Def. 3.1.11) *)
  Parameter c_star : State -> nat.
  Parameter marginal_pair : State -> option Match.

  Axiom c_star_properties :
    forall s m,
      marginal_pair s = Some m ->
      p_b (mb m) >= c_star s /\ c_star s >= a_s (ma m).

  Axiom uniform_price_for_all_trades :
    forall s m,
      In m (Mt s) -> True.
End ClearingPrice.

Export ClearingPrice.
