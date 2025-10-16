From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Matching Tactics.

Module Maximality.

  (* Terminal state means no feasible pairs - Theorem 4.4.2 *)
  Theorem maximality_at_terminal :
    forall s,
      is_terminal s ->
      forall b a, In b (Bids s) -> In a (Asks s) -> ~ matchable b a.
  Proof.
    intros s Hterm b a Hb Ha.
    unfold is_terminal in Hterm.
    apply Hterm; assumption.
  Qed.

End Maximality.

Export Maximality.