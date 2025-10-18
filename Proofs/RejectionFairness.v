From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Matching Tactics.

Module RejectionFairness.

  (* Buyer not in final match means no feasible seller - Theorem 4.4.3 *)
  Definition in_final_matches (b:Bid) (s:State) : Prop :=
    exists m, In m (Mt s) /\ mb m = b.

  Theorem rejection_fairness_buyer :
    forall s b,
      is_terminal s ->
      In b (Bids s) ->
      ~ in_final_matches b s ->
      forall a, In a (Asks s) -> ~ matchable b a.
  Proof.
    intros s b Hterm Hb Hnot a Ha.
    unfold is_terminal in Hterm.
    apply Hterm; assumption.
  Qed.

End RejectionFairness.

Export RejectionFairness.