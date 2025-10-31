(* Fairness/RejectionFairness.v *)
From Stdlib Require Import List.
Import ListNotations.

From MUDA Require Import Eqb Types State Sorting Matching ClearingPrice Transitions.


Definition rejected_bid (b : Bid) (s : State) : Prop :=
  In b (bids s) /\ residual_bid b (matches s) > 0.
Definition rejected_ask (a : Ask) (s : State) : Prop :=
  In a (asks s) /\ residual_ask a (matches s) > 0.

Definition justified_rejection (s : State) : Prop :=
  (forall b a, rejected_bid b s -> In a (asks s) -> residual_ask a (matches s) = 0 \/ is_feasible b a (matches s) = false) /\
  (forall a b, rejected_ask a s -> In b (bids s) -> residual_bid b (matches s) = 0 \/ is_feasible b a (matches s) = false).

(* If we are at P4 (after matching), the last P3 had match_step = None, i.e., no feasible pair. *)
Lemma no_feasible_pairs_post_matching : forall s,
  phase s = P4 ->
  forall b a, In b (bids s) -> In a (asks s) ->
    residual_bid b (matches s) = 0 \/ residual_ask a (matches s) = 0 \/ is_feasible b a (matches s) = false.
Proof. Admitted.


Theorem rejection_fairness : forall s,
  phase s = P4 \/ phase s = P5 \/ phase s = P6 \/ phase s = P7 ->
  justified_rejection s.
Proof. Admitted.
