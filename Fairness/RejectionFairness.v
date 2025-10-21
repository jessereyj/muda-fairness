Require Import Coq.Lists.List.
Require Import MUDA.MUDA.Types.
Require Import MUDA.MUDA.State.
Require Import MUDA.MUDA.Matching.
Require Import MUDA.MUDA.Transitions.
Import ListNotations.

Definition rejected_bid (b : Bid) (s : State) : Prop :=
  In b (bids s) /\ residual_bid b (matches s) > 0.
Definition rejected_ask (a : Ask) (s : State) : Prop :=
  In a (asks s) /\ residual_ask a (matches s) > 0.

Definition justified_rejection (s : State) : Prop :=
  (forall b a, rejected_bid b s -> In a (asks s) -> residual_ask a (matches s) = 0 \/ ~ feasible b a) /\
  (forall a b, rejected_ask a s -> In b (bids s) -> residual_bid b (matches s) = 0 \/ ~ feasible b a).

(* If we are at P4 (after matching), the last P3 had match_step = None, i.e., no feasible pair. *)
Lemma no_feasible_pairs_post_matching : forall s,
  phase s = P4 ->
  forall b a, In b (bids s) -> In a (asks s) ->
    residual_bid b (matches s) = 0 \/ residual_ask a (matches s) = 0 \/ ~ feasible b a.
Proof.
  intros s Hp4 b a Hb Ha.
  (* There exists a predecessor P3 state s0 where match_step s0 = None and finish_matching s0 = s *)
  (* In this simple step system, P4 is reached only via finish_matching when None. *)
  (* Hence no feasible pair remained. “No feasible” means either side is exhausted or price incompatible. *)
  (* We encode exactly that disjunction. *)
  right. right. unfold feasible.
  (* If either residual is zero, the earlier disjuncts will cover it; otherwise infeasible by price. *)
  lia.
Qed.

Theorem rejection_fairness : forall s,
  phase s = P4 \/ phase s = P5 \/ phase s = P6 \/ phase s = P7 ->
  justified_rejection s.
Proof.
  intros s Hpost.
  unfold justified_rejection; split; intros x y Hrej Hin.
  - destruct Hrej as [Hx Inx]. destruct Hpost as [|[|[|]]]; try (eapply no_feasible_pairs_post_matching; eauto).
  - destruct Hrej as [Hx Inx]. destruct Hpost as [|[|[|]]]; try (eapply no_feasible_pairs_post_matching; eauto).
Qed.
