(* MUDA/Atoms.v *)
From Stdlib Require Import List Arith Bool.
Import ListNotations.
From MUDA Require Import Types State Sorting Matching ClearingPrice Transitions.

(* Allocation bounds, Section 3 *)
Definition allocOK_prop (s : State) : Prop :=
  (forall b, In b (bids s) -> allocated_bid b (matches s) <= quantity b) /\
  (forall a, In a (asks s) -> allocated_ask a (matches s) <= ask_quantity a).

(* No feasible pair remains *)
Definition no_feasible_prop (s : State) : Prop :=
  forall b a, In b (bids s) -> In a (asks s) ->
              is_feasible b a (matches s) = false.

(* Clearing price is defined *)
Definition has_clearing_price_prop (s : State) : Prop :=
  exists c, determine_clearing_price s = Some c.

(* Clearing price within marginal bounds, when defined *)
Definition bounds_cstar_prop (s : State) : Prop :=
  match marginal_pair s, determine_clearing_price s with
  | Some (b,a), Some c => ask_price a <= c /\ c <= price b
  | _, _ => True
  end.

(* Existing matches persist after one step *)
Definition matches_monotone_1_prop (s : State) : Prop :=
  forall m, In m (matches s) -> In m (matches (step s)).

(* Removed unused True-stub predicates (priorityOK_prop/final_prop/maximal_prop/
  rejectionOK_prop). Fairness proofs use concrete atoms defined in
  Fairness/Interpretation.v via interp_atom and do not depend on these stubs. *)

(* Rejection fairness building blocks (Section 4.3.6) *)
Definition rejected_bid_prop (b : Bid) (s : State) : Prop :=
  In b (bids s) /\ residual_bid b (matches s) > 0.

Definition rejected_ask_prop (a : Ask) (s : State) : Prop :=
  In a (asks s) /\ residual_ask a (matches s) > 0.

(* Global justification predicate: for any remaining counterparty, either that
   side is exhausted or the pair is infeasible under current matches. *)
Definition rejection_justified_prop (s : State) : Prop :=
  (forall (b : Bid) (aa : Ask),
      rejected_bid_prop b s -> In aa (asks s) ->
      residual_ask aa (matches s) = 0 \/ is_feasible b aa (matches s) = false)
  /\
  (forall (aa : Ask) (b : Bid),
      rejected_ask_prop aa s -> In b (bids s) ->
      residual_bid b (matches s) = 0 \/ is_feasible b aa (matches s) = false).

Definition priorityB_step_ok_prop (s: State) : Prop :=
  phase s = P3 ->
  forall b1 b2 a,
    prioB b1 b2 ->
    feasible b1 a (matches s) ->
    find_feasible (bids s) (asks s) (matches s) <> Some (b2, a).

Definition priorityS_step_ok_prop (s: State) : Prop :=
  phase s = P3 ->
  forall a1 a2 b,
    prioS a1 a2 ->
    feasible b a1 (matches s) ->
    find_feasible (bids s) (asks s) (matches s) <> Some (b, a2).

(** Priority invariants and greedy selection principles used by Fairness proofs. **)
(* Invariant: within the matching phase (P3), lists remain sorted by priority. *)
Axiom bids_sorted_in_P3 : forall s,
  phase s = P3 -> bids_sorted (bids s).
(* TODO: Replace bids_sorted_in_P3.
  Plan: prove via (1) constructive sorting correctness for do_sorting establishing
  bids_sorted after P2; (2) show matching phase (step / match_step) preserves
  index-based sortedness because find_feasible only removes residual quantities
  but never reorders lists; (3) chain phase progression P2 -> P3 invariant.
  This will yield a lemma bids_sorted_in_P3_constructive without using an axiom. *)

Axiom asks_sorted_in_P3 : forall s,
  phase s = P3 -> asks_sorted (asks s).
(* TODO: Replace asks_sorted_in_P3 similarly to bids: sorting correctness +
  preservation under matching + phase transition argument. *)

(* Greedy selection respects priority: a dominated counterparty is never chosen
   if a strictly better feasible one exists. These reflect the left-to-right
   scan of find_feasible and are convenient Section 4 hooks. *)
Axiom greedy_respects_priority_bids :
  forall s b1 b2 a,
    phase s = P3 ->
    prioB b1 b2 ->
    feasible b1 a (matches s) ->
    find_feasible (bids s) (asks s) (matches s) <> Some (b2,a).
(* TODO: Derive greedy_respects_priority_bids constructively.
   Outline: prove a specification lemma for find_feasible stating it returns
   the first feasible (b,a) in left-to-right traversal; combine with sortedness
   and prioB transitivity to show any dominated b2 cannot be chosen while a
   strictly better feasible b1 exists earlier in the list. *)

Axiom greedy_respects_priority_asks :
  forall s a1 a2 b,
    phase s = P3 ->
    prioS a1 a2 ->
    feasible b a1 (matches s) ->
    find_feasible (bids s) (asks s) (matches s) <> Some (b,a2).
(* TODO: Derive greedy_respects_priority_asks symmetrically using the
   analogous find_feasible traversal argument for asks dimension. *)