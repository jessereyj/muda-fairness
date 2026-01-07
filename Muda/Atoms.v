(* MUDA/Atoms.v *)
From Stdlib Require Import List Arith Bool.
Import ListNotations.
From MUDA Require Import Types State Sorting Matching ClearingPrice Transitions.

Definition allocOK_prop (s : State) : Prop :=
  (forall b, In b (bids s) -> allocated_bid b (matches s) <= quantity b) /\
  (forall a, In a (asks s) -> allocated_ask a (matches s) <= ask_quantity a).

Definition no_feasible_prop (s : State) : Prop :=
  forall b a, In b (bids s) -> In a (asks s) ->
              is_feasible b a (matches s) = false.

Definition has_clearing_price_prop (s : State) : Prop :=
  exists c, determine_clearing_price s = Some c.

Definition bounds_cstar_prop (s : State) : Prop :=
  match marginal_pair s, determine_clearing_price s with
  | Some (b,a), Some c => ask_price a <= c /\ c <= price b
  | _, _ => True
  end.

(* Price rule atom: matches the tie-breaking rule used in determine_clearing_price.
   Vacuously true when no marginal pair exists (no matches). *)
Definition price_rule_prop (s : State) : Prop :=
  match marginal_pair s with
  | None => True
  | Some (b, a) =>
      let eb := (residual_bid b (matches s) =? 0) in
      let ea := (residual_ask a (matches s) =? 0) in
      determine_clearing_price s =
        (if eb && ea then Some (price b)
         else if eb then Some (price b)
         else if ea then Some (ask_price a)
         else Some (price b))
  end.

Definition matches_monotone_1_prop (s : State) : Prop :=
  forall m, In m (matches s) -> In m (matches (step s)).

Definition rejected_bid_prop (b : Bid) (s : State) : Prop :=
  In b (bids s) /\ residual_bid b (matches s) > 0.

Definition rejected_ask_prop (a : Ask) (s : State) : Prop :=
  In a (asks s) /\ residual_ask a (matches s) > 0.

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

Axiom bids_sorted_in_P3 : forall s,
  phase s = P3 -> bids_sorted (bids s).

Axiom asks_sorted_in_P3 : forall s,
  phase s = P3 -> asks_sorted (asks s).

Axiom greedy_respects_priority_bids :
  forall s b1 b2 a,
    phase s = P3 ->
    prioB b1 b2 ->
    feasible b1 a (matches s) ->
    find_feasible (bids s) (asks s) (matches s) <> Some (b2,a).

Axiom greedy_respects_priority_asks :
  forall s a1 a2 b,
    phase s = P3 ->
    prioS a1 a2 ->
    feasible b a1 (matches s) ->
    find_feasible (bids s) (asks s) (matches s) <> Some (b,a2).