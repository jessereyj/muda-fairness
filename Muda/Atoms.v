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

(* Stubs to replace with your concrete Section 3 predicates *)
Definition priorityOK_prop  (s : State) : Prop := True.
Definition final_prop       (s : State) : Prop := True.
Definition maximal_prop     (s : State) : Prop := True.
Definition rejectionOK_prop (s : State) : Prop := True.

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
