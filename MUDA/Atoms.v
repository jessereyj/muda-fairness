From Stdlib Require Import List Arith Bool.
From MUDA Require Import Types State Sorting Matching ClearingPrice Transitions.

(** Panel index (thesis ↔ code)

  Chapter 4 (Atomic propositions over MUDA states)
  - allocOK_prop: quantity accounting atom (initial = allocated + residual)
  - has_clearing_price_prop, bounds_pstar_prop, price_rule_prop: price fairness atoms
  - priorityB_step_ok_prop, priorityS_step_ok_prop: priority-step correctness atoms
*)

(* Chapter 4 quantity fairness notation:
  initial(b) = sum_matches(b, x) + residual_bid(b, matches(x))

   In this mechanization:
  - `sum_matches` is `allocated_*`
  - residuals are `residual_* = initial - allocated_*` (computed, not stored)
*)
(* allocOK_prop: atom asserting exact quantity accounting (allocated + residual = initial). *)
Definition allocOK_prop (s : State) : Prop :=
  (forall b, quantity b = allocated_bid b (matches s) + residual_bid b (matches s)) /\
  (forall a, ask_quantity a = allocated_ask a (matches s) + residual_ask a (matches s)).

(* has_clearing_price_prop: atom asserting that determine_clearing_price returns Some c. *)
Definition has_clearing_price_prop (s : State) : Prop :=
  exists c, determine_clearing_price s = Some c.

(* bounds_pstar_prop: atom asserting clearing price bounds w.r.t. the marginal pair (when defined). *)
Definition bounds_pstar_prop (s : State) : Prop :=
  match marginal_pair s, determine_clearing_price s with
  | Some (b,a), Some c => ask_price a <= c /\ c <= price b
  | _, _ => True
  end.



(* Price rule atom: must match determine_clearing_price. *)
(* price_rule_prop: atom asserting the deterministic price-selection rule after P3. *)
Definition price_rule_prop (s : State) : Prop :=
  match phase s with
  | P1 | P2 | P3 => True
  | _ =>
      match marginal_pair s with
      | None => True
      | Some (b, a) =>
          determine_clearing_price s =
            (if (residual_ask a (matches s) =? 0)
             then Some (price b)
             else Some (ask_price a))
      end
  end.

(* Priority fairness atoms.

  These are phrased directly in terms of the executable greedy selector:
  - `find_feasible` selects the highest-priority feasible buyer
  - `best_feasible_ask` selects the highest-priority feasible seller for that buyer
*)
(* priorityB_step_ok_prop: atom asserting greedy buyer choice respects priority among feasible buyers. *)
Definition priorityB_step_ok_prop (s : State) : Prop :=
  phase s = P3 ->
  match find_feasible (bids s) (asks s) (matches s) with
  | None => True
  | Some (b, _) =>
      forall b',
      In b' (bids s) ->
        prioB b' b ->
        ~ exists a', In a' (asks s) /\ feasible b' a' (matches s)
  end.

(* priorityS_step_ok_prop: atom asserting greedy seller choice respects priority among feasible sellers. *)
Definition priorityS_step_ok_prop (s : State) : Prop :=
  phase s = P3 ->
  match find_feasible (bids s) (asks s) (matches s) with
  | None => True
  | Some (b, a) =>
      forall a',
        In a' (asks s) ->
        prioS a' a ->
        feasible b a' (matches s) ->
        False
  end.
