(** MUDA/Atoms.v — Chapter 4 (MUDA Protocol Layer): Atomic Predicates

  This project focuses on Chapters 3–5 only:
  - Chapter 3: operational semantics (phases + deterministic transitions)
  - Chapter 4: LTL semantics over MUDA traces
  - Chapter 5: concrete executions + fairness validation

  Atomic predicates are therefore restricted to those needed for:
  - Priority fairness
  - Quantity fairness
  - Uniform price fairness
*)
From Stdlib Require Import List Arith Bool.
Import ListNotations.
From MUDA Require Import Types State Sorting Matching ClearingPrice Transitions.

Definition allocOK_prop (s : State) : Prop :=
  (forall b, allocated_bid b (matches s) <= quantity b) /\
  (forall a, allocated_ask a (matches s) <= ask_quantity a).

Definition has_clearing_price_prop (s : State) : Prop :=
  exists c, determine_clearing_price s = Some c.

Definition bounds_cstar_prop (s : State) : Prop :=
  match marginal_pair s, determine_clearing_price s with
  | Some (b,a), Some c => ask_price a <= c /\ c <= price b
  | _, _ => True
  end.

(* Price rule atom: must match determine_clearing_price. *)
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
