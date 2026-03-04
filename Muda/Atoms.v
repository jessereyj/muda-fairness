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
  (* Chapter 4: has_cprice(x) iff the final match record is non-empty.
     In this mechanization, this is equivalent to determine_clearing_price s
     being defined (Some _), which happens exactly when a marginal pair exists.
   *)
  exists c, determine_clearing_price s = Some c.

Definition bounds_cstar_prop (s : State) : Prop :=
  match marginal_pair s, determine_clearing_price s with
  | Some (b,a), Some c => ask_price a <= c /\ c <= price b
  | _, _ => True
  end.

(* Price rule atom: matches the tie-breaking rule used in determine_clearing_price.
   Vacuously true when no marginal pair exists (no matches). *)
Definition price_rule_prop (s : State) : Prop :=
  match phase s with
  | P1 | P2 | P3 => True
  | _ =>
      match marginal_pair s with
      | None => True
      | Some (b, a) =>
          (* Chapter 3: p* depends only on whether the marginal seller is exhausted. *)
          determine_clearing_price s =
            (if (residual_ask a (matches s) =? 0)
             then Some (ask_price a)
             else Some (price b))
      end
  end.

Definition prefix {A : Type} (l1 l2 : list A) : Prop :=
  exists w, l2 = l1 ++ w.

Definition match_keep_prop (s : State) : Prop :=
  prefix (matches s) (matches (step s)).

(* Chapter 4 match finality: after matching terminates (i.e., from P4 onward),
   the match record is no longer modified by the transition function. *)
Definition match_final_prop (s : State) : Prop :=
  match phase s with
  | P4 | P5 | P6 | P7 => matches (step s) = matches s
  | _ => True
  end.

Definition occurs_bid (b : Bid) (ms : list Match) : Prop :=
  exists m, In m ms /\ matched_bid m = b.

Definition occurs_ask (a : Ask) (ms : list Match) : Prop :=
  exists m, In m ms /\ matched_ask m = a.

(** Definition-10 (Rejection at Termination).

    An agent is rejected iff it does not occur in the final match record.
*)
Definition rejected_bid_prop (b : Bid) (s : State) : Prop :=
  In b (bids s) /\ ~ occurs_bid b (matches s).

Definition rejected_ask_prop (a : Ask) (s : State) : Prop :=
  In a (asks s) /\ ~ occurs_ask a (matches s).

(** Proposition-7 (Justified Rejection at Termination).

    A rejection is justified when a rejected agent has no feasible counterpart
    in the terminal post-matching state.
*)
Definition rejection_justified_prop (s : State) : Prop :=
  (forall (b : Bid) (aa : Ask),
      rejected_bid_prop b s -> In aa (asks s) ->
      is_feasible b aa (matches s) = false)
  /\
  (forall (aa : Ask) (b : Bid),
      rejected_ask_prop aa s -> In b (bids s) ->
      is_feasible b aa (matches s) = false).

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
