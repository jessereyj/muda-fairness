From Stdlib Require Import List Arith.
Import ListNotations.
From MUDA Require Import Types.

(** Panel index (thesis ↔ code)

  Chapter 3 (State-transition model)
  - Phase: protocol phases P1..P7
  - State: (bids, asks, matches, clearing_price, phase)
  - initial_state: construct the initial state from inputs

  Chapter 4 (Quantity accounting layer)
  - allocated_bid/allocated_ask: total matched quantity from a match record
  - residual_bid/residual_ask: remaining quantity after accounting
  - allocOK: invariant (no over-allocation) used in quantity fairness proofs
*)

(* Phase: protocol phases P1..P7 (Chapter 3).
   P1 (submission) → P2 (sorting) → P3 (matching) →
   P4 (clearing price) → P5 (finalization) → P6 (bookkeeping) → P7 (rejection/terminal) *)
Inductive Phase : Type :=
  | P1  (* Order submission *)
  | P2  (* Sorting *)
  | P3  (* Matching *)
  | P4  (* Clearing price *)
  | P5  (* Finalization *)
  | P6  (* Bookkeeping *)
  | P7. (* Rejection (terminal) *)

(* State: system state record (Chapter 3 STS state space).
   Thesis notation: x = (B, S, orders, residuals, M, p*, phase)
   Mapping:
     - bids = B (list of bids)
     - asks = S (list of asks)
     - matches = M (list of matches, append semantics: new matches added at tail)
     - clearing_price = p* (determined in P4)
     - phase = current protocol phase
   Note: "residuals" from thesis are computed via residual_bid/residual_ask,
         not stored as a separate field.
*)
Record State := {
  bids : list Bid;
  asks : list Ask;
  matches : list Match;
  clearing_price : option nat;
  phase : Phase
}.

(* initial_state: construct starting state from bid/ask inputs. *)
Definition initial_state (bs : list Bid) (as_list : list Ask) : State :=
  {| bids := bs;
     asks := as_list;
     matches := [];
     clearing_price := None;
     phase := P1 |}.

(* allocated_bid: total quantity of b appearing in the match record. *)
Fixpoint allocated_bid (b : Bid) (ms : list Match) : nat :=
  match ms with
  | [] => 0
  | m :: ms' =>
      if bid_eq_dec (matched_bid m) b
      then match_quantity m + allocated_bid b ms'
      else allocated_bid b ms'
  end.

(* allocated_ask: total quantity of a appearing in the match record. *)
Fixpoint allocated_ask (a : Ask) (ms : list Match) : nat :=
  match ms with
  | [] => 0
  | m :: ms' =>
      if ask_eq_dec (matched_ask m) a
      then match_quantity m + allocated_ask a ms'
      else allocated_ask a ms'
  end.

(* residual_bid: remaining (unmatched) quantity for bid b. *)
Definition residual_bid (b : Bid) (ms : list Match) : nat :=
  quantity b - allocated_bid b ms.

(* residual_ask: remaining (unmatched) quantity for ask a. *)
Definition residual_ask (a : Ask) (ms : list Match) : nat :=
  ask_quantity a - allocated_ask a ms.

(* allocOK: no bid/ask is allocated beyond its initial quantity (invariant). *)
Definition allocOK (s : State) : Prop :=
  (forall b, allocated_bid b (matches s) <= quantity b) /\
  (forall a, allocated_ask a (matches s) <= ask_quantity a).