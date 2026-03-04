(**  MUDA/State.v
     See NOTATION.md for complete thesis-to-code mapping.
**)
From Stdlib Require Import List Arith.
Import ListNotations.
From MUDA Require Import Types.

(* Phase enumeration (Chapter 3):
  P1 (submission) → P2 (sorting) → P3 (matching) →
  P4 (clearing price) → P5 (finalization) → P6 (bookkeeping) → P7 (rejection/terminal)
*)
Inductive Phase : Type :=
  | P1  (* Order submission *)
  | P2  (* Sorting *)
  | P3  (* Matching *)
  | P4  (* Clearing price *)
  | P5  (* Finalization *)
  | P6  (* Bookkeeping *)
  | P7. (* Rejection (terminal) *)

(* State record.
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

Definition initial_state (bs : list Bid) (as_list : list Ask) : State :=
  {| bids := bs;
     asks := as_list;
     matches := [];
     clearing_price := None;
     phase := P1 |}.

(* Allocation functions: sum of matched quantities.
   Thesis (Definition 5): allocB(m, b) = Σ{q | (b, s, q) ∈ m}
   
   Implementation: structural recursion over match list with decidable equality.
   These functions enable computing residuals dynamically without storing them.
*)
  (** Definition-5 (Unit Allocation).

    `allocated_bid` / `allocated_ask` compute total traded quantity for an
    agent from the match record.
  *)
Fixpoint allocated_bid (b : Bid) (ms : list Match) : nat :=
  match ms with
  | [] => 0
  | m :: ms' =>
      if bid_eq_dec (matched_bid m) b
      then match_quantity m + allocated_bid b ms'
      else allocated_bid b ms'
  end.

Fixpoint allocated_ask (a : Ask) (ms : list Match) : nat :=
  match ms with
  | [] => 0
  | m :: ms' =>
      if ask_eq_dec (matched_ask m) a
      then match_quantity m + allocated_ask a ms'
      else allocated_ask a ms'
  end.

(* Residual computation: remaining unmatched quantity.
   Thesis presents residuals as part of state, but computing them dynamically
   ensures consistency: residual = initial quantity - allocated quantity.
*)
(** Proposition-1 (Residual Non-negativity) and Proposition-2 (Conservation).

    Residuals are `nat`-valued and are defined by construction as initial
    quantity minus allocated quantity.
*)
Definition residual_bid (b : Bid) (ms : list Match) : nat :=
  quantity b - allocated_bid b ms.

Definition residual_ask (a : Ask) (ms : list Match) : nat :=
  ask_quantity a - allocated_ask a ms.


Definition allocOK (s : State) : Prop :=
  (forall b, In b (bids s) -> allocated_bid b (matches s) <= quantity b) /\
  (forall a, In a (asks s) -> allocated_ask a (matches s) <= ask_quantity a).


(** Definition-1 (Feasibility).

    A buyer–seller pair is feasible when bid price is at least ask price and
    both agents have positive residual quantities.
*)
Definition feasible_pair (b:Bid) (a:Ask) (ms:list Match) : Prop :=
  price b >= ask_price a
  /\ residual_bid b ms > 0
  /\ residual_ask a ms > 0.