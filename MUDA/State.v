(** Chapter 3 (Methodology)

  - Section 3.1: MUDA state representation (`State`, `Phase`).
  - Section 3.4: feasibility, allocation, and residual definitions.

  See NOTATION.md for complete thesis-to-code mapping.
*)
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


(* Quantity/accounting invariant used as an atomic predicate for fairness.

   Thesis (Chapter 3, Proposition 2 / Chapter 4 quantity fairness): the allocated
   quantity never exceeds the initial quantity for any agent.

  We quantify over *all* bids/asks (not just list membership) so that this
  invariant is insensitive to Phase P2 reordering and does not depend on any
  sorting permutation lemmas.
*)
Definition allocOK (s : State) : Prop :=
  (forall b, allocated_bid b (matches s) <= quantity b) /\
  (forall a, allocated_ask a (matches s) <= ask_quantity a).


(** Definition-1 (Feasibility).

    A buyer–seller pair is feasible when bid price is at least ask price and
    both agents have positive residual quantities.
*)
Definition feasible_pair (b:Bid) (a:Ask) (ms:list Match) : Prop :=
  price b >= ask_price a
  /\ residual_bid b ms > 0
  /\ residual_ask a ms > 0.


(* Chapter 4 (Atomic proposition interpretation) — math-friendly predicates.

   These are *state-level* predicates mirroring the thesis notation.
   The LTL layer in this repo interprets a fixed set of named atoms via
   `Fairness/Interpretation.v`, but the underlying predicates are defined here.
*)

Definition matched (b : Bid) (a : Ask) (q : nat) (x : State) : Prop :=
  exists m,
    In m (matches x)
    /\ matched_bid m = b
    /\ matched_ask m = a
    /\ match_quantity m = q.

Definition residualB (b : Bid) (x : State) : nat :=
  residual_bid b (matches x).

Definition residualS (a : Ask) (x : State) : nat :=
  residual_ask a (matches x).

Definition feasible (b : Bid) (a : Ask) (x : State) : Prop :=
  feasible_pair b a (matches x).