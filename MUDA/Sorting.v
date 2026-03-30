(** Chapter 3 (Methodology) — Priority Ordering + Phase P2 Sorting

  This file provides:
  - thesis-level priority relations `prioB` / `prioS`
  - deterministic tie-broken priority relations (`bid_priority` / `ask_priority`)
  - an executable, deterministic sorting function used in Phase P2

  Note: Fairness proofs do not rely on sorting correctness; the matching
  step selects the highest-priority feasible buyer/seller directly.
*)
From Stdlib Require Import List Arith Bool.
Import ListNotations.
From MUDA Require Import Types State.

Local Open Scope bool_scope.

(* Thesis priority (Definition 7) *)
Definition prioB (b1 b2 : Bid) : Prop :=
  price b1 > price b2 \/
  (price b1 = price b2 /\ ts b1 < ts b2).

Definition prioS (a1 a2 : Ask) : Prop :=
  ask_price a1 < ask_price a2 \/
  (ask_price a1 = ask_price a2 /\ ask_ts a1 < ask_ts a2).

(* Deterministic refinement (adds IDs as a final tie-breaker). *)
Definition bid_priority (b1 b2 : Bid) : Prop :=
  price b1 > price b2 \/
  (price b1 = price b2 /\
     (ts b1 < ts b2 \/ (ts b1 = ts b2 /\ bid_id b1 < bid_id b2))).

Definition ask_priority (a1 a2 : Ask) : Prop :=
  ask_price a1 < ask_price a2 \/
  (ask_price a1 = ask_price a2 /\
     (ask_ts a1 < ask_ts a2 \/ (ask_ts a1 = ask_ts a2 /\ ask_id a1 < ask_id a2))).

(* Boolean comparators for executable sorting. *)
Definition bid_priorityb (b1 b2 : Bid) : bool :=
  Nat.ltb (price b2) (price b1)
  || (Nat.eqb (price b1) (price b2)
      && (Nat.ltb (ts b1) (ts b2)
          || (Nat.eqb (ts b1) (ts b2) && Nat.ltb (bid_id b1) (bid_id b2)))).

Definition ask_priorityb (a1 a2 : Ask) : bool :=
  Nat.ltb (ask_price a1) (ask_price a2)
  || (Nat.eqb (ask_price a1) (ask_price a2)
      && (Nat.ltb (ask_ts a1) (ask_ts a2)
          || (Nat.eqb (ask_ts a1) (ask_ts a2) && Nat.ltb (ask_id a1) (ask_id a2)))).

Fixpoint insert_bid (b : Bid) (bs : list Bid) : list Bid :=
  match bs with
  | [] => [b]
  | x :: xs => if bid_priorityb b x then b :: x :: xs else x :: insert_bid b xs
  end.

Fixpoint insert_ask (a : Ask) (asx : list Ask) : list Ask :=
  match asx with
  | [] => [a]
  | x :: xs => if ask_priorityb a x then a :: x :: xs else x :: insert_ask a xs
  end.

Fixpoint sort_bids (bs : list Bid) : list Bid :=
  match bs with
  | [] => []
  | b :: bs' => insert_bid b (sort_bids bs')
  end.

Fixpoint sort_asks (asx : list Ask) : list Ask :=
  match asx with
  | [] => []
  | a :: as' => insert_ask a (sort_asks as')
  end.

Definition do_sorting (s : State) : State :=
  {| bids := sort_bids (bids s);
     asks := sort_asks (asks s);
     matches := matches s;
     clearing_price := clearing_price s;
     phase := P3 |}.
