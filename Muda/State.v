(**  MUDA/State.v **)
From Stdlib Require Import List Arith.
Import ListNotations.
From MUDA Require Import Types.

Inductive Phase : Type :=
  | P1  (* Order submission *)
  | P2  (* Sorting *)
  | P3  (* Matching *)
  | P4  (* Clearing price *)
  | P5  (* Notification *)
  | P6  (* Settlement *)
  | P7. (* Terminal *)

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

Definition residual_bid (b : Bid) (ms : list Match) : nat :=
  quantity b - allocated_bid b ms.

Definition residual_ask (a : Ask) (ms : list Match) : nat :=
  ask_quantity a - allocated_ask a ms.


Definition allocOK (s : State) : Prop :=
  (forall b, In b (bids s) -> allocated_bid b (matches s) <= quantity b) /\
  (forall a, In a (asks s) -> allocated_ask a (matches s) <= ask_quantity a).


Definition feasible_pair (b:Bid) (a:Ask) (ms:list Match) : Prop :=
  price b >= ask_price a
  /\ residual_bid b ms > 0
  /\ residual_ask a ms > 0.