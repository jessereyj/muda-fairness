(** * MUDA Sorting (Phase P2)
    
    Priority sorting of bids and asks.
*)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import MUDA.MUDA.Types.
Require Import MUDA.MUDA.State.
Import ListNotations.

(** ** Sorting Criteria *)

(* Bids: descending by price, then ascending by timestamp *)
Definition bid_priority (b1 b2 : Bid) : Prop :=
  price b1 > price b2 \/ (price b1 = price b2 /\ bid_id b1 < bid_id b2).

(* Asks: ascending by price, then ascending by timestamp *)
Definition ask_priority (a1 a2 : Ask) : Prop :=
  ask_price a1 < ask_price a2 \/ (ask_price a1 = ask_price a2 /\ ask_id a1 < ask_id a2).

(** ** Sorted Lists *)

Definition bids_sorted (bs : list Bid) : Prop :=
  forall i j b1 b2,
    nth_error bs i = Some b1 ->
    nth_error bs j = Some b2 ->
    i < j ->
    bid_priority b1 b2.

Definition asks_sorted (as_list : list Ask) : Prop :=
  forall i j a1 a2,
    nth_error as_list i = Some a1 ->
    nth_error as_list j = Some a2 ->
    i < j ->
    ask_priority a1 a2.

(** ** Sorting Functions *)

(* Simplified: assume sorting functions exist *)
Axiom sort_bids : list Bid -> list Bid.
Axiom sort_asks : list Ask -> list Ask.

Axiom sort_bids_correct : forall bs,
  bids_sorted (sort_bids bs).

Axiom sort_asks_correct : forall as_list,
  asks_sorted (sort_asks as_list).

(** ** Phase P2 Transition *)

Definition do_sorting (s : State) : State :=
  {| bids := sort_bids (bids s);
     asks := sort_asks (asks s);
     matches := matches s;
     clearing_price := clearing_price s;
     phase := P3 |}.