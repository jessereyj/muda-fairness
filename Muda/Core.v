From Coq Require Import List Arith Lia.
Import ListNotations.

(* Define Exhaustion OUTSIDE module to avoid signature issues *)
Inductive Exhaustion : Type :=
| BuyerExhausted : Exhaustion
| SellerExhausted : Exhaustion
| BothExhausted : Exhaustion.

Module Type CORE.
  Parameter Buyer Seller : Type.

  (* Bid tuple: (price, quantity, timestamp) - Definition 3.1.1 *)
  Record Bid := {
    b_agent : Buyer;
    p_b : nat;
    q_b : nat;
    t_b : nat
  }.

  (* Ask tuple: (price, quantity, timestamp) - Definition 3.1.1 *)
  Record Ask := {
    s_agent : Seller;
    a_s : nat;
    q_s : nat;
    t_s : nat
  }.

  (* Feasibility - Definition 3.1.1 *)
  Definition matchable (B:Bid) (A:Ask) : Prop :=
    p_b B >= a_s A /\ q_b B > 0 /\ q_s A > 0.

  (* Trade quantity - Definition 3.1.2 *)
  Definition q_ij (B:Bid) (A:Ask) : nat :=
    Nat.min (q_b B) (q_s A).

  (* Match record *)
  Record Match := {
    mb : Bid;
    ma : Ask;
    mq : nat
  }.

  (* Auction state with residual tracking *)
  Record State := {
    Bids : list Bid;
    Asks : list Ask;
    Mt   : list Match;
    marginal_pair : option (Bid * Ask * Exhaustion);
    step_number : nat
  }.

  (* Initial state - Protocol Step P₁ *)
  Definition init_state (bs:list Bid) (as_list:list Ask) : State :=
    {| Bids := bs; Asks := as_list; Mt := []; 
       marginal_pair := None; step_number := 0 |}.

  (* Feasible match construction *)
  Definition feasible_match (m:Match) : Prop :=
    matchable (mb m) (ma m) /\ mq m = q_ij (mb m) (ma m).

  (* Monotonicity - Definition 3.1.7 *)
  Definition monotone_Mt (M N:list Match) : Prop :=
    forall m, In m M -> In m N.

  (* Quantity bounds - Definition 3.1.5 *)
  Definition per_buyer_bound (M:list Match) : Prop :=
    forall (b:Bid) (m:Match), In m M -> mb m = b -> mq m <= q_b b.

  Definition per_seller_bound (M:list Match) : Prop :=
    forall (a:Ask) (m:Match), In m M -> ma m = a -> mq m <= q_s a.
End CORE.

Module Core <: CORE.
  Definition Buyer := nat.
  Definition Seller := nat.

  Record Bid := {
    b_agent : Buyer;
    p_b : nat;
    q_b : nat;
    t_b : nat
  }.

  Record Ask := {
    s_agent : Seller;
    a_s : nat;
    q_s : nat;
    t_s : nat
  }.

  Definition matchable (B:Bid) (A:Ask) : Prop :=
    p_b B >= a_s A /\ q_b B > 0 /\ q_s A > 0.

  Definition q_ij (B:Bid) (A:Ask) : nat :=
    Nat.min (q_b B) (q_s A).

  Record Match := {
    mb : Bid;
    ma : Ask;
    mq : nat
  }.

  Record State := {
    Bids : list Bid;
    Asks : list Ask;
    Mt   : list Match;
    marginal_pair : option (Bid * Ask * Exhaustion);
    step_number : nat
  }.

  Definition init_state (bs:list Bid) (as_list:list Ask) : State :=
    {| Bids := bs; Asks := as_list; Mt := []; 
       marginal_pair := None; step_number := 0 |}.

  Definition feasible_match (m:Match) : Prop :=
    matchable (mb m) (ma m) /\ mq m = q_ij (mb m) (ma m).

  Definition monotone_Mt (M N:list Match) : Prop :=
    forall m, In m M -> In m N.

  Definition per_buyer_bound (M:list Match) : Prop :=
    forall (b:Bid) (m:Match), In m M -> mb m = b -> mq m <= q_b b.

  Definition per_seller_bound (M:list Match) : Prop :=
    forall (a:Ask) (m:Match), In m M -> ma m = a -> mq m <= q_s a.
End Core.

Export Core.