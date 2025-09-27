  From Coq Require Import List Arith Lia.
  Import ListNotations.

  Module Type CORE.
    Parameter Buyer Seller : Type.

    Record Bid := {
      b_agent : Buyer;
      p_b : nat;  (* price (discretized) *)
      q_b : nat;  (* quantity (N) *)
      t_b : nat   (* timestamp (N) *)
    }.

    Record Ask := {
      s_agent : Seller;
      a_s : nat;  (* ask price (discretized) *)
      q_s : nat;  (* quantity (N) *)
      t_s : nat   (* timestamp (N) *)
    }.

    (* Feasibility (Def. 3.1.1) *)
    Definition matchable (B:Bid) (A:Ask) : Prop :=
      p_b B >= a_s A /\ q_b B > 0 /\ q_s A > 0.

    (* Matched quantity (Def. 3.1.2) *)
    Definition q_ij (B:Bid) (A:Ask) : nat :=
      Nat.min (q_b B) (q_s A).

    Record Match := {
      mb : Bid;
      ma : Ask;
      mq : nat
    }.

    (* Auction state = order books + executed matches Mt *)
    Record State := {
      Bids : list Bid;
      Asks : list Ask;
      Mt   : list Match
    }.

    (* Exact association: the match uses precisely these orders *)
    Definition uses_bid_of (m:Match) (b:Bid) : Prop := mb m = b.
    Definition uses_ask_of (m:Match) (a:Ask) : Prop := ma m = a.

    (* Per-order logical bounds (Defs. 3.1.6–3.1.7) *)
    Definition per_buyer_bound (M:list Match) : Prop :=
      forall (b:Bid) (m:Match), In m M -> uses_bid_of m b -> mq m <= q_b b.

    Definition per_seller_bound (M:list Match) : Prop :=
      forall (a:Ask) (m:Match), In m M -> uses_ask_of m a -> mq m <= q_s a.

    (* Feasible match in Mt construction *)
    Definition feasible_match (m:Match) : Prop :=
      matchable (mb m) (ma m) /\ mq m = q_ij (mb m) (ma m).

    (* Monotonicity of the executed-match ledger *)
    Definition monotone_Mt (M N:list Match) : Prop :=
      forall m, In m M -> In m N.
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
      Mt   : list Match
    }.

    Definition uses_bid_of (m:Match) (b:Bid) : Prop := mb m = b.
    Definition uses_ask_of (m:Match) (a:Ask) : Prop := ma m = a.

    Definition per_buyer_bound (M:list Match) : Prop :=
      forall (b:Bid) (m:Match), In m M -> uses_bid_of m b -> mq m <= q_b b.

    Definition per_seller_bound (M:list Match) : Prop :=
      forall (a:Ask) (m:Match), In m M -> uses_ask_of m a -> mq m <= q_s a.

    Definition feasible_match (m:Match) : Prop :=
      matchable (mb m) (ma m) /\ mq m = q_ij (mb m) (ma m).

    Definition monotone_Mt (M N:list Match) : Prop :=
      forall m, In m M -> In m N.
  End Core.

  Export Core.