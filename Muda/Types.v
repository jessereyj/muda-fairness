(** * MUDA Types
    
    Basic types for bids, asks, agents, and matches.
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** ** Agent Types *)

Inductive AgentType : Type :=
  | Buyer
  | Seller.

Record Agent := {
  agent_id : nat;
  agent_type : AgentType
}.

(** ** Orders *)

Record Bid := {
  bid_id : nat;
  buyer : Agent;
  price : nat;
  quantity : nat
}.

Record Ask := {
  ask_id : nat;
  seller : Agent;
  ask_price : nat;
  ask_quantity : nat
}.

(** ** Matches *)

Record Match := {
  matched_bid : Bid;
  matched_ask : Ask;
  match_quantity : nat
}.

(** ** Decidable Equality *)

Lemma agent_type_eq_dec : forall (t1 t2 : AgentType), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

Lemma agent_eq_dec : forall (a1 a2 : Agent), {a1 = a2} + {a1 <> a2}.
Proof.
  intros. decide equality.
  - apply agent_type_eq_dec.
  - apply Nat.eq_dec.
Defined.

Lemma bid_eq_dec : forall (b1 b2 : Bid), {b1 = b2} + {b1 <> b2}.
Proof.
  intros. decide equality; try apply Nat.eq_dec; apply agent_eq_dec.
Defined.

Lemma ask_eq_dec : forall (a1 a2 : Ask), {a1 = a2} + {a1 <> a2}.
Proof.
  intros. decide equality; try apply Nat.eq_dec; apply agent_eq_dec.
Defined.

(** ** Helper Functions *)

Definition get_bid_price (b : Bid) : nat := price b.
Definition get_ask_price (a : Ask) : nat := ask_price a.
Definition get_bid_qty (b : Bid) : nat := quantity b.
Definition get_ask_qty (a : Ask) : nat := ask_quantity a.

(** ** Feasibility *)

Definition feasible (b : Bid) (a : Ask) : Prop :=
  get_bid_price b >= get_ask_price a.