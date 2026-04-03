From Stdlib Require Export Arith List Bool PeanoNat.

(** Panel index (thesis ↔ code)

  Chapter 3 (Market objects)
  - AgentType, Agent: ownership bookkeeping (not explicit in thesis notation)
  - Bid, Ask: orders (price, quantity, timestamp) plus identifiers
  - Match: recorded trade triple (b, s, q)

  Chapter 4 (Executable derived quantities)
  - *_eq_dec: decidable equality used by executable list scans (e.g., allocated_bid/allocated_ask)
*)


(* AgentType: buyer/seller role used for ownership bookkeeping. *)
Inductive AgentType := Buyer | Seller.

(* Agent: ownership bookkeeping record (not explicit in the thesis notation).
   Not explicitly modeled in thesis—agents are implicit in order ownership. *)
Record Agent := { agent_id : nat; agent_type : AgentType }.

(* Bid: order record (price, quantity, timestamp) with identifiers/ownership bookkeeping.
   Thesis notation: bi = (pi, q⁰ᵢ, ti)
   Mapping:
     - price = pi (limit price)
     - quantity = q⁰ᵢ (initial quantity)
     - ts = ti (timestamp)
   Additional fields:
     - bid_id: unique identifier for decidable equality
     - buyer: agent ownership (implementation bookkeeping)
*)
Record Bid := {
  bid_id : nat;
  buyer : Agent;
  price : nat;
  quantity : nat;
  ts : nat
}.

(* Ask: order record (ask_price, ask_quantity, ask_ts) with identifiers/ownership bookkeeping.
   Thesis notation: sj = (aj, q⁰ⱼ, tj)
   Mapping:
     - ask_price = aj (ask price)
     - ask_quantity = q⁰ⱼ (initial quantity)
     - ask_ts = tj (timestamp)
   Additional fields:
     - ask_id: unique identifier for decidable equality
     - seller: agent ownership (implementation bookkeeping)
*)
Record Ask := {
  ask_id : nat;
  seller : Agent;
  ask_price : nat;
  ask_quantity : nat;
  ask_ts : nat
}.

(* Match: trade record (matched_bid, matched_ask, match_quantity) appended to `matches`.
   Thesis notation: m = (b, s, q)
   Direct correspondence: matched_bid = b, matched_ask = s, match_quantity = q.
   Note: b and s are full Bid and Ask records, not just identifiers.
*)
Record Match := {
  matched_bid : Bid;
  matched_ask : Ask;
  match_quantity : nat
}.

(* agent_type_eq_dec: decidable equality for AgentType (used by later record deciders). *)
Definition agent_type_eq_dec (x y : AgentType) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

(* Use a computational nat equality decider (instead of Stdlib's Nat.eq_dec,
   which may be opaque under vm_compute), so executions can be evaluated. *)
Definition nat_eq_dec (x y : nat) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

(* agent_eq_dec: decidable equality for Agent records (enables executable scans over orders). *)
Definition agent_eq_dec (a1 a2 : Agent) : {a1 = a2} + {a1 <> a2}.
Proof. decide equality. - apply agent_type_eq_dec. - apply nat_eq_dec. Defined.

#[export] Hint Resolve agent_type_eq_dec agent_eq_dec : core.

Lemma bid_eq_dec_spec : forall b1 b2 : Bid, {b1 = b2} + {b1 <> b2}.
Proof.
  intros [bid_id1 buyer1 price1 quantity1] [bid_id2 buyer2 price2 quantity2].
  decide equality; try apply agent_eq_dec; try apply nat_eq_dec.
Defined.

(* bid_eq_dec: exported bid equality decider (wrapper around bid_eq_dec_spec). *)
Definition bid_eq_dec := bid_eq_dec_spec.

Lemma ask_eq_dec_spec : forall a1 a2 : Ask, {a1 = a2} + {a1 <> a2}.
Proof.
  intros [ask_id1 seller1 price1 quantity1] [ask_id2 seller2 price2 quantity2].
  decide equality; try apply agent_eq_dec; try apply nat_eq_dec.
Defined.

(* ask_eq_dec: exported ask equality decider (wrapper around ask_eq_dec_spec). *)
Definition ask_eq_dec := ask_eq_dec_spec.

#[global]
Hint Resolve agent_type_eq_dec agent_eq_dec bid_eq_dec ask_eq_dec : core.
