(*  MUDA/Types.v *)
From Stdlib Require Export Arith List Bool PeanoNat.
From MUDA Require Export Eqb.
Import ListNotations.
Local Open Scope bool_scope.

(** ** Agent Types and Equality Instances *)
Inductive AgentType : Type :=
  | Buyer
  | Seller.

Record Agent := {
  agent_id : nat;
  agent_type : AgentType
}.

(** ** Equality instances *)

Definition agent_eq (a1 a2 : Agent) : bool :=
  Nat.eqb (agent_id a1) (agent_id a2).

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

Definition bid_eq (b1 b2 : Bid) : bool :=
  Nat.eqb (bid_id b1) (bid_id b2).

Definition ask_eq (a1 a2 : Ask) : bool :=
  Nat.eqb (ask_id a1) (ask_id a2).

#[export] Instance bid_eqb : Eqb Bid := {
  eqb := bid_eq;
}.

#[export] Instance ask_eqb : Eqb Ask := {
  eqb := ask_eq;
}.

Lemma bid_eq_spec {eqb_instance : Eqb Bid} : forall b1 b2 : Bid,
  (b1 =? b2) = true <-> b1 = b2.
Proof.
Admitted.

Lemma ask_eq_spec {eqb_instance : Eqb Ask} : forall a1 a2 : Ask,
  (a1 =? a2) = true <-> a1 = a2.
Proof.
Admitted.

#[export] Instance bid_eqb_spec {eqb_instance : Eqb Bid} : EqbSpec Bid := {
  eqb_eq := bid_eq_spec;
}.

#[export] Instance ask_eqb_spec {eqb_instance : Eqb Ask} : EqbSpec Ask := {
  eqb_eq := ask_eq_spec;
}.

(** ** Matches *)

Record Match := {
  matched_bid : Bid;
  matched_ask : Ask;
  match_quantity : nat
}.

Definition match_eq (m1 m2 : Match) : bool :=
  (matched_bid m1 =? matched_bid m2) && (matched_ask m1 =? matched_ask m2).

#[export] Instance match_eqb : Eqb Match := {
  eqb := match_eq;
}.

Lemma match_eq_spec {eqb_instance : Eqb Match} : forall m1 m2 : Match,
  (m1 =? m2) = true <-> m1 = m2.
Proof.
Admitted.

#[export] Instance match_eqb_spec {eqb_instance : Eqb Match} : EqbSpec Match := {
  eqb_eq := match_eq_spec;
}.

(* Option and product instances *)

Definition option_eq {A} `{Eqb A} (x y : option A) : bool :=
  match x, y with
  | None, None => true
  | Some x', Some y' => x' =? y'
  | _, _ => false
  end.

Definition prod_eq {A B} `{Eqb A} `{Eqb B} (p1 p2 : A * B) : bool :=
  let (x1, y1) := p1 in
  let (x2, y2) := p2 in
  eqb x1 x2 && eqb y1 y2.

#[export] Instance option_eqb {A} `{Eqb A} : Eqb (option A) := {
  eqb := option_eq;
}.

#[export] Instance prod_eqb {A B} `{Eqb A} `{Eqb B} : Eqb (A * B) := {
  eqb := prod_eq;
}.

Lemma option_eq_spec {A} `{EqbSpec A} : forall x y : option A,
  option_eq x y = true <-> x = y.
Proof.
Admitted.

Lemma prod_eq_spec {A B} `{EqbSpec A} `{EqbSpec B} : forall x y : A * B,
  prod_eq x y = true <-> x = y.
Proof.
Admitted.

#[export] Instance option_eqb_spec {A} `{EqbSpec A} : EqbSpec (option A) := {
  eqb_eq := option_eq_spec;
}.

#[export] Instance prod_eqb_spec {A B} `{EqbSpec A} `{EqbSpec B} : EqbSpec (A * B) := {
  eqb_eq := prod_eq_spec;
}.

(* Decidable equality helpers *)

Definition agent_type_eq_dec (x y : AgentType) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition agent_eq_dec (a1 a2 : Agent) : {a1 = a2} + {a1 <> a2}.
Proof. decide equality. - apply agent_type_eq_dec. - apply Nat.eq_dec. Defined.

(** ** Export hints *)

#[export] Hint Resolve agent_type_eq_dec agent_eq_dec : core.

Lemma bid_eq_dec_spec : forall b1 b2 : Bid, {b1 = b2} + {b1 <> b2}.
Proof.
  intros [bid_id1 buyer1 price1 quantity1] [bid_id2 buyer2 price2 quantity2].
  decide equality; try apply agent_eq_dec; try apply Nat.eq_dec.
Qed.
Definition bid_eq_dec := bid_eq_dec_spec.

Lemma ask_eq_dec_spec : forall a1 a2 : Ask, {a1 = a2} + {a1 <> a2}.
Proof.
  intros [ask_id1 seller1 price1 quantity1] [ask_id2 seller2 price2 quantity2].
  decide equality; try apply agent_eq_dec; try apply Nat.eq_dec.
Qed.
Definition ask_eq_dec := ask_eq_dec_spec.

Lemma match_eq_dec_spec : forall m1 m2 : Match, {m1 = m2} + {m1 <> m2}.
Proof.
  intros [bid1 ask1 q1] [bid2 ask2 q2].
  decide equality; try apply bid_eq_dec; try apply ask_eq_dec; try apply Nat.eq_dec.
Qed.
Definition match_eq_dec := match_eq_dec_spec.

(* Mark the eq_dec functions as global *)
#[global]
Hint Resolve agent_type_eq_dec agent_eq_dec bid_eq_dec ask_eq_dec match_eq_dec : core.
