(*  MUDA/Types.v
    See NOTATION.md for detailed thesis-to-code mapping.
*)
From Stdlib Require Export Arith List Bool PeanoNat.
From MUDA Require Export Eqb.
Import ListNotations.
Local Open Scope bool_scope.

(* Agent type: implementation detail not shown in thesis notation *)
Inductive AgentType := Buyer | Seller.

Definition agent_type_eqb (x y : AgentType) : bool :=
  match x, y with Buyer, Buyer | Seller, Seller => true | _, _ => false end.

Lemma agent_type_eqb_spec :
  forall x y, agent_type_eqb x y = true <-> x = y.
Proof.
  destruct x, y; simpl; split; intro H; try discriminate; try reflexivity; now inversion H.
Qed.

(* Agent record: enables ownership tracking and bid/ask partitioning.
   Not explicitly modeled in thesis—agents are implicit in order ownership. *)
Record Agent := { agent_id : nat; agent_type : AgentType }.

Definition agent_eq (a1 a2 : Agent) : bool :=
  Nat.eqb (agent_id a1) (agent_id a2)
  && agent_type_eqb (agent_type a1) (agent_type a2).


Lemma agent_eq_spec :
  forall a1 a2, agent_eq a1 a2 = true <-> a1 = a2.
Proof.
  intros [id1 t1] [id2 t2]; simpl.
  split.
  - intros H.
    apply Bool.andb_true_iff in H as [Hid Ht].
    apply Nat.eqb_eq in Hid.                (* id1 = id2 *)
    apply agent_type_eqb_spec in Ht.        (* t1 = t2   *)
    cbn in Hid, Ht. subst. reflexivity.
  - intros Heq; inversion Heq; subst; simpl.
    apply Bool.andb_true_iff; split.
    + apply Nat.eqb_refl.
  + apply (proj2 (agent_type_eqb_spec t2 t2)). reflexivity.
Qed.

(* Bid record.
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

(* Ask record.
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

(* Match record.
   Thesis notation: m = (b, s, q)
   Direct correspondence: matched_bid = b, matched_ask = s, match_quantity = q.
   Note: b and s are full Bid and Ask records, not just identifiers.
*)
Record Match := {
  matched_bid : Bid;
  matched_ask : Ask;
  match_quantity : nat
}.

Definition bid_eq (b1 b2 : Bid) : bool :=
  Nat.eqb (bid_id b1) (bid_id b2) &&
  Nat.eqb (price b1) (price b2) &&
  Nat.eqb (quantity b1) (quantity b2) &&
  Nat.eqb (ts b1) (ts b2) &&
  agent_eq (buyer b1) (buyer b2).

Definition ask_eq (a1 a2 : Ask) : bool :=
  Nat.eqb (ask_id a1) (ask_id a2) &&
  Nat.eqb (ask_price a1) (ask_price a2) &&
  Nat.eqb (ask_quantity a1) (ask_quantity a2) &&
  Nat.eqb (ask_ts a1) (ask_ts a2) &&
  agent_eq (seller a1) (seller a2).

Definition match_eq (m1 m2 : Match) : bool :=
  bid_eq (matched_bid m1) (matched_bid m2) &&
  ask_eq (matched_ask m1) (matched_ask m2) &&
  Nat.eqb (match_quantity m1) (match_quantity m2).

#[export] Instance bid_eqb : Eqb Bid := { eqb := bid_eq }.
#[export] Instance ask_eqb : Eqb Ask := { eqb := ask_eq }.
#[export] Instance match_eqb : Eqb Match := { eqb := match_eq }.


Lemma build_bid_eq :
  forall id1 ag1 p1 q1 ts1 id2 ag2 p2 q2 ts2,
    id1 = id2 -> ag1 = ag2 -> p1 = p2 -> q1 = q2 -> ts1 = ts2 ->
    {| bid_id := id1; buyer := ag1; price := p1; quantity := q1; ts := ts1; |} =
    {| bid_id := id2; buyer := ag2; price := p2; quantity := q2; ts := ts2; |}.
Proof. intros; subst; reflexivity. Qed.

Lemma bid_eq_spec : forall b1 b2,
  bid_eq b1 b2 = true <-> b1 = b2.
Proof.
  intros [id1 ag1 p1 q1 ts1] [id2 ag2 p2 q2 ts2]; simpl.
  split.
  - (* -> *)
    intros H.
    (* ((((id && price) && qty) && ts) && agent) = true *)
    apply Bool.andb_true_iff in H as [H1234 Hag].
    apply Bool.andb_true_iff in H1234 as [H123 Ht].
    apply Bool.andb_true_iff in H123 as [H12 Hq].
    apply Bool.andb_true_iff in H12  as [Hid Hp].
    apply Nat.eqb_eq in Hid.
    apply Nat.eqb_eq in Hp.
    apply Nat.eqb_eq in Hq.
    apply Nat.eqb_eq in Ht.
    apply agent_eq_spec in Hag.
    (* id1=id2, ag1=ag2, p1=p2, q1=q2, ts1=ts2 *)
    now apply build_bid_eq.
  - (* <- *)
    intros Heq; inversion Heq; subst; simpl.
    (* build ((((id && price) && qty) && ts) && agent) = true *)
    apply Bool.andb_true_iff; split.
    + apply Bool.andb_true_iff; split.
      * apply Bool.andb_true_iff; split.
        -- apply Bool.andb_true_iff; split.
           ** apply Nat.eqb_refl.   (* id *)
           ** apply Nat.eqb_refl.   (* price *)
        -- apply Nat.eqb_refl.      (* qty *)
      * apply Nat.eqb_refl.        (* ts *)
    + apply agent_eq_spec; reflexivity.
Qed.


Lemma build_ask_eq :
  forall id1 s1 p1 q1 ts1 id2 s2 p2 q2 ts2,
    id1 = id2 -> s1 = s2 -> p1 = p2 -> q1 = q2 -> ts1 = ts2 ->
    {| ask_id := id1; seller := s1; ask_price := p1; ask_quantity := q1; ask_ts := ts1 |} =
    {| ask_id := id2; seller := s2; ask_price := p2; ask_quantity := q2; ask_ts := ts2 |}.
Proof. intros; subst; reflexivity. Qed.

Lemma ask_eq_spec : forall a1 a2,
  ask_eq a1 a2 = true <-> a1 = a2.
Proof.
  intros [id1 s1 p1 q1 ts1] [id2 s2 p2 q2 ts2]; simpl.
  split.
  - (* -> *)
    intros H.
    (* ((((id && price) && qty) && ts) && agent) = true *)
    apply Bool.andb_true_iff in H as [H1234 Hs].
    apply Bool.andb_true_iff in H1234 as [H123 Ht].
    apply Bool.andb_true_iff in H123  as [H12 Hq].
    apply Bool.andb_true_iff in H12   as [Hid Hp].
    apply Nat.eqb_eq in Hid.
    apply Nat.eqb_eq in Hp.
    apply Nat.eqb_eq in Hq.
    apply Nat.eqb_eq in Ht.
    apply agent_eq_spec in Hs.
    now apply build_ask_eq.
  - (* <- *)
    intros Heq; inversion Heq; subst; simpl.
    (* build ((((id && price) && qty) && ts) && agent) = true *)
    apply Bool.andb_true_iff; split.
    + apply Bool.andb_true_iff; split.
      * apply Bool.andb_true_iff; split.
        -- apply Bool.andb_true_iff; split.
           ** apply Nat.eqb_refl.   (* id  *)
           ** apply Nat.eqb_refl.   (* price *)
        -- apply Nat.eqb_refl.      (* qty *)
      * apply Nat.eqb_refl.         (* ts *)
    + apply agent_eq_spec; reflexivity.
Qed.

Lemma build_match_eq :
  forall b1 a1 q1 b2 a2 q2,
    b1 = b2 -> a1 = a2 -> q1 = q2 ->
    {| matched_bid := b1; matched_ask := a1; match_quantity := q1 |} =
    {| matched_bid := b2; matched_ask := a2; match_quantity := q2 |}.
Proof. intros; subst; reflexivity. Qed.

Lemma match_eq_spec : forall m1 m2,
  match_eq m1 m2 = true <-> m1 = m2.
Proof.
  intros [b1 a1 q1] [b2 a2 q2]; simpl.
  split.
  - intros H.
    apply Bool.andb_true_iff in H as [H12 Hq].
    apply Bool.andb_true_iff in H12 as [Hb Ha].
    apply bid_eq_spec in Hb.
    apply ask_eq_spec in Ha.
    apply Nat.eqb_eq in Hq.
    now apply build_match_eq.
  - intros Heq; inversion Heq; subst; simpl.
    apply Bool.andb_true_iff; split.
    + apply Bool.andb_true_iff; split; [apply bid_eq_spec | apply ask_eq_spec]; reflexivity.
    + apply Nat.eqb_refl.
Qed.

#[export] Instance bid_eqb_spec : EqbSpec Bid := { eqb_eq := bid_eq_spec }.
#[export] Instance ask_eqb_spec : EqbSpec Ask := { eqb_eq := ask_eq_spec }.
#[export] Instance match_eqb_spec : EqbSpec Match := { eqb_eq := match_eq_spec }.

Definition agent_type_eq_dec (x y : AgentType) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

(* Use a computational nat equality decider (instead of Stdlib's Nat.eq_dec,
   which may be opaque under vm_compute), so executions can be evaluated. *)
Definition nat_eq_dec (x y : nat) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition agent_eq_dec (a1 a2 : Agent) : {a1 = a2} + {a1 <> a2}.
Proof. decide equality. - apply agent_type_eq_dec. - apply nat_eq_dec. Defined.

#[export] Hint Resolve agent_type_eq_dec agent_eq_dec : core.

Lemma bid_eq_dec_spec : forall b1 b2 : Bid, {b1 = b2} + {b1 <> b2}.
Proof.
  intros [bid_id1 buyer1 price1 quantity1] [bid_id2 buyer2 price2 quantity2].
  decide equality; try apply agent_eq_dec; try apply nat_eq_dec.
Defined.
Definition bid_eq_dec := bid_eq_dec_spec.

Lemma ask_eq_dec_spec : forall a1 a2 : Ask, {a1 = a2} + {a1 <> a2}.
Proof.
  intros [ask_id1 seller1 price1 quantity1] [ask_id2 seller2 price2 quantity2].
  decide equality; try apply agent_eq_dec; try apply nat_eq_dec.
Defined.
Definition ask_eq_dec := ask_eq_dec_spec.

Lemma match_eq_dec_spec : forall m1 m2 : Match, {m1 = m2} + {m1 <> m2}.
Proof.
  intros [bid1 ask1 q1] [bid2 ask2 q2].
  decide equality; try apply bid_eq_dec; try apply ask_eq_dec; try apply nat_eq_dec.
Defined.
Definition match_eq_dec := match_eq_dec_spec.

#[global]
Hint Resolve agent_type_eq_dec agent_eq_dec bid_eq_dec ask_eq_dec match_eq_dec : core.
