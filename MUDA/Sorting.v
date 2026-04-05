From Stdlib Require Import List Arith Bool Lia.
From Stdlib.Sorting Require Import Sorted Permutation.
Import ListNotations.
From MUDA Require Import Types State.

(** Panel index (thesis ↔ code)

  Chapter 3 (Priority order and sorting)
  - prioB/prioS: thesis priority relations (Definition 7)
  - bid_priority/ask_priority: deterministic refinement (adds identifiers as tie-breakers)
  - bid_priorityb/ask_priorityb, sort_bids/sort_asks: executable sorting
  - do_sorting: Phase P2 action (sort inputs, advance to P3)
*)

Local Open Scope bool_scope.

(* Thesis priority (Definition 7) *)
(* prioB: buyer priority (higher price, then earlier time). *)
Definition prioB (b1 b2 : Bid) : Prop :=
  price b1 > price b2 \/
  (price b1 = price b2 /\ ts b1 < ts b2).

(* prioS: seller priority (lower ask price, then earlier time). *)
Definition prioS (a1 a2 : Ask) : Prop :=
  ask_price a1 < ask_price a2 \/
  (ask_price a1 = ask_price a2 /\ ask_ts a1 < ask_ts a2).

(* Deterministic refinement (adds IDs as a final tie-breaker). *)
(* bid_priority: deterministic buyer priority used by executable sorting. *)
Definition bid_priority (b1 b2 : Bid) : Prop :=
  price b1 > price b2 \/
  (price b1 = price b2 /\
     (ts b1 < ts b2 \/ (ts b1 = ts b2 /\ bid_id b1 < bid_id b2))).

(* ask_priority: deterministic seller priority used by executable sorting. *)
Definition ask_priority (a1 a2 : Ask) : Prop :=
  ask_price a1 < ask_price a2 \/
  (ask_price a1 = ask_price a2 /\
     (ask_ts a1 < ask_ts a2 \/ (ask_ts a1 = ask_ts a2 /\ ask_id a1 < ask_id a2))).

(* Boolean comparators for executable sorting. *)
(* bid_priorityb: boolean comparator implementing bid_priority. *)
Definition bid_priorityb (b1 b2 : Bid) : bool :=
  Nat.ltb (price b2) (price b1)
  || (Nat.eqb (price b1) (price b2)
      && (Nat.ltb (ts b1) (ts b2)
          || (Nat.eqb (ts b1) (ts b2) && Nat.ltb (bid_id b1) (bid_id b2)))).

(* ask_priorityb: boolean comparator implementing ask_priority. *)
Definition ask_priorityb (a1 a2 : Ask) : bool :=
  Nat.ltb (ask_price a1) (ask_price a2)
  || (Nat.eqb (ask_price a1) (ask_price a2)
      && (Nat.ltb (ask_ts a1) (ask_ts a2)
          || (Nat.eqb (ask_ts a1) (ask_ts a2) && Nat.ltb (ask_id a1) (ask_id a2)))).

(* insert_bid: insertion step for insertion-sort on bids. *)
Fixpoint insert_bid (b : Bid) (bs : list Bid) : list Bid :=
  match bs with
  | [] => [b]
  | x :: xs => if bid_priorityb b x then b :: x :: xs else x :: insert_bid b xs
  end.

(* insert_ask: insertion step for insertion-sort on asks. *)
Fixpoint insert_ask (a : Ask) (asx : list Ask) : list Ask :=
  match asx with
  | [] => [a]
  | x :: xs => if ask_priorityb a x then a :: x :: xs else x :: insert_ask a xs
  end.

(* sort_bids: executable sorting of bids by bid_priorityb (Phase P2). *)
Fixpoint sort_bids (bs : list Bid) : list Bid :=
  match bs with
  | [] => []
  | b :: bs' => insert_bid b (sort_bids bs')
  end.

(* sort_asks: executable sorting of asks by ask_priorityb (Phase P2). *)
Fixpoint sort_asks (asx : list Ask) : list Ask :=
  match asx with
  | [] => []
  | a :: as' => insert_ask a (sort_asks as')
  end.

(* do_sorting: Phase P2 transition (sort bids/asks and move to P3). *)
Definition do_sorting (s : State) : State :=
  {| bids := sort_bids (bids s);
     asks := sort_asks (asks s);
     matches := matches s;
     clearing_price := clearing_price s;
     phase := P3 |}.


(** * Proof support: comparator correctness and thesis correspondence *)

(** ** Boolean comparator soundness (strict) *)

Lemma bid_priorityb_true_priority :
  forall b1 b2,
    bid_priorityb b1 b2 = true -> bid_priority b1 b2.
Proof.
  intros b1 b2 H.
  unfold bid_priorityb in H.
  apply Bool.orb_true_iff in H as [Hprice|Hrest].
  - left. apply Nat.ltb_lt in Hprice. lia.
  - apply Bool.andb_true_iff in Hrest as [Heq Ht].
    apply Nat.eqb_eq in Heq.
    right.
    split; [exact Heq|].
    apply Bool.orb_true_iff in Ht as [Hts|Hid].
    + left. apply Nat.ltb_lt in Hts. exact Hts.
    + apply Bool.andb_true_iff in Hid as [Heqts Hltid].
      apply Nat.eqb_eq in Heqts.
      apply Nat.ltb_lt in Hltid.
      right. split; [exact Heqts|exact Hltid].
Qed.

Lemma ask_priorityb_true_priority :
  forall a1 a2,
    ask_priorityb a1 a2 = true -> ask_priority a1 a2.
Proof.
  intros a1 a2 H.
  unfold ask_priorityb in H.
  apply Bool.orb_true_iff in H as [Hprice|Hrest].
  - left. apply Nat.ltb_lt in Hprice. exact Hprice.
  - apply Bool.andb_true_iff in Hrest as [Heq Ht].
    apply Nat.eqb_eq in Heq.
    right.
    split; [exact Heq|].
    apply Bool.orb_true_iff in Ht as [Hts|Hid].
    + left. apply Nat.ltb_lt in Hts. exact Hts.
    + apply Bool.andb_true_iff in Hid as [Heqts Hltid].
      apply Nat.eqb_eq in Heqts.
      apply Nat.ltb_lt in Hltid.
      right. split; [exact Heqts|exact Hltid].
Qed.


(** ** Explicit correspondence to the thesis priority relations (Definition 7)

    The deterministic refinement agrees with the thesis order, and only adds an
    extra deterministic tie-break when price and time are equal.
*)

Lemma prioB_implies_bid_priority :
  forall b1 b2,
    prioB b1 b2 -> bid_priority b1 b2.
Proof.
  intros b1 b2 H.
  unfold prioB in H.
  unfold bid_priority.
  destruct H as [Hgt|[Heq Hlt]].
  - left; exact Hgt.
  - right. split; [exact Heq|]. left; exact Hlt.
Qed.

Lemma prioS_implies_ask_priority :
  forall a1 a2,
    prioS a1 a2 -> ask_priority a1 a2.
Proof.
  intros a1 a2 H.
  unfold prioS in H.
  unfold ask_priority.
  destruct H as [Hlt|[Heq Hlt_ts]].
  - left; exact Hlt.
  - right. split; [exact Heq|]. left; exact Hlt_ts.
Qed.

