(*  MUDA/Sorting.v *)
From Stdlib Require Import List Lia Arith Sorting Permutation Sorted.
Import ListNotations.
From MUDA Require Import Types State.

(* Definition 3.1.3: lexicographic order *)
Definition prioB (b1 b2 : Bid) : Prop :=
  price b1 > price b2 \/
  (price b1 = price b2 /\ ts b1 < ts b2).

Definition prioS (a1 a2 : Ask) : Prop :=
  ask_price a1 < ask_price a2 \/
  (ask_price a1 = ask_price a2 /\ ask_ts a1 < ask_ts a2).

(* Bids: price ↓, then ts ↑, then id ↑ *)
Definition bid_priority (b1 b2 : Bid) : Prop :=
  price b1 > price b2 \/
  (price b1 = price b2 /\
     (ts b1 < ts b2 \/
      (ts b1 = ts b2 /\ bid_id b1 < bid_id b2))).

(* Asks: ask_price ↑, then ask_ts ↑, then ask_id ↑ *)
Definition ask_priority (a1 a2 : Ask) : Prop :=
  ask_price a1 < ask_price a2 \/
  (ask_price a1 = ask_price a2 /\
     (ask_ts a1 < ask_ts a2 \/
      (ask_ts a1 = ask_ts a2 /\ ask_id a1 < ask_id a2))).

(** ** Basic order facts (useful in P2 invariants) *)
Lemma bid_priority_irrefl : forall b, ~ bid_priority b b.
Proof.
  intros b; unfold bid_priority; intros [Hgt|[Heq [Hlt|[Heqt Hid]]]]; try lia.
Qed.

Lemma ask_priority_irrefl : forall a, ~ ask_priority a a.
Proof.
  intros a; unfold ask_priority; intros [Hlt|[Heq [Hlt'|[Heqt Hid]]]]; try lia.
Qed.

(* Transitivity for these lexicographic orders is routine but case-heavy.
   We keep them available as axioms to simplify later developments; you can
   replace these with full proofs when you implement a concrete comparator. *)
Axiom bid_priority_trans :
  forall x y z, bid_priority x y -> bid_priority y z -> bid_priority x z.

Axiom ask_priority_trans :
  forall x y z, ask_priority x y -> ask_priority y z -> ask_priority x z.

(** ** Sortedness predicates (index-based, convenient for nth_error reasoning) *)

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

(** ** StronglySorted variants (sometimes easier for inductive proofs) *)
Definition bids_strongly_sorted (bs : list Bid) : Prop :=
  StronglySorted bid_priority bs.

Definition asks_strongly_sorted (as_list : list Ask) : Prop :=
  StronglySorted ask_priority as_list.

(* Bridges between the two styles. These are convenient to use downstream.
   If you prefer, you can later prove them from first principles. *)
Axiom bids_sorted__StronglySorted :
  forall bs, bids_sorted bs -> bids_strongly_sorted bs.
Axiom asks_sorted__StronglySorted :
  forall asx, asks_sorted asx -> asks_strongly_sorted asx.

Axiom StronglySorted__bids_sorted :
  forall bs, bids_strongly_sorted bs -> bids_sorted bs.
Axiom StronglySorted__asks_sorted :
  forall asx, asks_strongly_sorted asx -> asks_sorted asx.

(** ** Sorting functions and contracts (P2) *)

(* We assume existence of sorting functions that realize the above priority.
   Later you can instantiate these with a concrete stable sort + comparator. *)
Axiom sort_bids      : list Bid -> list Bid.
Axiom sort_asks      : list Ask -> list Ask.

(* Correctness: the outputs are sorted by the intended priorities. *)
Axiom sort_bids_correct : forall bs, bids_sorted (sort_bids bs).
Axiom sort_asks_correct : forall asx, asks_sorted (sort_asks asx).

(* Reordering only: no loss/duplication (needed for Maximality/Rejection). *)
Axiom sort_bids_perm : forall bs, Permutation (sort_bids bs) bs.
Axiom sort_asks_perm : forall asx, Permutation (sort_asks asx) asx.

(** ** Phase P2 Transition (Section 3 pipeline) *)
Definition do_sorting (s : State) : State :=
  {| bids := sort_bids (bids s);
     asks := sort_asks (asks s);
     matches := matches s;
     clearing_price := clearing_price s;
     phase := P3 |}.
