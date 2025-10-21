(** * MUDA Clearing Price (Phase P4)
    Uniform price determination.
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import MUDA.MUDA.Types.
Require Import MUDA.MUDA.State.
Require Import MUDA.MUDA.Matching.
Import ListNotations.

(* --- NEW: define marginal_pair here (latest match is at head) --- *)
Definition marginal_pair (s : State) : option (Bid * Ask) :=
  match matches s with
  | [] => None
  | m :: _ => Some (matched_bid m, matched_ask m)
  end.

(* Uniform Price Rule *)
Definition determine_clearing_price (s : State) : option nat :=
  match marginal_pair s with
  | None => None
  | Some (b, a) =>
      let eb := (residual_bid b (matches s) =? 0) in
      let ea := (residual_ask a (matches s) =? 0) in
      if eb && ea then Some (price b)
      else if eb then Some (price b)
      else if ea then Some (ask_price a)
      else Some (price b) (* conservative; should not happen if pair is marginal *)
  end.

(* Phase P4 transition *)
Definition do_clearing_price (s : State) : State :=
  {| bids := bids s
   ; asks := asks s
   ; matches := matches s
   ; clearing_price := determine_clearing_price s
   ; phase := P5 |}.

(* Bounds: a(s*) ≤ c ≤ p(b*) *)
Lemma clearing_price_bounds : forall s b a c,
  marginal_pair s = Some (b, a) ->
  determine_clearing_price s = Some c ->
  ask_price a <= c <= price b.
Proof.
  intros s b a c Hm Hc.
  unfold determine_clearing_price in Hc; rewrite Hm in Hc.
  remember (residual_bid b (matches s) =? 0) as eb.
  remember (residual_ask a (matches s) =? 0) as ea.
  (* All branches set c to either price b or ask_price a. *)
  destruct eb, ea; inversion Hc; subst; simpl; lia.
Qed.
