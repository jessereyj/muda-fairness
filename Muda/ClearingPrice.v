(** * MUDA/ClearingPrice.v (Phase P4)
    Uniform price determination.*)

From Stdlib Require Import Arith List Lia.
Import ListNotations.

From MUDA Require Import Types State Matching.

Local Open Scope nat_scope.


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

(* Bounds *)
Lemma clearing_price_bounds : forall s b a c,
  marginal_pair s = Some (b, a) ->
  determine_clearing_price s = Some c ->
  ask_price a <= c <= price b.
Proof.
  intros s b a c Hm Hc.
  unfold determine_clearing_price in Hc; rewrite Hm in Hc.
  remember (residual_bid b (matches s) =? 0) as eb.
  remember (residual_ask a (matches s) =? 0) as ea.
  destruct eb, ea; inversion Hc; subst; clear Hc.
  all: unfold marginal_pair in Hm;
      destruct (matches s) as [|m ms']; try discriminate;
      inversion Hm; subst; clear Hm.
  all: split; auto;
      apply (feasible_price_bounds m).
Qed.
