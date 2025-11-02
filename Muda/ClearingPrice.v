(** * MUDA/ClearingPrice.v (Phase P4)
    Uniform price determination. *)

From Stdlib Require Import Arith List.
Import ListNotations.

From MUDA Require Import Types State Matching.

Local Open Scope nat_scope.

(* ------------------------------------------------------------------------- *)
(* Well-formedness: every stored match respects the feasibility price guard. *)
(* Section 3 creates matches only via feasibility, so this holds from P3 on. *)
(* ------------------------------------------------------------------------- *)

Definition wf_state (s : State) : Prop :=
  forall m, In m (matches s) ->
    ask_price (matched_ask m) <= price (matched_bid m).

Lemma wf_state_empty :
  forall bs asx,
    wf_state {| bids := bs; asks := asx; matches := [];
                clearing_price := None; phase := P3 |}.
Proof.
  intros bs asx m Hin. inversion Hin.
Qed.

Lemma wf_state_preserved_by_match_step :
  forall s s',
    wf_state s ->
    match_step s = Some s' ->
    wf_state s'.
Proof.
  intros s s' Hwf Hstep.
  unfold wf_state.                     (* goal: forall m, In m (matches s') -> ... *)
  intros m Hin.                        (* now Hin exists *)
  unfold match_step in Hstep.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf;
    try discriminate.
  inversion Hstep; subst s'; clear Hstep.
  simpl in Hin.
  destruct Hin as [Hin | Hin].
  - (* head: the newly created match *)
    subst m.
    (* find_feasible -> is_feasible -> price guard *)
    apply find_feasible_spec in Hf.      (* is_feasible b a (matches s) = true *)
    unfold is_feasible in Hf.
    repeat rewrite Bool.andb_true_iff in Hf.
    destruct Hf as [[Hp _] _].
    apply Nat.leb_le in Hp.
    simpl.                               (* matched_ask/create_match = a, matched_bid = b *)
    exact Hp.
  - (* tail: inherited from s *)
    exact (Hwf m Hin).
Qed.

(* ------------------------------------------------------------------------- *)
(* Marginal pair: newest match is at head (added by match_step).             *)
(* ------------------------------------------------------------------------- *)

Definition marginal_pair (s : State) : option (Bid * Ask) :=
  match matches s with
  | [] => None
  | m :: _ => Some (matched_bid m, matched_ask m)
  end.

Lemma marginal_pair_price_bound :
  forall s b a,
    wf_state s ->
    marginal_pair s = Some (b,a) ->
    ask_price a <= price b.
Proof.
  intros s b a Hwf Hm.
  unfold marginal_pair in Hm.
  remember (matches s) as ms eqn:Hms.
  destruct ms as [|m ms']; try discriminate.
  inversion Hm; subst b a; clear Hm.
  (* Build In m (matches s) using Hms, then apply the invariant *)
  assert (Hin : In m (matches s)) by (rewrite Hms; simpl; left; reflexivity).
  specialize (Hwf m Hin).
  exact Hwf.
Qed.


(* ------------------------------------------------------------------------- *)
(* Uniform Price Rule (Section 3/4).                                         *)
(* If both sides are fully satisfied at the marginal pair: price(b).         *)
(* If only bid side is exhausted: price(b).                                  *)
(* If only ask  side is exhausted: ask_price(a).                              *)
(* The "else" branch shouldn't occur for a true marginal, but stays bounded. *)
(* ------------------------------------------------------------------------- *)

Definition determine_clearing_price (s : State) : option nat :=
  match marginal_pair s with
  | None => None
  | Some (b, a) =>
      let eb := (residual_bid b (matches s) =? 0) in
      let ea := (residual_ask a (matches s) =? 0) in
      if eb && ea then Some (price b)
      else if eb then Some (price b)
      else if ea then Some (ask_price a)
      else Some (price b) (* fallback: stays within bounds by wf_state *)
  end.

(* Phase P4 transition *)
Definition do_clearing_price (s : State) : State :=
  {| bids := bids s
   ; asks := asks s
   ; matches := matches s
   ; clearing_price := determine_clearing_price s
   ; phase := P5 |}.

(* ------------------------------------------------------------------------- *)
(* Bounds: chosen clearing price lies between ask and bid of marginal pair.  *)
(* ------------------------------------------------------------------------- *)

Lemma clearing_price_bounds :
  forall s b a c,
    wf_state s ->
    marginal_pair s = Some (b, a) ->
    determine_clearing_price s = Some c ->
    ask_price a <= c /\ c <= price b.
Proof.
  intros s b a c Hwf Hm Hc.
  pose proof (marginal_pair_price_bound s b a Hwf Hm) as Hab.
  unfold determine_clearing_price in Hc; rewrite Hm in Hc.
  set (eb := residual_bid b (matches s) =? 0).
  set (ea := residual_ask a (matches s) =? 0).
  destruct eb, ea; inversion Hc; subst; clear Hc; split; auto.
Qed.