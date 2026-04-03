From Stdlib Require Import Arith List.
Import ListNotations.
From LTL  Require Import Syntax Semantics.
From MUDA Require Import Types State Matching.

Local Open Scope LTL_scope.
Local Open Scope nat_scope.

Definition wf_state (s : State) : Prop :=
  forall m, In m (matches s) ->
    ask_price (matched_ask m) <= price (matched_bid m).

Lemma in_rev_l {A} (l : list A) (x : A) : In x (rev l) -> In x l.
Proof.
  induction l as [|h t IH]; simpl; intro H.
  - contradiction.
  - rewrite in_app_iff in H.
    destruct H as [Hin | Hin].
    + right. apply IH. exact Hin.
    + simpl in Hin. destruct Hin as [Heq | Hnil].
      * subst. left. reflexivity.
      * contradiction.
Qed.

Lemma wf_state_initial : forall bs as_list,
  wf_state (initial_state bs as_list).
Proof.
  intros bs as_list m Hin. inversion Hin.
Qed.

(* Chapter 3 Definition numbering notes are recorded as Coqdoc comments below. *)

(** Definition-10 (Clearing Price): Last marginal pair.

    The marginal pair is the last trade in the final match record.
*)
Definition marginal_pair (s : State) : option (Bid * Ask) :=
  match rev (matches s) with
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
  remember (rev (matches s)) as ms eqn:Hms.
  destruct ms as [|m ms']; try discriminate.
  inversion Hm; subst b a; clear Hm.
  (* Build In m (matches s) using Hms, then apply the invariant *)
  assert (Hin_rev : In m (rev (matches s))) by (rewrite <- Hms; simpl; left; reflexivity).
  pose proof (in_rev_l (matches s) m Hin_rev) as Hin.
  specialize (Hwf m Hin).
  exact Hwf.
Qed.

(** Definition-10 (Clearing Price): Uniform clearing price.

  Chapter 5 scenarios use the convention:
  - if the marginal seller is exhausted, use the marginal bid price
  - otherwise, use the marginal ask price.
*)
Definition determine_clearing_price (s : State) : option nat :=
  match marginal_pair s with
  | None => None
  | Some (b, a) =>
        (* Clearing price convention used by this development:
           Let (b_star, a_star) be the marginal pair from the final match record.
           We deterministically select either the marginal bid price or the
           marginal ask price based on whether the marginal seller is exhausted.
         *)
        if (residual_ask a (matches s) =? 0)
        then Some (price b)
        else Some (ask_price a)
  end.

Definition do_clearing_price (s : State) : State :=
  {| bids := bids s
   ; asks := asks s
   ; matches := matches s
   ; clearing_price := determine_clearing_price s
   ; phase := P5 |}.

(** Proposition-6 (Clearing Price Boundedness).

    The computed clearing price is within the marginal ask/bid bounds.
*)
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
  remember (residual_ask a (matches s) =? 0) as ea eqn:Hea.
  destruct ea;
    simpl in Hc;
    inversion Hc; subst; clear Hc.
  - (* seller residual = 0 -> clearing price is price b *)
    split; [exact Hab | apply le_n].
  - (* seller residual > 0 -> clearing price is ask_price a *)
    split; [apply le_n | exact Hab].
Qed.
