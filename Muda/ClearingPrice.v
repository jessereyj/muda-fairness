(** Chapter 3 (Methodology) — Section 3.5.3 (Phase P4: Clearing Price)

  - Definition-8 (marginal pair) and Definition-9 (uniform clearing price)
  - Proposition-6 (clearing price boundedness)

  Uses the final match record (the match list once matching terminates).
*)
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

Lemma wf_state_match_step_preservation :
  forall s s',
    wf_state s ->
    match_step s = Some s' ->
    wf_state s'.
Proof.
  intros s s' Hwf Hms.
  unfold match_step in Hms.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf; try discriminate.
  inversion Hms; subst s'; clear Hms.
  unfold wf_state in *. intros m Hin.
  set (ms := matches s) in *.
  set (m0 := create_match b a (matches s)) in *.
  change (In m (ms ++ [m0])) in Hin.
  rewrite in_app_iff in Hin.
  destruct Hin as [Hin|Hin].
  - (* inherited *) apply Hwf, Hin.
  - simpl in Hin. destruct Hin as [Hin|Hin]; [|contradiction].
    subst m. (* newly created match *)
    apply find_feasible_spec in Hf.
    unfold is_feasible in Hf.
    repeat rewrite Bool.andb_true_iff in Hf.
    destruct Hf as [[Hp _] _].
    apply Nat.leb_le in Hp. simpl. exact Hp.
Qed.

(* Chapter 3 Definition numbering notes are recorded as Coqdoc comments below. *)

(** Definition-8 (Last Marginal Pair).

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

(** Definition-9 (Uniform Clearing Price).

    If the marginal seller is exhausted, use the marginal ask price; otherwise
    use the marginal bid price.
*)
Definition determine_clearing_price (s : State) : option nat :=
  match marginal_pair s with
  | None => None
  | Some (b, a) =>
      (* Chapter 3 clearing-price rule:
         Let (b_star, a_star) be the marginal pair. If the marginal seller still has
         positive residual quantity, then p* = p(b_star); otherwise p* = a(a_star).
         (In particular, if both residuals are 0, pick the marginal ask.)
       *)
      if (residual_ask a (matches s) =? 0)
      then Some (ask_price a)
      else Some (price b)
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
  - (* seller residual = 0 -> clearing price is ask_price a *)
    split; [apply le_n | exact Hab].
  - (* seller residual > 0 -> clearing price is price b *)
    split; [exact Hab | apply le_n].
Qed.
