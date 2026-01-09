(** * MUDA/ClearingPrice.v*)
From Stdlib Require Import Arith List.
Import ListNotations.
From LTL  Require Import Syntax Semantics.
From MUDA Require Import Types State Matching.

Local Open Scope LTL_scope.
Local Open Scope nat_scope.

Definition wf_state (s : State) : Prop :=
  forall m, In m (matches s) ->
    ask_price (matched_ask m) <= price (matched_bid m).

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
  assert (Hin : In m (matches s)) by (apply (proj1 (in_rev m (matches s))); exact Hin_rev).
  specialize (Hwf m Hin).
  exact Hwf.
Qed.

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

Definition do_clearing_price (s : State) : State :=
  {| bids := bids s
   ; asks := asks s
   ; matches := matches s
   ; clearing_price := determine_clearing_price s
   ; phase := P5 |}.

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
  remember (residual_bid b (matches s) =? 0) as eb eqn:Heb.
  remember (residual_ask a (matches s) =? 0) as ea eqn:Hea.
  destruct eb, ea;
    simpl in Hc;
    inversion Hc; subst; clear Hc.
  - split; [exact Hab | apply le_n].
  - split; [exact Hab | apply le_n].
  - split; [apply le_n | exact Hab].
  - split; [exact Hab | apply le_n].
Qed.
