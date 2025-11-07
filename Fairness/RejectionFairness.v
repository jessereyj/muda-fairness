(* Fairness/RejectionFairness.v *)
From Stdlib Require Import List.
Import ListNotations.
From LTL  Require Import LTL.           (* re-export module *)
From MUDA Require Import MUDA. 

(* ---------- Rejection predicates ---------- *)
Definition rejected_bid (b : Bid) (s : State) : Prop :=
  In b (bids s) /\ residual_bid b (matches s) > 0.

Definition rejected_ask (a : Ask) (s : State) : Prop :=
  In a (asks s) /\ residual_ask a (matches s) > 0.

(* Justification: for any remaining counterparty, either that side is exhausted
   or the pair is infeasible w.r.t. current matches. *)
Definition justified_rejection (s : State) : Prop :=
  (forall (b : Bid) (aa : Ask),
      rejected_bid b s -> In aa (asks s) ->
      residual_ask aa (matches s) = 0 \/ is_feasible b aa (matches s) = false)
  /\
  (forall (aa : Ask) (b : Bid),
      rejected_ask aa s -> In b (bids s) ->
      residual_bid b (matches s) = 0 \/ is_feasible b aa (matches s) = false).

(* ---------- Core list-scanning facts ---------- *)
(* If pick_ask returns None, then b is infeasible with every ask in the list. *)
Lemma pick_ask_None_all_false :
  forall (b : Bid) (as_list : list Ask) (ms : list Match),
    pick_ask b as_list ms = None ->
    forall (aa : Ask), In aa as_list -> is_feasible b aa ms = false.
Proof.
  intros b as_list ms Hnone.
  induction as_list as [|a_hd as_tl IH]; intros aa Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hin_eq | Hin_tl].
    + subst aa. destruct (is_feasible b a_hd ms); [discriminate|reflexivity].
    + destruct (is_feasible b a_hd ms); [discriminate|].
      eapply IH; eauto.
Qed.

(* If find_feasible is None, then pick_ask is None for each bid in bs. *)
Lemma find_feasible_None_forall :
  forall (bs : list Bid) (as_list : list Ask) (ms : list Match),
    find_feasible bs as_list ms = None ->
    forall (b : Bid), In b bs -> pick_ask b as_list ms = None.
Proof.
  intros bs as_list ms Hnone.
  induction bs as [|b_hd bs_tl IH]; intros b Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hin_eq | Hin_tl].
    + subst b. destruct (pick_ask b_hd as_list ms); [discriminate|reflexivity].
    + destruct (pick_ask b_hd as_list ms); [discriminate|].
      eauto.
Qed.

(* From “no feasible pair overall” derive the local justification condition. *)
Lemma no_feasible_pairs_gives_justification :
  forall s,
    find_feasible (bids s) (asks s) (matches s) = None ->
    justified_rejection s.
Proof.
  intros s Hnone.
  split.
  - (* rejected_bid side *)
    intros b aa [Hb_in _] Haa_in.
    pose proof
      (find_feasible_None_forall (bids s) (asks s) (matches s) Hnone b Hb_in)
      as Hb_none.
    pose proof
      (pick_ask_None_all_false b (asks s) (matches s) Hb_none aa Haa_in)
      as Hinf.
    right; exact Hinf.
  - (* rejected_ask side *)
    intros aa b [Haa_in _] Hb_in.
    pose proof
      (find_feasible_None_forall (bids s) (asks s) (matches s) Hnone b Hb_in)
      as Hb_none.
    pose proof
      (pick_ask_None_all_false b (asks s) (matches s) Hb_none aa Haa_in)
      as Hinf.
    right; exact Hinf.
Qed.

(* A small convenience equivalence for using match_step in proofs. *)
Lemma match_step_None_iff :
  forall s, match_step s = None <->
            find_feasible (bids s) (asks s) (matches s) = None.
Proof.
  intro s. unfold match_step.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf;
    split; intro H; try reflexivity; try discriminate.
Qed.

Theorem rejection_fairness_from_None :
  forall s, match_step s = None -> justified_rejection s.
Proof.
  intros s Hms.
  apply match_step_None_iff in Hms.
  eapply no_feasible_pairs_gives_justification; eauto.
Qed.

(* Phase-flavored wrapper if you use it after P4/P5/P6/P7. *)
Theorem rejection_fairness :
  forall s,
    (phase s = P4 \/ phase s = P5 \/ phase s = P6 \/ phase s = P7) ->
    find_feasible (bids s) (asks s) (matches s) = None ->
    justified_rejection s.
Proof.
  intros s _ Hnone.
  eapply no_feasible_pairs_gives_justification; eauto.
Qed.
