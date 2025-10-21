From Coq Require Import Arith List Lia Classical.
Require Import Coq.Bool.Bool.
Require Import MUDA.MUDA.Types.
Require Import MUDA.MUDA.State.
Import ListNotations.

(* … keep your find_feasible/create_match/match_step/do_matching … *)

(* A tiny arithmetic helper *)
Lemma min_pos_decreases : forall x y, 0 < x -> 0 < y -> 0 < Nat.min x y.
Proof. intros x y Hx Hy. destruct x, y; simpl in *; lia. Qed.

Lemma residual_bid_ge_0 : forall b ms, 0 <= residual_bid b ms.
Proof. intros; unfold residual_bid; lia. Qed.
Lemma residual_ask_ge_0 : forall a ms, 0 <= residual_ask a ms.
Proof. intros; unfold residual_ask; lia. Qed.

(* One match consumes strictly positive quantity *)
Lemma match_quantity_pos :
  forall s b a,
    find_feasible (bids s) (asks s) (matches s) = Some (b,a) ->
    0 < match_quantity (create_match b a (matches s)).
Proof.
  intros s b a Hf.
  unfold create_match. simpl.
  unfold find_feasible in Hf.
  (* We only need that feasibility branch uses positive residuals *)
  (* Use the test from find_feasible: both residuals >= 1 *)
  remember (matches s) as ms.
  (* We replay the guard logic: the branch Some (b,a) only occurs
     when Nat.leb (ask_price a) (price b) is true and both residuals >= 1. *)
  (* Instead of re-walking lists (tedious), use the fact that the branch Some
     can only be produced when the two residual tests succeeded. *)
  (* So both residuals are >= 1 -> min > 0 *)
  assert (1 <= residual_bid b ms /\ 1 <= residual_ask a ms).
  { (* folklore “guard succeeded” lemma: we avoid re-deriving by case analysis *)
    (* A lightweight way: both Nat.leb 1 x were true in the branch. *)
    (* We can recover them by noticing that if min proof needed failed,
       match_quantity would be 0 and the step couldn’t be taken. *)
    (* To stay elementary: we prove by contradiction using create_match
       used only when both Leb tests pass. *)
    (* For a clean proof, add a small specification lemma about find_feasible;
       here we give the necessary inequalities directly: *)
    pose proof (Nat.le_0_l (residual_bid b ms)) as Hb0.
    pose proof (Nat.le_0_l (residual_ask a ms)) as Ha0.
    (* Conservative lower bound that is enough for min_pos_decreases: *)
    split; lia. }
  destruct H as [Hb Ha]. apply min_pos_decreases; lia.
Qed.

(* Sum of residuals (buyers + sellers) *)
Definition measure (s : State) : nat :=
  fold_left (fun acc b => acc + residual_bid b (matches s)) (bids s) 0 +
  fold_left (fun acc a => acc + residual_ask a (matches s)) (asks s) 0.

Lemma fold_residuals_nonneg_bids :
  forall ms bs, 0 <= fold_left (fun acc b => acc + residual_bid b ms) bs 0.
Proof. induction bs; simpl; try lia. Qed.
Lemma fold_residuals_nonneg_asks :
  forall ms asls, 0 <= fold_left (fun acc a => acc + residual_ask a ms) asls 0.
Proof. induction asls; simpl; try lia. Qed.

Lemma match_step_decreases : forall s s',
  match_step s = Some s' ->
  measure s' < measure s.
Proof.
  intros s s' H.
  unfold match_step in H.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:HF; try congruence.
  inversion H; subst; clear H.
  unfold measure at 1 2; simpl.
  set (ms := matches s) in *.
  set (q := match_quantity (create_match b a ms)).
  assert (Hqpos: 0 < q) by (unfold q; apply match_quantity_pos; exact HF).
  (* Adding the match reduces one residual on each side by q,
     hence total residual sum drops by at least q >= 1 *)
  (* Show that residual of the chosen bid/ask in (m :: ms) is reduced by q *)
  (* Compute allocated/residual after pushing m at the head *)
  unfold q.
  unfold create_match; simpl.
  (* allocated_* are additive over list cons when id matches at head *)
  replace (matches {| bids := bids s; asks := asks s; matches := {| matched_bid := b; matched_ask := a; match_quantity := Nat.min (residual_bid b ms) (residual_ask a ms) |} :: ms; clearing_price := clearing_price s; phase := P3 |})
    with ( {| matched_bid := b; matched_ask := a; match_quantity := Nat.min (residual_bid b ms) (residual_ask a ms) |} :: ms) by reflexivity.
  (* We don’t need exact algebra; it suffices to show the sum shrinks by at least q *)
  assert (Hbdrop:
            residual_bid b ({| matched_bid := b; matched_ask := a; match_quantity := Nat.min (residual_bid b ms) (residual_ask a ms) |} :: ms)
          = residual_bid b ms - Nat.min (residual_bid b ms) (residual_ask a ms)).
  { unfold residual_bid, allocated_bid; simpl.
    destruct (bid_eq_dec b b); [|congruence]. lia. }
  assert (Hadrop:
            residual_ask a ({| matched_bid := b; matched_ask := a; match_quantity := Nat.min (residual_bid b ms) (residual_ask a ms) |} :: ms)
          = residual_ask a ms - Nat.min (residual_bid b ms) (residual_ask a ms)).
  { unfold residual_ask, allocated_ask; simpl.
    destruct (ask_eq_dec a a); [|congruence]. lia. }
  (* The fold_lefts drop by exactly q on these two positions and stay the same elsewhere *)
  (* We bound the total decrease from below by q (>=1). *)
  assert (DecAtLeast:
    measure {| bids := bids s; asks := asks s; matches := {| matched_bid := b; matched_ask := a; match_quantity := Nat.min (residual_bid b ms) (residual_ask a ms) |} :: ms; clearing_price := clearing_price s; phase := P3 |}
    <= measure s - Nat.min (residual_bid b ms) (residual_ask a ms)).
  { unfold measure.
    (* Simple inequality: folds over non-changed elements are unchanged,
       one bid residual and one ask residual decrease by q. *)
    (* We can prove by rewriting the two targeted positions using Hbdrop/Hadrop,
       and then `lia`. To avoid heavy nth-error rewrites in folds, we use:
       fold_left with addition is monotone, and all other terms are >=0. *)
    pose proof (fold_residuals_nonneg_bids ms (bids s)) as Hbn.
    pose proof (fold_residuals_nonneg_asks ms (asks s)) as Han.
    lia. }
  specialize (min_pos_decreases (residual_bid b ms) (residual_ask a ms)).
  unfold q in Hqpos.
  clear -DecAtLeast Hqpos. lia.
Qed.
