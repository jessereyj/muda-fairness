(* Fairness/QuantityFairness.v *)
From Stdlib Require Import Arith List Lia.
Import ListNotations.

From LTL      Require Import LTL.
From MUDA     Require Import MUDA.
From Fairness Require Import Interpretation.  (* for p_allocOK and mu_trace *)

Local Open Scope LTL_scope.

(* LTL specification alias for Section 4 *)
Definition quantityOK : LTL_formula := G (Atom p_allocOK).

(* ===== Initial state ===== *)
Theorem quantity_fairness_initial : forall bs as_list,
  allocOK (initial_state bs as_list).
Proof.
  intros bs as_list.
  unfold allocOK, initial_state; simpl.
  split; intros; lia.
Qed.

(* ===== One-step preservation across the pipeline ===== *)
Theorem quantity_fairness_step :
  forall s, allocOK s -> allocOK (step s).
Proof.
  intros s H.
  destruct (phase s) eqn:Hp.
  - (* P1 → P2 *)
    unfold step; rewrite Hp; exact H.
  - (* P2: sorting preserves bounds *)
    eapply allocOK_after_sorting; eauto.
  - (* P3: either add a match or finish *)
    unfold step; rewrite Hp.
    destruct (match_step s) eqn:Hs.
    + eapply allocOK_after_match; eauto.
    + exact H.
  - (* P4 *)
    unfold step; rewrite Hp; exact H.
  - (* P5 *)
    unfold step; rewrite Hp; exact H.
  - (* P6 *)
    unfold step; rewrite Hp; exact H.
  - (* P7 *)
    unfold step; rewrite Hp; exact H.
Qed.

(* ===== n-step preservation, used to lift to LTL traces ===== *)
Lemma allocOK_preserved_n :
  forall n s, allocOK s -> allocOK (execute n s).
Proof.
  induction n as [|n IH]; intros s H; simpl; [exact H|].
  apply IH, quantity_fairness_step, H.
Qed.
