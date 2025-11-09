(* Fairness/QuantityFairness.v *)
From Stdlib Require Import Arith List Lia.
Import ListNotations.

From LTL      Require Import LTL.
From MUDA     Require Import MUDA Atoms.
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

(* Lifting for initial states: At any index i, p_allocOK holds on mu_trace of an initial state. *)
Lemma allocOK_to_prop : forall s, allocOK s -> allocOK_prop s.
Proof. intros s H; exact H. Qed.

Lemma mu_trace_satisfies_allocOK_initial :
  forall bs as_list i,
    satisfies (mu_trace (initial_state bs as_list)) i (Atom p_allocOK).
Proof.
  intros bs as_list i.
  apply (proj2 (mu_trace_atom_at_execute (initial_state bs as_list) i p_allocOK)).
  unfold interp_atom.
  (* Need allocOK_prop on execute i initial *)
  apply allocOK_to_prop.
  apply allocOK_preserved_n.
  apply quantity_fairness_initial.
Qed.

(* Global quantity fairness on traces for initial states. *)
Theorem quantity_fairness_LTL_initial : forall bs as_list,
  satisfies (mu_trace (initial_state bs as_list)) 0 quantityOK.
Proof.
  intros bs as_list.
  unfold quantityOK.
  rewrite satisfies_always_unfold.
  intros j _.
  apply mu_trace_satisfies_allocOK_initial.
Qed.
