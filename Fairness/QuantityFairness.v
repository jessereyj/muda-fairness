(** Chapter 4 (Fairness Verification Layer) — Section 4.3/4.4

  Quantity fairness: allocation is consistent with residual quantities.
  Proved as a global invariant over MUDA traces.

  Chapter 4 math notation view:
  - `matched(b, s, q)` ranges over the match record
  - `residualB(b)` / `residualS(s)` are the remaining quantities

  Chapter 4 quantity fairness formula (thesis notation):

    sum_matches(b, x) = Σ{ q | matched(b, s, q, x) }

    φ_qty = G(
      initial(b) = sum_matches(b, x) + residualB(b, x)
    )

  Mechanization note:
  - `sum_matches` is `allocated_bid`.
  - `residualB` is `residual_bid` (computed as `initial - allocated`).
  - The trace-level atom `p_allocOK` is interpreted as this equality for all
    bids/asks, and `φ_qty := G(Atom p_allocOK)`.
*)
From Stdlib Require Import Arith List Lia.
Import ListNotations.
From LTL      Require Import LTL.
From MUDA     Require Import MUDA Atoms.
From Fairness Require Import Interpretation.  (* for p_allocOK and mu_trace *)

Local Open Scope LTL_scope.

Definition quantityOK : LTL_formula := G (Atom p_allocOK).

(* Chapter 4 notation alias. *)
Definition phi_qty : LTL_formula := quantityOK.

Theorem quantity_fairness_initial : forall bs as_list,
  allocOK (initial_state bs as_list).
Proof.
  intros bs as_list.
  unfold allocOK, initial_state; simpl.
  split; intro x; lia.
Qed.

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

Lemma allocOK_preserved_n :
  forall n s, allocOK s -> allocOK (execute n s).
Proof.
  induction n as [|n IH]; intros s H; simpl; [exact H|].
  apply IH, quantity_fairness_step, H.
Qed.

Lemma allocOK_to_prop : forall s, allocOK s -> allocOK_prop s.
Proof.
  intros s [Hb Ha].
  split.
  - intro b.
    unfold residual_bid.
    rewrite Nat.add_comm.
    symmetry.
    apply Nat.sub_add.
    exact (Hb b).
  - intro a.
    unfold residual_ask.
    rewrite Nat.add_comm.
    symmetry.
    apply Nat.sub_add.
    exact (Ha a).
Qed.

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

Theorem quantity_fairness_LTL_initial : forall bs as_list,
  satisfies (mu_trace (initial_state bs as_list)) 0 quantityOK.
Proof.
  intros bs as_list.
  unfold quantityOK.
  rewrite satisfies_always_unfold.
  intros j _.
  apply mu_trace_satisfies_allocOK_initial.
Qed.
