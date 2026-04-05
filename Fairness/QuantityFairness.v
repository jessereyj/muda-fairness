From Stdlib Require Import Arith List Lia.
From LTL      Require Import Syntax Semantics.
From MUDA     Require Import Types State Matching Transitions Atoms.
From Fairness Require Import Interpretation.  (* for p_allocOK and mu_trace *)

(** Panel index (thesis ↔ code)

  Chapter 4 (Quantity fairness)
  - quantityOK: LTL formula G(p_allocOK)
  - quantity_fairness_LTL_initial: main theorem (holds for all initial states)
*)

Local Open Scope LTL_scope.

(* quantityOK: LTL formula asserting allocOK_prop holds at every time (Chapter 4). *)
Definition quantityOK : LTL_formula := G (Atom p_allocOK).

(* quantity_fairness_LTL_initial: LTL lift — quantityOK holds on μ(initial_state). *)
Theorem quantity_fairness_LTL_initial : forall bs as_list,
  satisfies (mu_trace (initial_state bs as_list)) 0 quantityOK.
Proof.
  intros bs as_list.
  unfold quantityOK.
  rewrite satisfies_always_unfold.
  intros j _.
  apply (proj2 (mu_trace_atom_at_execute (initial_state bs as_list) j p_allocOK)).
  unfold interp_atom.
  (* Goal: allocOK_prop on execute j initial. *)
  unfold allocOK_prop.
  assert (Halloc0 : allocOK (initial_state bs as_list)).
  { unfold allocOK, initial_state; simpl.
    split; intro x; lia.
  }
  assert (Hstep : forall s, allocOK s -> allocOK (step s)).
  { intros s H.
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
  }
  assert (Hexec : forall n s, allocOK s -> allocOK (execute n s)).
  { induction n as [|n IH]; intros s H; simpl.
    - exact H.
    - apply IH.
      apply Hstep.
      exact H.
  }
  assert (Hallocj : allocOK (execute j (initial_state bs as_list))).
  { apply Hexec. exact Halloc0. }
  destruct Hallocj as [Hb Ha].
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
