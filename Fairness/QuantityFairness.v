(** Chapter 4 (Fairness Verification Layer) — Section 4.3/4.4

  Quantity fairness: allocation is consistent with residual quantities.
  Proved as a global invariant over MUDA traces.
*)
From Stdlib Require Import Arith List Lia.
Import ListNotations.
From LTL      Require Import LTL.
From MUDA     Require Import MUDA Atoms.
From Fairness Require Import Interpretation.  (* for p_allocOK and mu_trace *)

Local Open Scope LTL_scope.

Definition quantityOK : LTL_formula := G (Atom p_allocOK).

Definition phase_ge_4 : LTL_formula :=
  Atom (p_phase 4) ∨ Atom (p_phase 5) ∨ Atom (p_phase 6) ∨ Atom (p_phase 7).

Definition priceOK : LTL_formula :=
  (* Chapter 4: price fairness is the global conjunction of the boundedness and
     the price-rule predicates. Totalisation for the undefined-price case is
     built into the atoms. *)
  G (Atom p_bounds_cstar)
  ∧ G (Atom p_price_rule).

Theorem quantity_fairness_initial : forall bs as_list,
  allocOK (initial_state bs as_list).
Proof.
  intros bs as_list.
  unfold allocOK, initial_state; simpl.
  split; intros; lia.
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

Theorem quantity_fairness_LTL_initial : forall bs as_list,
  satisfies (mu_trace (initial_state bs as_list)) 0 quantityOK.
Proof.
  intros bs as_list.
  unfold quantityOK.
  rewrite satisfies_always_unfold.
  intros j _.
  apply mu_trace_satisfies_allocOK_initial.
Qed.

Lemma bounds_cstar_from_wf : forall s,
  wf_state s -> bounds_cstar_prop s.
Proof.
  intros s Hwf.
  unfold bounds_cstar_prop.
  destruct (marginal_pair s) as [[b a]|] eqn:Hmp.
  - destruct (determine_clearing_price s) as [c|] eqn:Hdc.
    + apply (clearing_price_bounds s b a c); [exact Hwf | exact Hmp | exact Hdc].
    + exact I.
  - destruct (determine_clearing_price s) as [c|]; exact I.
Qed.

Lemma bounds_cstar_preserved_n : forall n bs as_list,
  bounds_cstar_prop (execute n (initial_state bs as_list)).
Proof.
  intros n bs as_list.
  apply bounds_cstar_from_wf.
  apply wf_state_execute_n.
  apply wf_state_initial.
Qed.

Lemma interp_atom_phase_4 : forall s, interp_atom s (p_phase 4) <-> phase s = P4.
Proof.
  intro s. unfold interp_atom, p_phase, nth_phase. simpl. tauto.
Qed.

Lemma interp_atom_phase_5 : forall s, interp_atom s (p_phase 5) <-> phase s = P5.
Proof.
  intro s. unfold interp_atom, p_phase, nth_phase. simpl. tauto.
Qed.

Lemma interp_atom_phase_6 : forall s, interp_atom s (p_phase 6) <-> phase s = P6.
Proof.
  intro s. unfold interp_atom, p_phase, nth_phase. simpl. tauto.
Qed.

Lemma interp_atom_phase_7 : forall s, interp_atom s (p_phase 7) <-> phase s = P7.
Proof.
  intro s. unfold interp_atom, p_phase, nth_phase. simpl. tauto.
Qed.


Lemma price_rule_fairness_LTL_initial : forall bs as_list,
  satisfies (mu_trace (initial_state bs as_list)) 0 (G (Atom p_price_rule)).
Proof.
  intros bs as_list.
  rewrite satisfies_always_unfold.
  intros j _.
  rewrite mu_trace_atom_at_execute.
  unfold interp_atom.
  (* goal: price_rule_prop (execute j (initial_state bs as_list)) *)
  unfold price_rule_prop.
  destruct (phase (execute j (initial_state bs as_list))) eqn:Hphase; simpl.
  - (* P1 *) exact I.
  - (* P2 *) exact I.
  - (* P3 *) exact I.
  - (* P4 *)
    destruct (marginal_pair (execute j (initial_state bs as_list))) as [[b a]|] eqn:Hmp; simpl; auto.
    unfold determine_clearing_price. rewrite Hmp. reflexivity.
  - (* P5 *)
    destruct (marginal_pair (execute j (initial_state bs as_list))) as [[b a]|] eqn:Hmp; simpl; auto.
    unfold determine_clearing_price. rewrite Hmp. reflexivity.
  - (* P6 *)
    destruct (marginal_pair (execute j (initial_state bs as_list))) as [[b a]|] eqn:Hmp; simpl; auto.
    unfold determine_clearing_price. rewrite Hmp. reflexivity.
  - (* P7 *)
    destruct (marginal_pair (execute j (initial_state bs as_list))) as [[b a]|] eqn:Hmp; simpl; auto.
    unfold determine_clearing_price. rewrite Hmp. reflexivity.
Qed.

Theorem uniform_price_fairness_LTL_initial : forall bs as_list,
  satisfies (mu_trace (initial_state bs as_list)) 0 priceOK.
Proof.
  intros bs as_list.
  unfold priceOK.
  split.
  - rewrite satisfies_always_unfold.
    intros j _. 
    rewrite mu_trace_atom_at_execute.
    unfold interp_atom.
    change (bounds_cstar_prop (execute j (initial_state bs as_list))).
    apply bounds_cstar_preserved_n.
  - apply price_rule_fairness_LTL_initial.
Qed.
