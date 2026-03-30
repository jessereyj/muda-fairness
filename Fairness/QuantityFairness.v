(** Chapter 4 (Fairness Verification Layer) — Section 4.3/4.4

  Quantity fairness: allocation is consistent with residual quantities.
  Proved as a global invariant over MUDA traces.

  Chapter 4 math notation view:
  - `matched(b, s, q)` ranges over the match record
  - `residualB(b)` / `residualS(s)` are the remaining quantities
*)
From Stdlib Require Import Arith List Lia.
Import ListNotations.
From LTL      Require Import LTL.
From MUDA     Require Import MUDA Atoms.
From Fairness Require Import Interpretation.  (* for p_allocOK and mu_trace *)

Local Open Scope LTL_scope.

Definition quantityOK : LTL_formula := G (Atom p_allocOK).

Definition priceOK : LTL_formula :=
  (* Chapter 4: price fairness is the global conjunction of the boundedness and
     the price-rule predicates. Totalisation for the undefined-price case is
     built into the atoms. *)
  G (Atom p_has_cprice → (Atom p_bounds_cstar ∧ Atom p_price_rule)).

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
  rewrite satisfies_always_unfold.
  intros j _.
  (* Prove the implication by establishing its consequent at every index.
     This matches the intended reading: whenever a clearing price exists, it
     follows the rule and is within bounds; the atoms are totalized so the
     consequent is also well-defined on no-trade executions. *)
  simpl.
  right.
  split.
  - (* bounds_cstar *)
    change (satisfies (mu_trace (initial_state bs as_list)) j (Atom p_bounds_cstar)).
    apply (proj2 (mu_trace_atom_at_execute (initial_state bs as_list) j p_bounds_cstar)).
    unfold interp_atom.
    change (bounds_cstar_prop (execute j (initial_state bs as_list))).
    apply bounds_cstar_preserved_n.
  - (* price_rule *)
    change (satisfies (mu_trace (initial_state bs as_list)) j (Atom p_price_rule)).
    pose proof (price_rule_fairness_LTL_initial bs as_list) as Hrule.
    rewrite satisfies_always_unfold in Hrule.
    exact (Hrule j (Nat.le_0_l j)).
Qed.
