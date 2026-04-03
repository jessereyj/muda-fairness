From Stdlib Require Import Arith List.
From LTL  Require Import Syntax Semantics.
From MUDA Require Import Types State Matching ClearingPrice Transitions Atoms.
From Fairness Require Import Interpretation.

Local Open Scope LTL_scope.

Definition priceOK : LTL_formula :=
  (* Chapter 4: price fairness is expressed over the MUDA execution trace using
     state-derived atomic propositions for clearing-price existence, boundedness,
     and the clearing-price rule. *)
  G (Atom p_has_cprice → (Atom p_bounds_cstar ∧ Atom p_price_rule)).

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

(* Price rule holds pointwise by definition of determine_clearing_price. *)
Lemma price_rule_fairness_LTL_initial : forall bs as_list,
  satisfies (mu_trace (initial_state bs as_list)) 0 (G (Atom p_price_rule)).
Proof.
  intros bs as_list.
  rewrite satisfies_always_unfold.
  intros j _.
  rewrite mu_trace_atom_at_execute.
  unfold interp_atom.
  (* goal: price_rule_prop (execute j initial) *)
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
  (* Prove the implication by establishing its consequent at every index. *)
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
