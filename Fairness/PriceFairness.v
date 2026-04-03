From Stdlib Require Import Arith List.
From LTL  Require Import Syntax Semantics.
From MUDA Require Import Types State Matching ClearingPrice Transitions Atoms.
From Fairness Require Import Interpretation.

(** Panel index (thesis ↔ code)

  Chapter 4 (Uniform price fairness)
  - priceOK: LTL formula G(p_has_cprice → (p_bounds_cstar ∧ p_price_rule))
  - uniform_price_fairness_LTL_initial: main theorem (holds for all initial states)
*)

Local Open Scope LTL_scope.

(* priceOK: LTL formula for uniform price fairness (bounds + deterministic price rule). *)
Definition priceOK : LTL_formula :=
  G (Atom p_has_cprice → (Atom p_bounds_cstar ∧ Atom p_price_rule)).

(* uniform_price_fairness_LTL_initial: LTL lift — priceOK holds on μ(initial_state). *)
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
    pose proof
      (wf_state_execute_n j (initial_state bs as_list) (wf_state_initial bs as_list))
      as Hwf.
    unfold bounds_cstar_prop.
    destruct (marginal_pair (execute j (initial_state bs as_list))) as [[b a]|] eqn:Hmp;
      destruct (determine_clearing_price (execute j (initial_state bs as_list))) as [c|] eqn:Hdc;
      simpl; try exact I.
    apply (clearing_price_bounds (execute j (initial_state bs as_list)) b a c);
      [exact Hwf | exact Hmp | exact Hdc].
  - (* price_rule *)
    change (satisfies (mu_trace (initial_state bs as_list)) j (Atom p_price_rule)).
    apply (proj2 (mu_trace_atom_at_execute (initial_state bs as_list) j p_price_rule)).
    unfold interp_atom.
    (* goal: price_rule_prop (execute j initial) *)
    unfold price_rule_prop.
    destruct (phase (execute j (initial_state bs as_list))) eqn:Hphase; simpl.
    + (* P1 *) exact I.
    + (* P2 *) exact I.
    + (* P3 *) exact I.
    + (* P4 *)
      destruct (marginal_pair (execute j (initial_state bs as_list))) as [[b a]|] eqn:Hmp; simpl; auto.
      unfold determine_clearing_price. rewrite Hmp. reflexivity.
    + (* P5 *)
      destruct (marginal_pair (execute j (initial_state bs as_list))) as [[b a]|] eqn:Hmp; simpl; auto.
      unfold determine_clearing_price. rewrite Hmp. reflexivity.
    + (* P6 *)
      destruct (marginal_pair (execute j (initial_state bs as_list))) as [[b a]|] eqn:Hmp; simpl; auto.
      unfold determine_clearing_price. rewrite Hmp. reflexivity.
    + (* P7 *)
      destruct (marginal_pair (execute j (initial_state bs as_list))) as [[b a]|] eqn:Hmp; simpl; auto.
      unfold determine_clearing_price. rewrite Hmp. reflexivity.
Qed.
