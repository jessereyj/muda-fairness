From Stdlib Require Import Arith List.
From LTL  Require Import Syntax Semantics.
From MUDA Require Import Types State Matching ClearingPrice Transitions Atoms.
From Fairness Require Import Interpretation.

(** Panel index (thesis ↔ code)

  Chapter 4 (Uniform price fairness)
  - priceOK: LTL formula G(p_has_cprice → (p_bounds_pstar ∧ p_price_rule))
  - uniform_price_fairness_LTL_initial: main theorem (holds for all initial states)

  Chapter 3/4 (State-field connection)
  - clearing_price_field_agrees_determine_initial: stored clearing_price agrees with determine_clearing_price once populated
  - clearing_price_field_bounds_initial: stored clearing_price satisfies marginal bounds once populated
  - clearing_price_field_rule_initial: stored clearing_price satisfies the deterministic price rule once populated
*)

Local Open Scope LTL_scope.

(* priceOK: LTL formula for uniform price fairness (bounds + deterministic price rule). *)
Definition priceOK : LTL_formula :=
  G (Atom p_has_cprice → (Atom p_bounds_pstar ∧ Atom p_price_rule)).

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
  - (* bounds_pstar *)
    change (satisfies (mu_trace (initial_state bs as_list)) j (Atom p_bounds_pstar)).
    apply (proj2 (mu_trace_atom_at_execute (initial_state bs as_list) j p_bounds_pstar)).
    unfold interp_atom.
    change (bounds_pstar_prop (execute j (initial_state bs as_list))).
    pose proof
      (wf_state_execute_n j (initial_state bs as_list) (wf_state_initial bs as_list))
      as Hwf.
    unfold bounds_pstar_prop.
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

(* cprice_post_pricing_initial: initial_state carries no clearing price. *)
Lemma cprice_post_pricing_initial : forall bs as_list,
  cprice_post_pricing (initial_state bs as_list).
Proof.
  intros bs as_list c Hcp.
  simpl in Hcp.
  discriminate.
Qed.

(* cprice_post_pricing_execute_initial: along execute, any stored clearing price implies phase ∈ {P5,P6,P7}. *)
Lemma cprice_post_pricing_execute_initial : forall bs as_list j,
  cprice_post_pricing (execute j (initial_state bs as_list)).
Proof.
  intros bs as_list j.
  apply cprice_post_pricing_execute_n.
  apply cprice_post_pricing_initial.
Qed.

(* cprice_field_ok_initial: initial_state trivially satisfies cprice_field_ok_prop. *)
Lemma cprice_field_ok_initial : forall bs as_list,
  cprice_field_ok_prop (initial_state bs as_list).
Proof.
  intros bs as_list.
  simpl.
  exact I.
Qed.

(* cprice_field_ok_execute_initial: along execute, the stored field agrees with determine once populated. *)
Lemma cprice_field_ok_execute_initial : forall bs as_list j,
  cprice_field_ok_prop (execute j (initial_state bs as_list)).
Proof.
  intros bs as_list j.
  apply cprice_field_ok_execute_n.
  apply cprice_field_ok_initial.
Qed.

(* clearing_price_field_agrees_determine_initial: whenever the state carries Some c,
   the stored value equals the computed determine_clearing_price. *)
Theorem clearing_price_field_agrees_determine_initial : forall bs as_list j c,
  clearing_price (execute j (initial_state bs as_list)) = Some c ->
  determine_clearing_price (execute j (initial_state bs as_list)) = Some c.
Proof.
  intros bs as_list j c Hcp.
  pose proof (cprice_post_pricing_execute_initial bs as_list j c Hcp) as Hphase.
  pose proof (cprice_field_ok_execute_initial bs as_list j) as Hok.
  unfold cprice_field_ok_prop in Hok.
  destruct Hphase as [Hp5|[Hp6|Hp7]].
  - rewrite Hp5 in Hok. simpl in Hok. rewrite Hcp in Hok. exact Hok.
  - rewrite Hp6 in Hok. simpl in Hok. rewrite Hcp in Hok. exact Hok.
  - rewrite Hp7 in Hok. simpl in Hok. rewrite Hcp in Hok. exact Hok.
Qed.

(* clearing_price_field_bounds_initial: whenever clearing_price is stored and the marginal pair exists,
   the stored value lies within the marginal bounds. *)
Theorem clearing_price_field_bounds_initial : forall bs as_list j c b a,
  clearing_price (execute j (initial_state bs as_list)) = Some c ->
  marginal_pair (execute j (initial_state bs as_list)) = Some (b, a) ->
  ask_price a <= c /\ c <= price b.
Proof.
  intros bs as_list j c b a Hcp Hmp.
  pose proof (clearing_price_field_agrees_determine_initial bs as_list j c Hcp) as Hdc.
  pose proof
    (wf_state_execute_n j (initial_state bs as_list) (wf_state_initial bs as_list))
    as Hwf.
  apply (clearing_price_bounds (execute j (initial_state bs as_list)) b a c);
    [exact Hwf | exact Hmp | exact Hdc].
Qed.

(* clearing_price_field_rule_initial: whenever clearing_price is stored, it is determined by the
   deterministic rule applied to the marginal pair. *)
Theorem clearing_price_field_rule_initial : forall bs as_list j c b a,
  clearing_price (execute j (initial_state bs as_list)) = Some c ->
  marginal_pair (execute j (initial_state bs as_list)) = Some (b, a) ->
  (if (residual_ask a (matches (execute j (initial_state bs as_list))) =? 0)
   then c = price b
   else c = ask_price a).
Proof.
  intros bs as_list j c b a Hcp Hmp.
  pose proof (clearing_price_field_agrees_determine_initial bs as_list j c Hcp) as Hdc.
  unfold determine_clearing_price in Hdc; rewrite Hmp in Hdc.
  remember (residual_ask a (matches (execute j (initial_state bs as_list))) =? 0) as ea eqn:Hea.
  destruct ea; simpl in Hdc; inversion Hdc; subst; reflexivity.
Qed.
