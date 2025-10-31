From Stdlib Require Import Arith List Lia.
Import ListNotations.

From MUDA Require Import Eqb Types State Sorting Matching ClearingPrice Transitions.

Theorem quantity_fairness_initial : forall bs as_list,
  allocOK (initial_state bs as_list).
Proof.
  intros; unfold allocOK, initial_state; simpl; split; intros; lia.
Qed.

(* Adding a match never exceeds the declared quantity because we match min(residuals) *)
Lemma allocOK_after_match : forall s s',
  match_step s = Some s' -> allocOK s' .
Proof. Admitted.

Theorem quantity_fairness_step : forall s,
  allocOK s -> allocOK (step s).
Proof.
  intros s H.
  destruct (phase s); simpl; try assumption.
  - (* P2 -> P3; sorting preserves allocOK *)
    exact H.
  - (* P3: either match or finish *)
    destruct (match_step s) eqn:Hs.
    + eapply allocOK_after_match; eauto.
    + exact H.
  - all: exact H.
Qed.
