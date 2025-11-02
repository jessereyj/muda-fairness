(* Fairness/Maximality.v *)
From Stdlib Require Import Arith List.
Import ListNotations.

From MUDA Require Import Eqb Types State Sorting Matching ClearingPrice Transitions.

(* --- Local progress/exit at P3 ------------------------------------------- *)

Lemma step_P3_progress_or_exit : forall s,
  phase s = P3 ->
  (exists s', match_step s = Some s') \/ (match_step s = None).
Proof.
  intros s Hp.
  unfold match_step.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:HF.
  - left. eexists; reflexivity.
  - right. reflexivity.
Qed.

(* If we are in P3 and no feasible pair, the next phase is P4. *)
Lemma step_P4_from_P3_None : forall s,
  phase s = P3 ->
  match_step s = None ->
  phase (step s) = P4.
Proof.
  intros s Hp Hnone.
  unfold step. rewrite Hp. simpl. rewrite Hnone. reflexivity.
Qed.

(* Inversion for one step to P4 (keep admitted for now, per your plan). *)
Lemma step_P4_inversion : forall s,
  phase (step s) = P4 ->
  phase s = P3 /\ match_step s = None.
Admitted.

(* A small helper: the defining equation of execute. *)
Lemma execute_S : forall n s, execute (S n) s = execute n (step s).
Proof. reflexivity. Qed.

(* --- Multi-step “last P3 predecessor” without commuting step past execute - *)
(* This is what you were trying to use step_P4_inversion on; instead, do an  *)
(* induction on n and rewrite with execute_S at each step.                   *)

Lemma last_P3_predecessor :
  forall s n,
    phase (execute (S n) s) = P4 ->
    exists t,
      t = execute n s
      /\ phase t = P3
      /\ match_step t = None.
Proof.
  intros s n H.
  (* We proceed by induction on n, not by commuting step past execute. *)
  induction n as [|n IH] in s, H |- *.
  - (* n = 0: execute (S 0) s = step s *)
    simpl in H. (* H : phase (step s) = P4 *)
    destruct (step_P4_inversion s H) as [Hp3 Hnone].
    exists s. repeat split; auto.
  - (* n = S n: execute (S (S n)) s = execute (S n) (step s) *)
    rewrite execute_S in H. (* H : phase (execute (S n) (step s)) = P4 *)
    (* Apply IH to s' := step s *)
    specialize (IH (step s) H) as [t [Ht_eq [Hp3 Hnone]]].
    (* We need t = execute (S n) s. By the defn, execute (S n) s = execute n (step s) *)
    exists (execute (S n) s).
    split.
    + reflexivity.
    + (* transport phase/match_step facts along definitional equalities *)
      (* From Ht_eq : t = execute n (step s) and execute (S n) s = execute n (step s) *)
      (* we can rewrite Hp3 and Hnone directly. *)
      (* replace t by execute n (step s) in Hp3/Hnone using Ht_eq *)
      subst t.
      split; [assumption | assumption].
Qed.

(* A convenient corollary that states just the properties, without the witness. *)
Lemma no_feasible_when_P4_reached :
  forall s n,
    phase (execute (S n) s) = P4 ->
    phase (execute n s) = P3 /\ match_step (execute n s) = None.
Proof.
  intros s n H.
  destruct (last_P3_predecessor s n H) as [t [-> [Hp3 Hnone]]].
  split; assumption.
Qed.
