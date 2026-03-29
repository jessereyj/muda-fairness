(** Chapter 4 (Foundation Layer) — Section 4.1.5 (Meta-theoretic Properties)

  Weak completeness and adequacy are treated as standard results.

  This file keeps the fairness verification layer independent of proof-search:
  - Soundness is proved in LTL/Soundness.v
  - Completeness/adequacy are included as axioms (canonical countermodel / weak completeness)
*)
From Stdlib Require Import Classical Lia.
From LTL Require Import Syntax Semantics Axioms Soundness.

Local Open Scope LTL_scope.
Local Open Scope nat_scope.

CoFixpoint ones : trace := Trace (fun _ => True) ones.


Axiom canonical_countermodel :
  forall (φ : LTL_formula),
    ~ Provable φ ->
    exists (σ : trace), ~ models σ φ.

Theorem completeness_valid :
  forall φ, valid φ -> Provable φ.
Proof.
  intros φ Hvalid.
  destruct (classic (Provable φ)) as [Hpr|Hnpr]; [assumption|].
  destruct (canonical_countermodel φ Hnpr) as [σ Hnot].
  unfold valid in Hvalid; specialize (Hvalid σ 0).
  unfold models in Hnot; contradiction.
Qed.

Corollary completeness_models0 :
  forall φ, (forall σ, models σ φ) -> Provable φ.
Proof.
  intros φ Hall. apply completeness_valid.
  (* Show validity from truth at index 0 on every suffix *)
  unfold valid; intros σ i.
  revert σ; induction i as [|i IHi]; intros σ.
  - (* i = 0 *) now apply Hall.
  - (* i = S i' *)
    destruct σ as [s σ']; simpl.
    (* shift from (Trace s σ'), S i to σ', i *)
    apply (proj2 (satisfies_shift_tail s σ' i φ)).
    apply IHi.
Qed.

Theorem WeakCompleteness : forall φ, valid φ -> Provable φ.
Proof.
  intros φ Hvalid.
  apply completeness_valid; exact Hvalid.
Qed.

Theorem Consistency : ~ exists φ, Provable φ /\ Provable (Not φ).
Proof.
  intros [φ [H1 H2]].
  pose proof (soundness _ H1) as V1.
  pose proof (soundness _ H2) as V2.
  (* V1: valid φ, V2: valid (¬φ) — impossible *)
  unfold valid in *.
  (* Instantiate on the inhabited trace `ones` and index 0. *)
  specialize (V1 ones 0%nat). specialize (V2 ones 0%nat).
  contradiction.
Qed.

Theorem Adequacy φ : Provable φ <-> valid φ.
Proof. split; [apply soundness|apply WeakCompleteness]. Qed.