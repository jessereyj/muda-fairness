(* Fairness/JustifiedRejection.v *)
From Stdlib Require Import List.
Import ListNotations.
From LTL  Require Import LTL.
From MUDA Require Import MUDA Atoms Matching.
From Fairness Require Import Interpretation.
Local Open Scope LTL_scope.

Definition rejectionOK : LTL_formula :=
  G ( (Atom (p_phase 4) ∨ Atom (p_phase 5) ∨ Atom (p_phase 6) ∨ Atom (p_phase 7))
      → Atom p_rejection_justified ).

Lemma no_feasible_pairs_gives_justification :
  forall s,
    find_feasible (bids s) (asks s) (matches s) = None ->
    rejection_justified_prop s.
Proof.
  intros s Hnone.
  split.
  - (* rejected_bid side *)
    intros b aa [Hb_in _] Haa_in.
    pose proof (find_feasible_None_forall (bids s) (asks s) (matches s) Hnone b aa Hb_in Haa_in)
      as Hinf.
    right; exact Hinf.
  - (* rejected_ask side *)
    intros aa b [Haa_in _] Hb_in.
    pose proof (find_feasible_None_forall (bids s) (asks s) (matches s) Hnone b aa Hb_in Haa_in)
      as Hinf.
    right; exact Hinf.
Qed.

Lemma match_step_None_iff :
  forall s, match_step s = None <->
            find_feasible (bids s) (asks s) (matches s) = None.
Proof.
  intro s. unfold match_step.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf;
    split; intro H; try reflexivity; try discriminate.
Qed.

Theorem justified_rejection_from_None :
  forall s, match_step s = None -> rejection_justified_prop s.
Proof.
  intros s Hms.
  apply match_step_None_iff in Hms.
  eapply no_feasible_pairs_gives_justification; eauto.
Qed.

Theorem justified_rejection :
  forall s,
    (phase s = P4 \/ phase s = P5 \/ phase s = P6 \/ phase s = P7) ->
    find_feasible (bids s) (asks s) (matches s) = None ->
    rejection_justified_prop s.
Proof.
  intros s _ Hnone.
  eapply no_feasible_pairs_gives_justification; eauto.
Qed.
