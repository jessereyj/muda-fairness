(* Fairness/RejectionFairness.v *)
From Stdlib Require Import List.
Import ListNotations.
From LTL  Require Import LTL.           (* re-export module *)
From MUDA Require Import MUDA Atoms Matching.
From Fairness Require Import Interpretation. (* for p_match_keep p_rejection_justified *)

Local Open Scope LTL_scope.

(* LTL formula (Section 4.3.6 Option A): after phase ≥ P4 every rejection is justified. *)
Definition rejectionOK : LTL_formula :=
  G ( (Atom (p_phase 4) ∨ Atom (p_phase 5) ∨ Atom (p_phase 6) ∨ Atom (p_phase 7))
      → Atom p_rejection_justified ).

(* ---------- Rejection predicates ---------- *)
(* Rejection predicates and justification now come from MUDA/Atoms via
   Interpretation atom p_rejection_justified. We retain local lemmas operating
   over find_feasible to derive the global justification atom. *)

(* ------------------------------------------------------------------------ *)
(* From “no feasible pair overall” derive the local justification condition. *
   (We reuse pick_ask_None_all_false and find_feasible_None_forall from
    MUDA/Matching instead of redefining them here.)                      *)
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

(* A small convenience equivalence for using match_step in proofs. *)
Lemma match_step_None_iff :
  forall s, match_step s = None <->
            find_feasible (bids s) (asks s) (matches s) = None.
Proof.
  intro s. unfold match_step.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a]|] eqn:Hf;
    split; intro H; try reflexivity; try discriminate.
Qed.

Theorem rejection_fairness_from_None :
  forall s, match_step s = None -> rejection_justified_prop s.
Proof.
  intros s Hms.
  apply match_step_None_iff in Hms.
  eapply no_feasible_pairs_gives_justification; eauto.
Qed.

(* Phase-flavored wrapper if you use it after P4/P5/P6/P7. *)
Theorem rejection_fairness :
  forall s,
    (phase s = P4 \/ phase s = P5 \/ phase s = P6 \/ phase s = P7) ->
    find_feasible (bids s) (asks s) (matches s) = None ->
    rejection_justified_prop s.
Proof.
  intros s _ Hnone.
  eapply no_feasible_pairs_gives_justification; eauto.
Qed.

(* Note: No global axioms about rejection justification. Constructive facts
  are provided above (rejection_fairness_from_None and rejection_fairness). *)
