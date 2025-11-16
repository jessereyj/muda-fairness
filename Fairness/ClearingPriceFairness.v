(* Fairness/ClearingPriceFairness.v *)
Require Import Stdlib.List Stdlib.Nat.
Require Import LTL.Syntax.
Require Import LTL.Semantics.
Require Import MUDA.Types MUDA.State MUDA.Matching MUDA.ClearingPrice MUDA.Transitions MUDA.Atoms.
Require Import Fairness.Interpretation.

Local Open Scope LTL_scope.

(* Uniform clearing price fairness: bounds between marginal ask/bid whenever defined. *)
Definition uniformPriceOK : LTL_formula := G (Atom p_bounds_cstar).

Lemma bounds_cstar_prop_holds_all : forall s i,
  wf_state (execute i s) -> bounds_cstar_prop (execute i s).
Proof.
  intros s i Hwf. apply bounds_cstar_from_wf. exact Hwf.
Qed.

Lemma uniform_price_fairness_LTL_initial : forall bs as_list,
  satisfies (mu_trace (initial_state bs as_list)) 0 uniformPriceOK.
Proof.
  intros bs as_list.
  unfold uniformPriceOK.
  apply (proj2 (satisfies_always_unfold _ 0 _)).
  intro j.
  rewrite mu_trace_atom_at_execute.
  (* interp_atom maps p_bounds_cstar to bounds_cstar_prop *)
  unfold interp_atom.
  (* Case split on predicate index to reach p_bounds_cstar = 4 *)
  (* Simpler: change goal directly using function behavior. *)
  set (s := execute j (initial_state bs as_list)).
  change (bounds_cstar_prop s).
  apply bounds_cstar_from_wf.
  apply wf_state_execute_n.
  apply wf_state_initial.
Qed.
