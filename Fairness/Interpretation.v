From Stdlib Require Import Bool PeanoNat.
From LTL  Require Import Syntax Semantics.
From MUDA Require Import State Transitions Atoms.

(** Panel index (thesis ↔ code)

  Chapter 4 (MUDA → LTL bridge)
  - p_*: predicate indices for the atomic propositions used in fairness specs
  - interp_atom: interpret predicate indices as state predicates
  - mu_trace / μ: induced infinite trace by iterating δ
  - mu_trace_atom_at_execute: lift bridge for atoms (trace time i ↔ execute i)
*)

Local Open Scope LTL_scope.
Local Open Scope bool_scope.  

(* p_allocOK: predicate index for allocOK_prop (quantity accounting). *)
Definition p_allocOK      : predicate := 0.
(* p_has_cprice: predicate index for “clearing price exists”. *)
Definition p_has_cprice   : predicate := 1.
(* p_bounds_pstar: predicate index for marginal-pair bounds on the clearing price pstar. *)
Definition p_bounds_pstar : predicate := 2.
(* p_price_rule: predicate index for the deterministic clearing-price rule. *)
Definition p_price_rule   : predicate := 3.
(* p_prioB_step: predicate index for the buyer-side priority-step atom. *)
Definition p_prioB_step   : predicate := 4.
(* p_prioS_step: predicate index for the seller-side priority-step atom. *)
Definition p_prioS_step   : predicate := 5.

(* p_phase: encoding of phase atoms p_phase(i) = 10+i. *)
Definition p_phase (i : nat) : predicate := (10 + i)%nat.

(* nth_phase: decode index i into the corresponding protocol phase. *)
Definition nth_phase (i : nat) : Phase :=
  match i with
  | 1 => P1 | 2 => P2 | 3 => P3 | 4 => P4
  | 5 => P5 | 6 => P6 | _ => P7
  end.

(* interp_atom: interpret predicate indices as concrete state propositions. *)
Definition interp_atom (s : State) : predicate -> Prop :=
  fun p =>
    match p with
    | 0 => allocOK_prop s
    | 1 => has_clearing_price_prop s
    | 2 => bounds_pstar_prop s
    | 3 => price_rule_prop s
    | 4 => priorityB_step_ok_prop s
    | 5 => priorityS_step_ok_prop s
    | p' =>
        (* decode phase atoms *)
        if andb (Nat.leb (p_phase 1) p') (Nat.leb p' (p_phase 7)) then
          let i := (p' - 10)%nat in phase s = nth_phase i
        else False
    end.

(* mu_trace: coinductively unfold the infinite trace induced by iterating δ. *)
CoFixpoint mu_trace (s : State) : trace :=
  Trace (interp_atom s) (mu_trace (δ s)).

(* μ: thesis-level alias for the induced infinite trace μ(x0) (Chapter 4). *)
Definition μ (s : State) : trace := mu_trace s.

(* Bridge lemma (Chapter 4 “lift step”): evaluating Atom p at time i on μ(s)
   coincides with evaluating p on the state reached by executing i steps. *)

(* mu_trace_atom_at_execute: bridge lemma (time i on μ(s) equals execute i on states). *)
Lemma mu_trace_atom_at_execute :
  forall s i p,
    satisfies (mu_trace s) i (Atom p) <-> interp_atom (execute i s) p.
Proof.
  intros s i p; split.
  - (* → *)
    unfold satisfies; revert s p.
    induction i as [|i IH]; intros s p; simpl.
    + intros H; exact H.
    + auto.
  - (* ← *)
    unfold satisfies; revert s p.
    induction i as [|i IH]; intros s p; simpl.
    + intros H; exact H.
    + auto.
Qed.
