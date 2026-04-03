From Stdlib Require Import Bool PeanoNat.
From LTL  Require Import Syntax Semantics.
From MUDA Require Import State Transitions Atoms.

Local Open Scope LTL_scope.
Local Open Scope bool_scope.  

Definition p_allocOK      : predicate := 0.
Definition p_has_cprice   : predicate := 1.
Definition p_bounds_cstar : predicate := 2.
Definition p_price_rule   : predicate := 3.
Definition p_prioB_step   : predicate := 4.
Definition p_prioS_step   : predicate := 5.

Definition p_phase (i : nat) : predicate := (10 + i)%nat.

Definition nth_phase (i : nat) : Phase :=
  match i with
  | 1 => P1 | 2 => P2 | 3 => P3 | 4 => P4
  | 5 => P5 | 6 => P6 | _ => P7
  end.

Definition interp_atom (s : State) : predicate -> Prop :=
  fun p =>
    match p with
    | 0 => allocOK_prop s
    | 1 => has_clearing_price_prop s
    | 2 => bounds_cstar_prop s
    | 3 => price_rule_prop s
    | 4 => priorityB_step_ok_prop s
    | 5 => priorityS_step_ok_prop s
    | p' =>
        (* decode phase atoms *)
        if andb (Nat.leb (p_phase 1) p') (Nat.leb p' (p_phase 7)) then
          let i := (p' - 10)%nat in phase s = nth_phase i
        else False
    end.

CoFixpoint mu_trace (s : State) : trace :=
  Trace (interp_atom s) (mu_trace (δ s)).

(** Thesis-level alias: μ(x0) denotes the induced infinite trace. *)
Definition μ (s : State) : trace := mu_trace s.

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
