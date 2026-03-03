(* Fairness/Interpretation.v *)
From Stdlib Require Import List Bool PeanoNat.
From LTL  Require Import Syntax Semantics.
From MUDA Require Import State Transitions Atoms.

Local Open Scope LTL_scope.
Local Open Scope bool_scope.  

Definition p_allocOK      : predicate := 0.
Definition p_terminal     : predicate := 1.
Definition p_no_feasible  : predicate := 2.
Definition p_has_cprice   : predicate := 3.
Definition p_bounds_cstar : predicate := 4.
Definition p_match_keep   : predicate := 5.
Definition p_prioB_step   : predicate := 6.
Definition p_prioS_step   : predicate := 7.
Definition p_rejection_justified : predicate := 8.
Definition p_price_rule         : predicate := 9.

(* Chapter 4 match-finality atom: matches are stable after matching ends. *)
Definition p_match_final : predicate := 10.

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
    | 1 => phase s = P7
    | 2 => no_feasible_prop s
    | 3 => has_clearing_price_prop s
    | 4 => bounds_cstar_prop s
    | 5 => match_keep_prop s
    | 6 => priorityB_step_ok_prop s
    | 7 => priorityS_step_ok_prop s
  | 8 => rejection_justified_prop s
    | 9 => price_rule_prop s
    | 10 => match_final_prop s
    | p' =>
        (* decode phase atoms *)
        if andb (Nat.leb (p_phase 1) p') (Nat.leb p' (p_phase 7)) then
          let i := (p' - 10)%nat in phase s = nth_phase i
        else False
    end.

CoFixpoint mu_trace (s : State) : trace :=
  Trace (interp_atom s)
        (match phase s with
         | P7 => mu_trace (step s)   (* still advance execute; avoid self-loop for lemma *)
         | _  => mu_trace (step s)
         end).

Lemma mu_trace_at_execute : forall s n,
  trace_at (mu_trace s) n = interp_atom (execute n s).
Proof.
  intros s n.
  revert s.
  induction n as [|n IH]; intros s; simpl.
  - reflexivity.
  - destruct (phase s) eqn:Hp; simpl; apply IH.
Qed.

Lemma mu_trace_atom_at_execute :
  forall s i p,
    satisfies (mu_trace s) i (Atom p) <-> interp_atom (execute i s) p.
Proof.
  intros s i p; split.
  - (* → *)
    unfold satisfies; revert s p.
    induction i as [|i IH]; intros s p; simpl.
    + intros H; exact H.
    + destruct (phase s); simpl; auto.
  - (* ← *)
    unfold satisfies; revert s p.
    induction i as [|i IH]; intros s p; simpl.
    + intros H; exact H.
    + destruct (phase s); simpl; auto.
Qed.
