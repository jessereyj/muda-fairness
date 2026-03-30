(** Chapter 4 (MUDA Protocol Layer) — Section 4.1.3 / 4.2 (Traces + Atomic Predicates)

    This file bridges MUDA executions (Chapter 3, deterministic `step`) to LTL
    trace semantics (Chapter 4):

    - Defines a fixed numbering of MUDA-specific atomic propositions `p_*`.
    - Defines `interp_atom : State -> predicate -> Prop`.
    - Defines the infinite trace `mu_trace` by iterating `step` and relying on
      terminal stuttering (P7 is a fixed point of `step`).

    Chapter 4 symbols and notation (bridge to code)
    ------------------------------------------------

    MUDA execution (Chapter 3):
      x0, x1, x2, ...  where  xi+1 = δ(xi)

    LTL trace (Chapter 4):
      σ = (v0, v1, v2, ...)
      where each vi assigns truth values to atomic propositions.

    In this development:
      - `mu_trace x0` is the infinite trace σ induced by repeatedly applying
        `step` (deterministic transition), with terminal stuttering at P7.
      - `trace_at (mu_trace x0) i` is the valuation vi.
      - `interp_atom x` is the valuation [[x]] : PROP -> Prop.

    Chapter 4 state-level atomic predicates are available (math notation):
      - matched(b, s, q, x)   (match record membership)
      - residualB(b, x) = r   (buyer residual)
      - residualS(s, x) = r   (seller residual)
      - price(x) = c          (clearing price)
      - feasible(b, s, x)     (price bound + positive residuals)
    These are defined in MUDA/State.v as:
      - `matched`    (match record membership)
      - `residualB`  (buyer residual)
      - `residualS`  (seller residual)
      - `price_at`   (clearing price equality)
      - `feasible`   (feasibility predicate)

    Fairness proofs in this repo evaluate a fixed set of *named* predicates
    (indexed as naturals) via `interp_atom`:
      p_allocOK      : quantity accounting predicate (Chapter 4 φ_qty)
      p_prioB_step   : buyer-side priority step predicate (part of Chapter 4 φ_prio)
      p_prioS_step   : seller-side priority step predicate (part of Chapter 4 φ_prio)
      p_has_cprice   : clearing price exists
      p_bounds_cstar : clearing price bounded by marginal pair
      p_price_rule   : clearing price follows protocol rule
*)
From Stdlib Require Import List Bool PeanoNat.
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

Lemma interp_atom_phase_4 : forall s, interp_atom s (p_phase 4) <-> phase s = P4.
Proof.
  intro s. unfold interp_atom, p_phase, nth_phase. simpl. tauto.
Qed.

Lemma interp_atom_phase_5 : forall s, interp_atom s (p_phase 5) <-> phase s = P5.
Proof.
  intro s. unfold interp_atom, p_phase, nth_phase. simpl. tauto.
Qed.

Lemma interp_atom_phase_6 : forall s, interp_atom s (p_phase 6) <-> phase s = P6.
Proof.
  intro s. unfold interp_atom, p_phase, nth_phase. simpl. tauto.
Qed.

Lemma interp_atom_phase_7 : forall s, interp_atom s (p_phase 7) <-> phase s = P7.
Proof.
  intro s. unfold interp_atom, p_phase, nth_phase. simpl. tauto.
Qed.

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
