(** * MUDA/Atoms.v
    Bridge from MUDA operational semantics (Section 3)
    to LTL valuation semantics (Section 4.2.4).  *)

From Stdlib Require Import Arith List Bool.
Import ListNotations.

From LTL   Require Import Syntax Semantics.
From MUDA  Require Import Eqb Types State Sorting Matching ClearingPrice Transitions.

Local Open Scope LTL_scope.
Local Open Scope bool_scope.
Local Open Scope nat_scope.

(** ** 1. Useful state predicates (Section 3) *)

(* No feasible bid-ask pair remains *)
Definition no_feasible (s : State) : Prop :=
  forall b a, In b (bids s) -> In a (asks s) ->
              is_feasible b a (matches s) = false.

(* Clearing price is defined *)
Definition has_clearing_price (s : State) : Prop :=
  exists c, determine_clearing_price s = Some c.

(* Clearing price is within marginal bounds (when defined) *)
Definition bounds_cstar (s : State) : Prop :=
  match marginal_pair s, determine_clearing_price s with
  | Some (b,a), Some c => ask_price a <= c /\ c <= price b
  | _, _ => True
  end.

(* Match finality as a one-step property: existing matches persist after one step *)
Definition matches_monotone_1 (s : State) : Prop :=
  forall m, In m (matches s) -> In m (matches (step s)).

(** ** 2. Atomic predicate interpretation (Section 4.2.4) *)

(* Keep indices small and focused; extend only when the corresponding proofs are ready. *)
Definition interp (s : State) (p : predicate) : Prop :=
  match p with
  | 0 => allocOK s                                (* allocation bounds *)
  | 1 => phase s = P7                             (* terminal *)
  | 2 => no_feasible s                            (* no feasible pair remains *)
  | 3 => has_clearing_price s                     (* clearing price defined *)
  | 4 => bounds_cstar s                           (* clearing price within marginal bounds *)
  | 5 => matches_monotone_1 s                     (* match finality (one step) *)
  | _ => False
  end.

(** ** 3. Encode a MUDA state as an LTL valuation. *)

Definition encode (s : State) : state := fun p => interp s p.

(** ** 4. Stuttering ω-run construction. *)

CoFixpoint stutter_from (s : State) : trace :=
  Trace (encode s)
        (match phase s with
         | P7 => stutter_from s          (* stay forever in terminal state *)
         | _  => stutter_from (step s)
         end).

(** ** 5. Helper lemmas used by the fairness layer. *)

Lemma encode_terminal_stable :
  forall s, phase s = P7 -> encode (step s) = encode s.
Proof.
  intros s Hterm.
  unfold encode.
  (* In Transitions.step, P7 -> s. *)
  assert (step s = s) as ->.
  { unfold step. now rewrite Hterm. }
  reflexivity.
Qed.

(** ** 6. Notations *)
Notation "⟦ s ⟧" := (encode s) (at level 0).
