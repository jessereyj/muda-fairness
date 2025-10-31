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

(** ** 1. Atomic predicate interpretation *)

(* Each predicate index corresponds to one state-local property.
   These numbers match the table in Section 4.2.4 of your thesis. *)
Definition interp (s : State) (p : predicate) : Prop :=
  match p with
  | 0 => allocOK s
  | 1 => phase s = P7
  | 2 => forall b a, In b (bids s) -> In a (asks s) ->
                     is_feasible b a (matches s) = false
  | 3 => forall b1 b2 a,
          In b1 (bids s) -> In b2 (bids s) -> In a (asks s) ->
          prioB b1 b2 = true ->
          is_feasible b1 a (matches s) = true ->
          ~ In (create_match b2 a (matches s)) (matches s)
  | 4 => forall a1 a2 b,
          In a1 (asks s) -> In a2 (asks s) -> In b (bids s) ->
          prioS a1 a2 = true ->
          is_feasible b a1 (matches s) = true ->
          ~ In (create_match b a2 (matches s)) (matches s)
  | 5 => forall m, In m (matches s) ->
          forall s', step s = s' ->
          In m (matches s')                 (* match finality *)
  | 6 => forall x, (exists b, x = buyer b) \/ (exists a, x = seller a) ->
          (* rejected if unallocated remainder *)
          (exists b, In b (bids s) /\ allocated_bid b (matches s) < quantity b) \/
          (exists a, In a (asks s) /\ allocated_ask a (matches s) < ask_quantity a)
  | 7 => forall x,
          (forall y, (In y (asks s) \/ In y (bids s)) ->
                     is_feasible (buyer x) (seller y) (matches s) = false)
  | _ => False
  end.

(** ** 2. Encode a MUDA state as an LTL valuation. *)

Definition encode (s : State) : state := fun p => interp s p.

(** ** 3. Stuttering ω-run construction. *)

CoFixpoint stutter_from (s : State) : trace :=
  Trace (encode s)
        (if phase s =? P7
         then stutter_from s          (* stay forever in terminal state *)
         else stutter_from (step s)).

(** ** 4. Helper lemmas used by Fairness layer. *)

Lemma encode_terminal_stable :
  forall s, phase s = P7 -> encode (step s) = encode s.
Proof.
  intros s Hterm. unfold encode, interp.
  f_equal. apply functional_extensionality. intro p.
  destruct p; simpl; try reflexivity.
  all: try rewrite Hterm; auto.
Qed.

Lemma stutter_from_unfold :
  forall s,
    stutter_from s =
    Trace (encode s)
          (if phase s =? P7 then stutter_from s
           else stutter_from (step s)).
Proof.
  reflexivity.  (* CoFixpoint definition unfolds directly *)
Qed.

(** ** 5. Export shorthand notations. *)

Notation "⟦ s ⟧" := (encode s) (at level 0).
Notation "σ_from s" := (stutter_from s) (at level 0).

#[export] Hint Resolve encode_terminal_stable : core.
