From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Matching Tactics.

Module Temporal.

  (* Runs: finite lists whose adjacent states follow [Step]. *)
  Inductive is_run : list State -> Prop :=
  | run_nil  : is_run []
  | run_one  : forall s, is_run [s]
  | run_cons : forall s1 s2 rest,
      Step s1 s2 ->
      is_run (s2 :: rest) ->
      is_run (s1 :: s2 :: rest).

  (* “Always P on adjacent pairs” over a list of states. *)
  Inductive G_pair (P: State -> State -> Prop) : list State -> Prop :=
  | G_nil  : G_pair P []
  | G_one  : forall s, G_pair P [s]
  | G_cons : forall s1 s2 rest,
      P s1 s2 ->
      G_pair P (s2 :: rest) ->
      G_pair P (s1 :: s2 :: rest).

  (* Finality as monotonicity of Mt across a single step. *)
  Definition finality_P (s1 s2:State) : Prop :=
    monotone_Mt (Mt s1) (Mt s2).

  Lemma finality_holds_on_step :
    forall s1 s2, Step s1 s2 -> finality_P s1 s2.
  Proof. intros; unfold finality_P; now apply step_monotone. Qed.

End Temporal.

Export Temporal.
