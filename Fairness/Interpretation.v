(* Fairness/Interpretation.v *)
From Stdlib Require Import List.
From LTL  Require Import Syntax Semantics.
From MUDA Require Import State Transitions Atoms.

Local Open Scope LTL_scope.

(* Fixed indices for atoms used in Section 4 *)
Local Notation p_allocOK      := 0.
Local Notation p_terminal     := 1.
Local Notation p_no_feasible  := 2.
Local Notation p_has_cprice   := 3.
Local Notation p_bounds_cstar := 4.
Local Notation p_match_keep   := 5.
(* add more only when needed *)

Definition interp_atom (s : State) : predicate -> Prop :=
  fun p =>
    match p with
    | 0 => allocOK_prop s
    | 1 => phase s = P7
    | 2 => no_feasible_prop s
    | 3 => has_clearing_price_prop s
    | 4 => bounds_cstar_prop s
    | 5 => matches_monotone_1_prop s
    | _ => False
    end.

CoFixpoint mu_trace (s : State) : trace :=
  Trace (interp_atom s)
        (match phase s with
         | P7 => mu_trace s
         | _  => mu_trace (step s)
         end).
