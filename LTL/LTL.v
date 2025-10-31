(* LTL/LTL.v — master export for the LTL layer *)

(* Export all core LTL modules *)
From LTL Require Export Syntax Semantics Axioms Soundness Completeness.

(* Convenience: import notation and scopes from Syntax *)
Local Open Scope LTL_scope.

(* Key metatheoretical properties for client code:

   1. Soundness (from Soundness.v):
      - If ⊢ φ then ⊨ φ  (derivable formulas are valid)

   2. WeakCompleteness (from Completeness.v):
      - If ⊨ φ then ⊢ φ  (valid formulas are derivable)
      - Assumed as an axiom to avoid canonical model construction

   3. Adequacy (from Completeness.v):
      - ⊢ φ if and only if ⊨ φ  (proof system captures validity)
      - Proven as a theorem from Soundness and WeakCompleteness
*)

(* Re-export key metatheorems for easier access *)
Export LTL.Completeness.