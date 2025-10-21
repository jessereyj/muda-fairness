(** * Linear Temporal Logic - Master Export
    
    Exports all LTL components.
*)

Require Export MUDA.LTL.Syntax.
Require Export MUDA.LTL.Semantics.
Require Export MUDA.LTL.Soundness.
Require Export MUDA.LTL.Completeness.

(** Meta-theorems are proven:
    - Soundness: provable -> valid
    - Completeness: valid -> provable
    - Consistency: follows from soundness
*)