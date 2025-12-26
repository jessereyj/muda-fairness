(* Fairness/BridgeExample.v — demonstration of using provable_implies_valid *)
From Fairness Require Import All.

Local Open Scope LTL_scope.

Lemma example_bridge : forall φ, Provable φ -> valid φ.
Proof.
  intros φ Hprov.
  apply provable_implies_valid; exact Hprov.
Qed.
