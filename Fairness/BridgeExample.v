(* Fairness/BridgeExample.v — demonstration of using provable_implies_valid *)
From Fairness Require Import All.

Local Open Scope LTL_scope.

(* This example shows invoking the bridge lemma to convert an axiomatic derivation
   into semantic validity. It is intentionally generic to keep examples lightweight. *)
Lemma example_bridge : forall φ, Provable φ -> valid φ.
Proof.
  intros φ Hprov.
  (* Invoke the bridge lemma defined in Fairness/All.v *)
  apply provable_implies_valid; exact Hprov.
Qed.
