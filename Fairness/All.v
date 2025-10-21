Require Export MUDA.Fairness.QuantityFairness.
Require Export MUDA.Fairness.PriorityFairness.
Require Export MUDA.Fairness.Finality.
Require Export MUDA.Fairness.Maximality.
Require Export MUDA.Fairness.RejectionFairness.

(* Verified properties:
   1. Quantity Fairness: G(allocOK)
   2. Priority Fairness: one-step safety ⇒ “until” (paper §4.4.1)
   3. Match Finality: G(matched → G matched)
   4. Termination: F(terminal)  (via reaching P4)
   5. Rejection Fairness: G(terminal ∧ rejected → justified)
*)
