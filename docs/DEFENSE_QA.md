# Defense Q&A (Draft)

## Contributions and scope

**Q1. What is the main contribution of this thesis?**
A. A deterministic, phase-based STS formalization of MUDA suitable for temporal reasoning, plus mechanized proofs (Rocq) that six execution-level fairness properties hold on all induced infinite traces.

**Q2. What exactly is being verified (and what isn’t)?**
A. Verified: fairness properties over protocol executions (priority, quantity, uniform price, finality, maximality, justified rejection). Not verified: incentive properties like truthfulness/IC, equilibrium behavior, collusion resistance, or multi-round market dynamics.

**Q3. Why do you need temporal logic at all? Why not just prove post-conditions?**
A. Several fairness properties are inherently *trace* properties (e.g., “every matching step respects priority” and “after matching terminates, no feasible pair exists”). LTL expresses invariants (`G`) and boundary/settlement behaviors cleanly.

## Modeling choices

**Q4. Why model MUDA as a deterministic STS?**
A. Determinism gives each initial state a unique execution trace, which simplifies semantics and allows fairness theorems to quantify over all executions without branching.

**Q5. Why extend finite executions to infinite traces by stuttering?**
A. LTL semantics is defined on infinite traces. The protocol naturally terminates; stuttering at P7 preserves the “completed execution” forever. The fairness properties are expressed so that stuttering does not introduce violations.

**Q6. How do you represent fairness predicates as atomic propositions?**
A. State-level predicates (like `no_feasible`, price bounds, “match record unchanged”, etc.) are interpreted as atoms through a fixed mapping in `Fairness/Interpretation.v`.

## Proof strategy

**Q7. What is the recurring proof pattern for fairness theorems?**
A. Prove a state-level invariant/boundary lemma in MUDA semantics, then lift it to an LTL satisfaction statement over the induced trace (`mu_trace`) using the atom interpretation.

**Q8. Why are there axioms in the development? Doesn’t that weaken the result?**
A. The axioms are explicit and scoped (sorting correctness + greedy respects priority). They isolate standard algorithmic facts so the verification effort focuses on the novel temporal fairness layer. The fairness theorems are conditional on these assumptions, and the repo documents them in `README.md`.

**Q9. Are there any admitted lemmas?**
A. No. The build scripts include a check that reports `Admitted.` occurrences; fairness proofs close with `Qed`.

## Fairness properties

**Q10. What is Priority Fairness in one sentence?**
A. At each matching step, the chosen buyer is the highest-priority buyer that can trade, and the chosen seller is the highest-priority feasible seller for that buyer.

**Q11. What is Quantity Fairness in one sentence?**
A. Residual quantities are consistent with allocations; trades never allocate more than the submitted quantities.

**Q12. What is Price Fairness in one sentence?**
A. When a clearing price exists, it is computed by the uniform-price rule from the marginal pair and lies between the marginal ask and marginal bid.

**Q13. What is Match Finality?**
A. Once matching ends, the match record is never modified in later phases.

**Q14. What is Maximality?**
A. After the protocol enters settlement/post-match phases, there are no feasible buyer–seller pairs remaining.

**Q15. What is Justified Rejection?**
A. Any agent that is rejected at the end lacks a feasible trading partner at the post-matching boundary.

## Limitations / future work

**Q16. What would you do next to strengthen the mechanization?**
A. Replace sorting/priority axioms with verified library proofs (e.g., using verified sorting over lists) and extend the STS to controlled nondeterminism to model alternative tie-breaking or asynchronous arrivals.
