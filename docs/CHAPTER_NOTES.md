# Chapter Notes (Compressed)

These notes are meant as *study notes* that track the structure of the thesis while staying anchored to the verified Rocq development.

## Chapter 1 — Introduction (what matters technically)
- MUDA is batch, multi-unit, double-sided, uniform-price clearing.
- Fairness properties are execution-level, not just “final allocation correctness”.
- Need a state-based, phase-based model + temporal logic (LTL) to express “always/eventually/until” properties across the whole trace.

## Chapter 2 — Literature Review (positioning)
- Prior MUDA work focuses on economic properties (IR/IC/BB/AE), not state-based protocol traces.
- Prior formalizations in Coq focus on other auction types or correctness of final match, not temporal fairness over a full deterministic protocol.

## Chapter 3 — MUDA as a deterministic STS
Key modeling decisions:
- **State components** include bids/asks, match record, clearing price, phase.
- **Residual quantities** track remaining demand/supply; trades are partial fills via `min(residB, residS)`.
- **Seven phases (P1–P7)**: submission, sorting, matching, clearing price, finalization, bookkeeping, rejection.
- **Determinism**: `δ` is a function (one successor state).
- **Termination**: P7 is absorbing; execution is extended to an infinite trace by repeating the terminal state.

Operational definitions to memorize:
- Feasibility: price-crossing + positive residuals.
- Priority order: lexicographic price/time (buyers: higher price earlier; sellers: lower ask earlier).
- Greedy matching: choose highest-priority feasible buyer, then highest-priority feasible seller for that buyer, trade maximum feasible quantity.
- Marginal pair + uniform price rule: derived from the final trade and exhaustion condition.
- Rejection: agents not appearing in final match record.

## Chapter 4 — LTL + proof framework
Three-layer approach:
1. LTL foundation (syntax/semantics on infinite traces).
2. MUDA execution → infinite trace (stuttering after termination).
3. Fairness verification by state invariants / termination arguments lifted to LTL (`G`, `F`).

Proof pattern (high-level):
- Show a state-level predicate holds for all reachable states (invariant), then conclude `G atom`.
- Or show a witness state exists, then conclude `F atom`.

## Chapter 5–6 — Results/Discussion
- Scenarios illustrate that the operational semantics produce traces satisfying the fairness formulas.
- These scenarios are evidence/intuition; the proof in Rocq is the actual guarantee.

## Chapter 7 — Conclusion
- Fairness expressed temporally over the whole protocol execution is mechanizable.
- The deterministic STS + LTL approach scales as a methodology (future: nondeterminism / alternative priority / pricing rules).
