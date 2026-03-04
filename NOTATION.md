# Notation Bridge: Thesis to Rocq Code

This document maps mathematical notation from the thesis (Chapters 3-4) to the corresponding Rocq/Coq definitions in the codebase.

## Chapter 3 Numbering Index

This section provides a stable cross-reference from Chapter 3 numbering (Structural Assumptions / Definitions / Propositions) to the corresponding Rocq symbols. The code uses descriptive identifiers (not numeric labels); the numeric labels are recorded here and in Coqdoc comments in the relevant `.v` files.

### Structural Assumptions (Chapter 3, Section 3.3)

1. **Order components remain constant**
  - Transitions never mutate `Bid`/`Ask` record fields; sorting only permutes lists.
  - See [MUDA/Sorting.v](MUDA/Sorting.v) (`sort_bids`, `sort_asks`, `do_sorting`) and [MUDA/Matching.v](MUDA/Matching.v) (`match_step`).

2. **Determinism (one successor)**
  - `delta` is modeled as a function `step : State -> State`.
  - See [MUDA/Transitions.v](MUDA/Transitions.v) (`step`).

3. **Terminal preservation**
  - If `phase = P7` then `step s = s`.
  - See [MUDA/Transitions.v](MUDA/Transitions.v) (`step`, `P7` branch).

### Definitions (Chapter 3)

1. **Feasibility**
  - [MUDA/State.v](MUDA/State.v) (`feasible_pair`), and boolean form [MUDA/Matching.v](MUDA/Matching.v) (`is_feasible`).

2. **Traded Unit Quantity**
  - [MUDA/Matching.v](MUDA/Matching.v) (`create_match` uses `Nat.min`).

3. **Priority Ordering**
  - [MUDA/Sorting.v](MUDA/Sorting.v) (`bid_priority`, `ask_priority`, `prioB`, `prioS`).

4. **Priority-Consistent Selection**
  - Encoded as priority-respecting axioms/predicates used in fairness:
    [MUDA/Atoms.v](MUDA/Atoms.v) (`greedy_respects_priority_bids`, `greedy_respects_priority_asks`, `priorityB_step_ok_prop`, `priorityS_step_ok_prop`).

5. **Unit Allocation**
  - [MUDA/State.v](MUDA/State.v) (`allocated_bid`, `allocated_ask`, plus residuals `residual_bid`, `residual_ask`).

6. **Greedy Matching Rule**
  - [MUDA/Matching.v](MUDA/Matching.v) (`find_feasible`, `match_step`).

7. **Match Monotonicity**
  - [MUDA/Matching.v](MUDA/Matching.v) (`match_step_monotonic`) and post-matching stability via [MUDA/Atoms.v](MUDA/Atoms.v) (`match_final_prop`).

8. **Last Marginal Pair**
  - [MUDA/ClearingPrice.v](MUDA/ClearingPrice.v) (`marginal_pair`).

9. **Uniform Clearing Price**
  - [MUDA/ClearingPrice.v](MUDA/ClearingPrice.v) (`determine_clearing_price`).

10. **Rejection at Termination**
  - [MUDA/Atoms.v](MUDA/Atoms.v) (`occurs_bid`, `occurs_ask`, `rejected_bid_prop`, `rejected_ask_prop`).

### Propositions (Chapter 3, Section 3.6)

1. **Residual Non-negativity**
  - Residuals are `nat`-valued: [MUDA/State.v](MUDA/State.v) (`residual_bid`, `residual_ask`).

2. **Conservation of Quantity in Phase P3**
  - Residuals are defined from allocation: [MUDA/State.v](MUDA/State.v) (`residual_* = initial - allocated_*`).

3. **Halting Condition of Phase P3**
  - Matching stops when no feasible pair is found: [MUDA/Matching.v](MUDA/Matching.v) (`find_feasible`, `find_feasible_None_forall`).

4. **Transition from P3 to P4**
  - Implemented in [MUDA/Transitions.v](MUDA/Transitions.v) (`step` uses `finish_matching` when `match_step` returns `None`).

5. **Clearing Price Stability After Matching**
  - Computed in P4 and preserved in later phases by `step`:
    [MUDA/ClearingPrice.v](MUDA/ClearingPrice.v) (`do_clearing_price`), [MUDA/Transitions.v](MUDA/Transitions.v) (`step` cases for P5–P7).

6. **Clearing Price Boundedness**
  - Proved as [MUDA/ClearingPrice.v](MUDA/ClearingPrice.v) (`clearing_price_bounds`).

7. **Justified Rejection at Termination**
  - Captured by [MUDA/Atoms.v](MUDA/Atoms.v) (`rejection_justified_prop`) and used in fairness proofs: [Fairness/JustifiedRejection.v](Fairness/JustifiedRejection.v).

## Chapter 4 Index

This section maps Chapter 4’s three-layer framework (foundation / MUDA trace interface / fairness verification) to the Rocq development.

### 4.1 Foundation Layer

4.1.1 **Syntax**
- Atomic proposition index set PROP = N: [LTL/Syntax.v](LTL/Syntax.v) (`predicate := nat`, `LTL_formula`, `X`, `U`, and abbreviations `F`, `G`).

4.1.2 **Semantics**
- Infinite traces and satisfaction: [LTL/Semantics.v](LTL/Semantics.v) (`trace`, `trace_at`, `satisfies`, `models`, `valid`).
- Lemma 1 (Semantics of F and G): [LTL/Semantics.v](LTL/Semantics.v) (`satisfies_eventually_unfold`, `satisfies_always_unfold`).

4.1.4 **Axiomatic System**
- Hilbert-style calculus (A0–A3, MP, necessitation restricted to tautologies): [LTL/Axioms.v](LTL/Axioms.v) (`Provable`, `Ax1`, `Ax2`, `Ax3`).

4.1.5 **Meta-theoretic properties**
- Soundness (Theorem 2): [LTL/Soundness.v](LTL/Soundness.v) (`soundness`).
- Weak completeness / adequacy / consistency (Theorems 3–4, Corollary 1): [LTL/Completeness.v](LTL/Completeness.v) (`WeakCompleteness`, `Adequacy`, `Consistency`).

### 4.2 MUDA Protocol Layer (Traces + Atomic Propositions)

- Determinism (unique trace from an initial state): Chapter 3 `step : State -> State` used coinductively (by construction) in [MUDA/Transitions.v](MUDA/Transitions.v) (`step`).
- Stuttering after termination (P7 fixed point): [MUDA/Transitions.v](MUDA/Transitions.v) (`step`, `P7 => s`).
- MUDA execution as infinite valuation trace: [Fairness/Interpretation.v](Fairness/Interpretation.v) (`interp_atom`, `mu_trace`).
- Trace identification lemma (link to i-fold execution): [Fairness/Interpretation.v](Fairness/Interpretation.v) (`mu_trace_at_execute`, `mu_trace_atom_at_execute`).

### 4.3 Fairness Verification Layer (Atoms + LTL Theorems)

- MUDA predicates as atoms (allocOK, no_feasible, has_cprice, bounds, etc.): [MUDA/Atoms.v](MUDA/Atoms.v) (state-level predicates) + [Fairness/Interpretation.v](Fairness/Interpretation.v) (atom numbering and interpretation).
- Fairness LTL formulas and mechanically-checked proofs:
  - [Fairness/PriorityFairness.v](Fairness/PriorityFairness.v)
  - [Fairness/QuantityFairness.v](Fairness/QuantityFairness.v)
  - [Fairness/PriceFairness.v](Fairness/PriceFairness.v)
  - [Fairness/MatchFinality.v](Fairness/MatchFinality.v)
  - [Fairness/Maximality.v](Fairness/Maximality.v)
  - [Fairness/JustifiedRejection.v](Fairness/JustifiedRejection.v)

## Core Data Types

### Agents (Implementation Detail)

**Code:** `MUDA/Types.v`
```coq
Inductive AgentType := Buyer | Seller.
Record Agent := { agent_id : nat; agent_type : AgentType }.
```

**Thesis:** Not explicitly modeled—agents are implicit in bid/ask ownership.

**Note:** The `Agent` type enables tracking ownership and partitioning bids/asks by participant. This is an implementation refinement that doesn't affect the protocol logic described in the thesis.

---

### Bids

**Thesis Notation (Chapter 3):**
```
bi = (pi, q⁰ᵢ, ti)
```
- `pi` = limit price
- `q⁰ᵢ` = initial quantity
- `ti` = arrival timestamp

**Code:** `MUDA/Types.v`
```coq
Record Bid := {
  bid_id : nat;        (* Unique identifier *)
  buyer : Agent;       (* Ownership/traceability *)
  price : nat;         (* = pi *)
  quantity : nat;      (* = q⁰ᵢ *)
  ts : nat             (* = ti *)
}.
```

**Mapping:**
- Thesis `pi` ↔ Code `price`
- Thesis `q⁰ᵢ` ↔ Code `quantity`
- Thesis `ti` ↔ Code `ts`
- Code `bid_id` and `buyer` are bookkeeping fields not shown in thesis notation

---

### Asks

**Thesis Notation (Chapter 3):**
```
sj = (aj, q⁰ⱼ, tj)
```
- `aj` = ask price
- `q⁰ⱼ` = initial quantity
- `tj` = arrival timestamp

**Code:** `MUDA/Types.v`
```coq
Record Ask := {
  ask_id : nat;         (* Unique identifier *)
  seller : Agent;       (* Ownership/traceability *)
  ask_price : nat;      (* = aj *)
  ask_quantity : nat;   (* = q⁰ⱼ *)
  ask_ts : nat          (* = tj *)
}.
```

**Mapping:**
- Thesis `aj` ↔ Code `ask_price`
- Thesis `q⁰ⱼ` ↔ Code `ask_quantity`
- Thesis `tj` ↔ Code `ask_ts`
- Code `ask_id` and `seller` are bookkeeping fields

---

### Matches

**Thesis Notation (Chapter 3, Definition 6):**
```
m = (b, s, q)
```
- `b` = matched bid
- `s` = matched ask
- `q` = matched quantity

**Code:** `MUDA/Types.v`
```coq
Record Match := {
  matched_bid : Bid;
  matched_ask : Ask;
  match_quantity : nat
}.
```

**Mapping:** Direct correspondence, but note that `b` and `s` are full `Bid` and `Ask` records, not just identifiers.

---

## State Representation

**Thesis Notation (Chapter 3, Section 3.2):**
```
x = (B, S, orders, residuals, M, p*, phase)
```
- `B` = set of bids
- `S` = set of asks
- `orders` = combined orders
- `residuals` = remaining quantities
- `M` = set of matches
- `p*` = clearing price
- `phase` = current phase

**Code:** `MUDA/State.v`
```coq
Inductive Phase := P1 | P2 | P3 | P4 | P5 | P6 | P7.

Record State := {
  bids : list Bid;              (* = B *)
  asks : list Ask;              (* = S *)
  matches : list Match;         (* = M *)
  clearing_price : option nat;  (* = p* *)
  phase : Phase
}.
```

**Mapping:**
- Thesis `B` ↔ Code `bids`
- Thesis `S` ↔ Code `asks`
- Thesis `M` ↔ Code `matches`
- Thesis `p*` ↔ Code `clearing_price`
- Thesis `orders` ↔ Code derives from `bids` and `asks`
- Thesis `residuals` ↔ Code **computed dynamically** (see Allocation Functions below)

**Key Difference:** The thesis presents `residuals` as a state component, but the code computes residuals on-the-fly from matches and initial quantities. This avoids redundancy and potential inconsistency.

---

## Allocation and Residuals

**Thesis (Chapter 3, Definition 5):**
```
allocB(m, b) = Σ{q | (b, s, q) ∈ m}
allocS(m, s) = Σ{q | (b, s, q) ∈ m}
```

**Code:** `MUDA/State.v`
```coq
Fixpoint allocated_bid (b : Bid) (ms : list Match) : nat :=
  match ms with
  | [] => 0
  | m :: ms' =>
      if bid_eq_dec (matched_bid m) b
      then match_quantity m + allocated_bid b ms'
      else allocated_bid b ms'
  end.

Fixpoint allocated_ask (a : Ask) (ms : list Match) : nat :=
  match ms with
  | [] => 0
  | m :: ms' =>
      if ask_eq_dec (matched_ask m) a
      then match_quantity m + allocated_ask a ms'
      else allocated_ask a ms'
  end.

Definition residual_bid (b : Bid) (ms : list Match) : nat :=
  quantity b - allocated_bid b ms.

Definition residual_ask (a : Ask) (ms : list Match) : nat :=
  ask_quantity a - allocated_ask a ms.
```

**Mapping:**
- Thesis `allocB(m, b)` ↔ Code `allocated_bid b ms`
- Thesis `allocS(m, s)` ↔ Code `allocated_ask a ms`
- Thesis residuals (implicit: `q⁰ - alloc`) ↔ Code `residual_bid` and `residual_ask`

**Note:** The thesis uses set notation `{q | ...}`, while the code uses structural recursion over lists with decidable equality.

---

## Feasibility

**Thesis (Chapter 3):**
```
feasible(b, s) ⟺ price(b) ≥ ask_price(s) ∧ residual(b) > 0 ∧ residual(s) > 0
```

**Code:** `MUDA/State.v`
```coq
Definition feasible_pair (b:Bid) (a:Ask) (ms:list Match) : Prop :=
  price b >= ask_price a
  /\ residual_bid b ms > 0
  /\ residual_ask a ms > 0.
```

**Mapping:** Direct correspondence.

---

## Clearing Price

**Thesis (Chapter 3, Definition 9):**
- Marginal pair `(b*, s*)` is the last match in `M`
- Clearing price `p*` determined by residuals of marginal pair

**Code:** `MUDA/ClearingPrice.v`
```coq
Definition marginal_pair (s : State) : option (Bid * Ask) :=
  match rev (matches s) with
  | [] => None
  | m :: _ => Some (matched_bid m, matched_ask m)
  end.

Definition determine_clearing_price (s : State) : option nat :=
  match marginal_pair s with
  | None => None
  | Some (b, a) =>
      if (residual_ask a (matches s) =? 0)
      then Some (ask_price a)
      else Some (price b)
  end.
```

**Mapping:**
- Thesis "last match" ↔ Code `rev (matches s)` and pattern match on head
- Thesis clearing-price rule ↔ Code test on marginal seller exhaustion (`residual_ask = 0`)
- Thesis uses append semantics (matches grow at tail) ↔ Code `rev` retrieves last element

---

## Rejection

**Thesis (Chapter 3, Definition 10):**
- An agent is rejected at termination iff it does not appear in the final match record.

**Code:** `MUDA/Atoms.v`
```coq
Definition occurs_bid (b : Bid) (ms : list Match) : Prop :=
  exists m, In m ms /\ matched_bid m = b.

Definition occurs_ask (a : Ask) (ms : list Match) : Prop :=
  exists m, In m ms /\ matched_ask m = a.

Definition rejected_bid_prop (b : Bid) (s : State) : Prop :=
  In b (bids s) /\ ~ occurs_bid b (matches s).

Definition rejected_ask_prop (a : Ask) (s : State) : Prop :=
  In a (asks s) /\ ~ occurs_ask a (matches s).
```

**Mapping:**
- Thesis “appears in final match record” ↔ Code `occurs_bid` / `occurs_ask` over `matches`
- Thesis “rejected” ↔ Code `rejected_bid_prop` / `rejected_ask_prop`

---

## Temporal Semantics

**Thesis (Chapter 4, Section 4.3):**
- Omega-run: `ω = x₀x₁x₂...`
- Stuttering after terminal state

**Code:** `Fairness/Interpretation.v`
```coq
CoFixpoint mu_trace (s : State) : trace :=
  Trace (interp_atom s)
        (match phase s with
         | P7 => mu_trace (step s)
         | _  => mu_trace (step s)
         end).
```

**Mapping:**
- Thesis `ω` ↔ Code `mu_trace s` (coinductive trace)
- Thesis stuttering (implicit in `x₇ = x₈ = ...`) ↔ Code `step` becomes identity at `P7`
- Thesis “xhalt” intuition (“post-matching forever”) ↔ Code guard `phase_ge_4` (phases `P4`–`P7`)

**Note:** Coq's `CoFixpoint` mechanizes infinite traces. The thesis describes this conceptually without implementation syntax.

---

## LTL Atoms

**Thesis (Chapter 4):** Atomic predicates like `allocOK`, `phase = k`, `has_cprice`, etc.

**Code:** `MUDA/Atoms.v` and `Fairness/Interpretation.v`
```coq
Definition allocOK_prop (s : State) : Prop := ...
Definition no_feasible_prop (s : State) : Prop := ...
Definition has_clearing_price_prop (s : State) : Prop := ...
(* etc. *)

Definition interp_atom (s : State) (p : predicate) : Prop :=
  match p with
  | 0 => allocOK_prop s
  | 1 => phase s = P7
  | 2 => no_feasible_prop s
  | 3 => has_clearing_price_prop s
  | 4 => bounds_cstar_prop s
  | 5 => match_keep_prop s
  | 6 => priorityB_step_ok_prop s
  | 7 => priorityS_step_ok_prop s
  | 8 => rejection_justified_prop s
  | 9 => price_rule_prop s
  (* phase atoms p_phase(k) are encoded separately *)
  end.
```

**Mapping:** Thesis uses informal predicates; code defines them as computable `Prop` values and maps them to LTL predicates via a numbered encoding.

---

## Summary of Abstraction Choices

| Aspect | Thesis Presentation | Code Implementation | Rationale |
|--------|---------------------|---------------------|-----------|
| Agent ownership | Implicit | Explicit `Agent` type | Traceability and partitioning |
| Bid/Ask fields | 3-tuple | 5-field record | Unique IDs and ownership |
| State residuals | Explicit component | Computed functions | Avoid redundancy, ensure consistency |
| Allocation sum | Set notation | Recursive function | Decidable, constructive |
| Trace construction | Conceptual ω-run | `CoFixpoint` | Mechanized coinduction |
| Match list | Abstract set `M` | `list Match` with append | Executable, provable monotonicity |
| Rejection | Non-occurrence in `M_fin` | `occurs_*` over `matches` | Matches Chapter 3 definition |

These choices are **standard practice in formal verification**: the thesis emphasizes mathematical clarity and essential logic, while the code provides a mechanically checkable implementation with necessary bookkeeping. The correctness of the formalization depends on faithful implementation of the thesis's core definitions (matching, feasibility, clearing price), which has been achieved.
