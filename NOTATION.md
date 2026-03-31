# Notation Bridge: Thesis to Rocq Code

This document maps mathematical notation from the thesis (Chapters 3-4) to the corresponding Rocq/Coq definitions in the codebase.

## Chapter 3 Numbering Index

This section provides a stable cross-reference from Chapter 3 numbering (Definitions / Propositions / phase rules) to the corresponding Rocq symbols. The code uses descriptive identifiers (not numeric labels); the numeric labels are recorded here and in Coqdoc comments in the relevant `.v` files.

### Structural Properties (Chapter 3)

1. **Order components remain constant**
  - Transitions never mutate `Bid`/`Ask` record fields; sorting only permutes lists.
  - See [MUDA/Sorting.v](MUDA/Sorting.v) (`sort_bids`, `sort_asks`, `do_sorting`) and [MUDA/Matching.v](MUDA/Matching.v) (`match_step`).

2. **Determinism (one successor)**
  - `delta` is modeled as a function `step : State -> State`.
  - See [MUDA/Transitions.v](MUDA/Transitions.v) (`step`).

3. **Terminal state preservation**
  - If `phase = P7` then `step s = s`.
  - See [MUDA/Transitions.v](MUDA/Transitions.v) (`step`, `P7` branch).

### Definitions (Chapter 3)

1. **Feasibility**
  - [MUDA/State.v](MUDA/State.v) (`feasible_pair`), and boolean form [MUDA/Matching.v](MUDA/Matching.v) (`is_feasible`).
  - Executable feasibility in `is_feasible` checks: (i) `ask_price(a) <= price(b)` and (ii) both residual quantities are at least 1. The model allows an order to participate in multiple matches until its residual reaches 0 (Scenario 1 includes a bid matched in more than one round).

2. **Traded Unit Quantity**
  - [MUDA/Matching.v](MUDA/Matching.v) (`create_match` uses `Nat.min`).

3. **Priority Ordering**
  - [MUDA/Sorting.v](MUDA/Sorting.v) (`bid_priority`, `ask_priority`, `prioB`, `prioS`).

4. **Priority-Consistent Selection**
  - Encoded by the deterministic greedy selector in [MUDA/Matching.v](MUDA/Matching.v) (`find_feasible`, `best_feasible_ask`) and exposed as step-level predicates in [MUDA/Atoms.v](MUDA/Atoms.v) (`priorityB_step_ok_prop`, `priorityS_step_ok_prop`).

5. **Unit Allocation**
  - [MUDA/State.v](MUDA/State.v) (`allocated_bid`, `allocated_ask`, plus residuals `residual_bid`, `residual_ask`).

6. **Greedy Matching Rule**
  - [MUDA/Matching.v](MUDA/Matching.v) (`find_feasible`, `match_step`).

7. **Match Monotonicity**
  - The match record grows by appending at most one new match per successful matching round: [MUDA/Matching.v](MUDA/Matching.v) (`match_step` uses `matches s ++ [m]`).

8. **Last Marginal Pair**
  - [MUDA/ClearingPrice.v](MUDA/ClearingPrice.v) (`marginal_pair`).

9. **Uniform Clearing Price**
  - [MUDA/ClearingPrice.v](MUDA/ClearingPrice.v) (`determine_clearing_price`).

10. **Rejection at Termination**
  - Not mechanized in this repository snapshot (no rejection predicates/atoms are used by the Chapter 3–5 fairness verification layer).

### Propositions (Chapter 3, Section 3.6)

1. **Residual Non-negativity**
  - Residuals are `nat`-valued: [MUDA/State.v](MUDA/State.v) (`residual_bid`, `residual_ask`).

2. **Conservation of Quantity in Phase P3**
  - Residuals are defined from allocation: [MUDA/State.v](MUDA/State.v) (`residual_* = initial - allocated_*`).

3. **Halting Condition of Phase P3**
  - Matching stops when no feasible pair is found: [MUDA/Matching.v](MUDA/Matching.v) (`find_feasible`, `match_step`).

4. **Transition from P3 to P4**
  - Implemented in [MUDA/Transitions.v](MUDA/Transitions.v) (`step` uses `finish_matching` when `match_step` returns `None`).

5. **Clearing Price Stability After Matching**
  - Computed in P4 and preserved in later phases by `step`:
    [MUDA/ClearingPrice.v](MUDA/ClearingPrice.v) (`do_clearing_price`), [MUDA/Transitions.v](MUDA/Transitions.v) (`step` cases for P5–P7).

6. **Clearing Price Boundedness**
  - Proved as [MUDA/ClearingPrice.v](MUDA/ClearingPrice.v) (`clearing_price_bounds`).

7. **Justified Rejection at Termination**
  - Out of scope for the refactored Chapter 3–5 fairness layer (this repo version focuses on priority/quantity/price fairness only).

## Chapter 4 Index

This section maps Chapter 4’s three-layer framework (foundation / MUDA trace interface / fairness verification) to the Rocq development.

### 4.1 Foundation Layer

4.1.1 **Syntax**
- Atomic proposition index set PROP = N: [LTL/Syntax.v](LTL/Syntax.v) (`predicate := nat`, `LTL_formula`, `X`, `F`, `G`).
- Chapter 4 primitives are `¬`, `∧`, `X`, `F`, `G`. The code also provides `∨` and `→` as *derived connectives with standard semantics* (implemented as extra constructors) so fairness specs can be written in the same style as the thesis, without relying on classical logic.

4.1.2 **Semantics**
- Infinite traces and satisfaction: [LTL/Semantics.v](LTL/Semantics.v) (`trace`, `trace_at`, `satisfies`, `models`, `valid`).
- Lemma (Semantics of G / Always): [LTL/Semantics.v](LTL/Semantics.v) (`satisfies_always_unfold`).

**Note:** This repository version keeps the Chapter 4 *semantic* satisfaction layer only (syntax + semantics in [LTL/Syntax.v](LTL/Syntax.v) and [LTL/Semantics.v](LTL/Semantics.v)). It intentionally does not include a Hilbert-style proof system, soundness, or completeness development.

### 4.2 MUDA Protocol Layer (Traces + Atomic Propositions)

- Determinism (unique trace from an initial state): Chapter 3 `step : State -> State` used coinductively (by construction) in [MUDA/Transitions.v](MUDA/Transitions.v) (`step`).
- Stuttering after termination (P7 fixed point): [MUDA/Transitions.v](MUDA/Transitions.v) (`step`, `P7 => s`).
- MUDA execution as infinite valuation trace: [Fairness/Interpretation.v](Fairness/Interpretation.v) (`interp_atom`, `mu_trace`).
- Trace identification lemma (link to i-fold execution for atoms): [Fairness/Interpretation.v](Fairness/Interpretation.v) (`mu_trace_atom_at_execute`).

### 4.3 Fairness Verification Layer (Atoms + LTL Theorems)

- MUDA predicates as atoms (allocOK, has_cprice, bounds_cstar, price_rule, prioB_step_ok, prioS_step_ok): [MUDA/Atoms.v](MUDA/Atoms.v) (state-level predicates) + [Fairness/Interpretation.v](Fairness/Interpretation.v) (atom numbering and interpretation).
- Fairness LTL formulas and mechanically-checked proofs:
  - [Fairness/PriorityFairness.v](Fairness/PriorityFairness.v)
  - [Fairness/QuantityFairness.v](Fairness/QuantityFairness.v)
  - [Fairness/PriceFairness.v](Fairness/PriceFairness.v)

#### Chapter 4 Atomic Proposition Notation

The thesis presents atomic propositions using mathematical predicate notation.
In the Rocq development, these are state-level predicates derived from the MUDA
state components (orders, residuals, match record, clearing price).

- `matched(b, s, q)` — true iff `(b, s, q)` is in the match record:
  [MUDA/State.v](MUDA/State.v) (`matched`) over `matches`.
- `residualB(b) = r` — true iff buyer order `b` has residual `r`:
  [MUDA/State.v](MUDA/State.v) (`residualB`) defined via `residual_bid`.
- `residualS(s) = r` — true iff seller order `s` has residual `r`:
  [MUDA/State.v](MUDA/State.v) (`residualS`) defined via `residual_ask`.
- `price(x) = c` — true iff the clearing price stored in state `x` is `c`:
- `price(x) = c` — true iff the clearing price stored in state `x` is `Some c`:
  [MUDA/State.v](MUDA/State.v) (`clearing_price` field of `State`).
- `feasible(b, s)` — true iff `p(b) ≥ a(s)` and both residuals are positive:
  [MUDA/State.v](MUDA/State.v) (`feasible`) / `feasible_pair`.

The LTL layer then assigns truth values to a fixed set of *named* predicates
(e.g., priority step correctness, quantity allocation bounds, clearing price
bounds/rule) using [Fairness/Interpretation.v](Fairness/Interpretation.v)
(`interp_atom`, `mu_trace`).

## Core Data Types

### Agents (Implementation Detail)

**Code:** `MUDA/Types.v`
```coq
Inductive AgentType := Buyer | Seller.
Record Agent := { agent_id : nat; agent_type : AgentType }.
```

**Thesis:** Not explicitly modeled—agents are implicit in bid/ask ownership.

**Chapter 3 note (one order per agent):** The thesis states “Each agent submits exactly one order.”

- **Modeling choice:** this development represents the submitted orders as lists `bids : list Bid` and `asks : list Ask` inside the MUDA state.
- **What is enforced:** order *immutability* is enforced by transitions (orders are not mutated).
- **What is not enforced by the core model:** uniqueness (“one order per agent”) is not encoded as a global invariant; instead it is a property of the concrete inputs used in examples/scenarios.

**Note:** The `Agent` type enables tracking ownership and partitioning bids/asks by participant. This is an implementation refinement that doesn't affect the protocol logic described in the thesis.

---

## Order Immutability

**Thesis (Definition 3):** Once an order is submitted, its components remain unchanged throughout the execution trace.

**Code:** Transitions never mutate the contents of `Bid`/`Ask` records; the only Phase that changes order presentation is P2 sorting, which reorders the lists.

- Sorting step: [MUDA/Sorting.v](MUDA/Sorting.v) (`do_sorting`)
- Deterministic transition: [MUDA/Transitions.v](MUDA/Transitions.v) (`step`) preserves `bids`/`asks` outside of Phase P2

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

**Thesis (Chapter 3, Definition 10):**
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
      then Some (price b)
      else Some (ask_price a)
  end.
```

**Mapping:**
- Thesis "last match" ↔ Code `rev (matches s)` and pattern match on head
- Thesis clearing-price rule ↔ Code test on marginal seller exhaustion (`residual_ask = 0`)
- Thesis uses append semantics (matches grow at tail) ↔ Code `rev` retrieves last element

---

## Rejection (not mechanized in this repository snapshot)

**Thesis (Chapter 3, Definition 11):**
- An agent is rejected at termination iff it does not appear in the final match record.

**Repository scope note:**
This repository snapshot focuses on the Chapter 3–5 fairness layer (priority, quantity, uniform price). It does not include rejection predicates/atoms in `MUDA/Atoms.v`, and no mechanized fairness result in this repo depends on rejection.

---

## Temporal Semantics

**Thesis (Chapter 4, Section 4.3):**
- Infinite run: `omega = x0 x1 x2 ...`
- Stuttering after terminal state

**Code:** `Fairness/Interpretation.v`
```coq
CoFixpoint mu_trace (s : State) : trace :=
  Trace (interp_atom s) (mu_trace (step s)).
```

**Mapping:**
- Thesis `omega` ↔ Code `mu_trace s` (coinductive trace)
- Thesis stuttering (implicit in `x7 = x8 = ...`) ↔ Code `step` becomes identity at `P7`

**Note:** `mu_trace` always advances by `step`; terminal stuttering is ensured because `step s = s` when `phase s = P7`.

**Note:** Coq's `CoFixpoint` mechanizes infinite traces. The thesis describes this conceptually without implementation syntax.

---

## LTL Atoms

**Thesis (Chapter 4):** Atomic predicates like `allocOK`, `phase = k`, `has_cprice`, etc.

**Code:** `MUDA/Atoms.v` and `Fairness/Interpretation.v`
```coq
Definition allocOK_prop (s : State) : Prop := ...
Definition has_clearing_price_prop (s : State) : Prop := ...
(* etc. *)

Definition interp_atom (s : State) (p : predicate) : Prop :=
  match p with
  | 0 => allocOK_prop s
  | 1 => has_clearing_price_prop s
  | 2 => bounds_cstar_prop s
  | 3 => price_rule_prop s
  | 4 => priorityB_step_ok_prop s
  | 5 => priorityS_step_ok_prop s
  | p' =>
      (* phase atoms: p_phase(i) = 10+i, for i in {1..7} *)
      if andb (Nat.leb (10 + 1) p') (Nat.leb p' (10 + 7)) then
        let i := (p' - 10) in
        phase s =
          match i with
          | 1 => P1 | 2 => P2 | 3 => P3 | 4 => P4
          | 5 => P5 | 6 => P6 | _ => P7
          end
      else False
  end.
```

**Mapping:** Thesis uses informal predicates; code defines them as computable `Prop` values and maps them to LTL predicates via a numbered encoding. This repo version includes only the atoms needed for priority/quantity/price fairness.

---

## Chapter 5 (Scenario 1): Execution Index and Predicate Evaluation

This section rewrites the Chapter 5 "predicate evaluation" in terms of the *actual* state sequence used by the mechanization.

### Time index convention

In [Example/Scenario1.v](Example/Scenario1.v), the trace is defined as:

- `st0 := initial_state bs_s1 as_s1`
- `run_s1 := mu_trace st0`

The LTL semantics are aligned with the deterministic STS iteration:

- Time `t = 0` corresponds to state `st0`.
- Time `t = n` corresponds to `execute n st0`.

### Concrete execution checkpoints (Scenario 1)

The file [Example/Scenario1.v](Example/Scenario1.v) contains concrete checks that pin down when matches and the clearing price appear:

- `matches (execute 3 st0) = [m1]`
- `matches (execute 4 st0) = [m1; m2]`
- `matches (execute 5 st0) = [m1; m2; m3]`
- `phase (execute 6 st0) = P4`
- `phase (execute 7 st0) = P5` and `clearing_price (execute 7 st0) = Some 8`

For Chapter 5 prose, the key alignment point is:

- the clearing price is *computed* by the P4 pricing transition, but the state *that carries* `clearing_price = Some 8` is the next state (phase `P5`).

### Predicate evaluation (atoms)

The relevant atomic predicates are defined in [MUDA/Atoms.v](MUDA/Atoms.v) and mapped into LTL atoms by `interp_atom` in [Fairness/Interpretation.v](Fairness/Interpretation.v).

Below is the intended interpretation for Scenario 1 along the states `execute t st0` (time `t` in the LTL trace).

##### Time-index table (t = 0..7)

This table is written to match the concrete checks in [Example/Scenario1.v](Example/Scenario1.v). It uses:

- `|matches|` = length of the match record `matches (execute t st0)`
- `cprice_field` = the state field `clearing_price (execute t st0)`
- `has_cprice` = `has_clearing_price_prop (execute t st0)` (defined via `determine_clearing_price`, not the field)

| t | phase | |matches| | cprice_field | has_cprice |
|--:|:------|--------:|:------------|:----------|
| 0 | P1 | 0 | None | False |
| 1 | P2 | 0 | None | False |
| 2 | P3 | 0 | None | False |
| 3 | P3 | 1 | None | True |
| 4 | P3 | 2 | None | True |
| 5 | P3 | 3 | None | True |
| 6 | P4 | 3 | None | True |
| 7 | P5 | 3 | Some 8 | True |

Notes:

- The `t = 3,4,5` match record sizes are exactly those proven by `Scenario1_Matches_After_Round{1,2,3}`.
- The `t = 6` and `t = 7` phases are exactly those proven by `Scenario1_Enters_P4` and `Scenario1_Final_Phase_And_Price`.
- `has_cprice` becomes true at `t = 3` because from that point the match record is non-empty, so `marginal_pair` exists and `determine_clearing_price` is defined.

#### Phase atoms

The phase atoms are encoded as `p_phase(i) = 10 + i` for `i in {1..7}`.

At any time `t`, exactly one of these phase atoms is true, namely the one corresponding to `phase (execute t st0)`.

#### Named fairness atoms (indices 0..5)

These are the atoms used by the three fairness formulas (`priorityOK`, `quantityOK`, `priceOK`):

| Atom index | Name (informal) | Coq predicate (in MUDA/Atoms.v) | How it is used |
|-----------:|------------------|---------------------------------|----------------|
| 0 | allocOK | `allocOK_prop` | Quantity fairness: `G allocOK` |
| 1 | has_cprice | `has_clearing_price_prop` | Price fairness guard: `G(has_cprice -> ...)` |
| 2 | bounds_cstar | `bounds_cstar_prop` | Price fairness: marginal bounds when defined |
| 3 | price_rule | `price_rule_prop` | Price fairness: clearing price rule when applicable |
| 4 | prioB_step_ok | `priorityB_step_ok_prop` | Priority fairness: `G prioB_step_ok` |
| 5 | prioS_step_ok | `priorityS_step_ok_prop` | Priority fairness: `G prioS_step_ok` |

#### Scenario 1 truth summary (aligned to the mechanization)

- `allocOK_prop` holds at all times on `run_s1` (this is exactly `Scenario1_Quantity : satisfies run_s1 0 quantityOK`).
- `priorityB_step_ok_prop` and `priorityS_step_ok_prop` hold at all times on `run_s1` (this is exactly `Scenario1_Priority : satisfies run_s1 0 priorityOK`).
- `has_clearing_price_prop` becomes true once there is at least one match in the record, because it is defined using `determine_clearing_price` (which depends on `marginal_pair`, i.e. the last match). In Scenario 1, this is from time `t = 3` onward, because `matches (execute 3 st0) = [m1]`.
- `bounds_cstar_prop` and `price_rule_prop` are the conjuncts enforced by the price fairness theorem whenever `has_clearing_price_prop` is true (this is exactly `Scenario1_UniformPrice : satisfies run_s1 0 priceOK`).

#### Important alignment note (priority atoms)

Although priority is conceptually "step-based", the mechanization exposes it as *state predicates* that inspect what the deterministic greedy selector would choose in that state. Concretely, both priority atoms are of the form:

- `phase s = P3 -> ...`

So outside phase `P3` these atoms hold trivially (because the antecedent is false). This is why a global invariant `G(prio*_step_ok)` is the correct LTL encoding for the intended per-round constraint.

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
| Rejection | Mentioned in Chapter 3 | Not included in this repo snapshot | Out of scope for current fairness proofs |

These choices are **standard practice in formal verification**: the thesis emphasizes mathematical clarity and essential logic, while the code provides a mechanically checkable implementation with necessary bookkeeping. The correctness of the formalization depends on faithful implementation of the thesis's core definitions (matching, feasibility, clearing price), which has been achieved.
