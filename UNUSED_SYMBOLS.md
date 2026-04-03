# Unused Coq symbols (external references)
This flags top-level identifiers with **no textual references in other `.v` files**.
Heuristic only: comments are not stripped; qualified names/notations can confuse matching.

## Summary
| File | Top-level symbols | Unused outside file | Unused anywhere (heuristic) |
|---|---:|---:|---:|
| MUDA/Types.v | 12 | 6 | 0 |
| MUDA/Sorting.v | 11 | 4 | 0 |
| MUDA/Matching.v | 12 | 3 | 0 |
| Fairness/Interpretation.v | 11 | 2 | 0 |
| MUDA/ClearingPrice.v | 8 | 2 | 0 |
| MUDA/Transitions.v | 6 | 2 | 0 |
| Fairness/PriceFairness.v | 2 | 0 | 0 |
| Fairness/PriorityFairness.v | 2 | 0 | 0 |
| Fairness/QuantityFairness.v | 2 | 0 | 0 |
| LTL/Semantics.v | 3 | 0 | 0 |
| LTL/Syntax.v | 2 | 0 | 0 |
| MUDA/Atoms.v | 6 | 0 | 0 |
| MUDA/State.v | 8 | 0 | 0 |

## Per-file details

### Fairness/Interpretation.v
- Total symbols: 11
- Unused outside file: 2
- Unused anywhere (heuristic): 0

Unused outside file:
- `p_phase`
- `nth_phase`

### Fairness/PriceFairness.v
- Total symbols: 2
- Unused outside file: 0
- Unused anywhere (heuristic): 0

(Every symbol is referenced from another file.)

### Fairness/PriorityFairness.v
- Total symbols: 2
- Unused outside file: 0
- Unused anywhere (heuristic): 0

(Every symbol is referenced from another file.)

### Fairness/QuantityFairness.v
- Total symbols: 2
- Unused outside file: 0
- Unused anywhere (heuristic): 0

(Every symbol is referenced from another file.)

### LTL/Semantics.v
- Total symbols: 3
- Unused outside file: 0
- Unused anywhere (heuristic): 0

(Every symbol is referenced from another file.)

### LTL/Syntax.v
- Total symbols: 2
- Unused outside file: 0
- Unused anywhere (heuristic): 0

(Every symbol is referenced from another file.)

### MUDA/Atoms.v
- Total symbols: 6
- Unused outside file: 0
- Unused anywhere (heuristic): 0

(Every symbol is referenced from another file.)

### MUDA/ClearingPrice.v
- Total symbols: 8
- Unused outside file: 2
- Unused anywhere (heuristic): 0

Unused outside file:
- `in_rev_l`
- `marginal_pair_price_bound`

### MUDA/Matching.v
- Total symbols: 12
- Unused outside file: 3
- Unused anywhere (heuristic): 0

Unused outside file:
- `best_feasible_ask_spec`
- `allocated_bid_app_single`
- `allocated_ask_app_single`

### MUDA/Sorting.v
- Total symbols: 11
- Unused outside file: 4
- Unused anywhere (heuristic): 0

Unused outside file:
- `insert_bid`
- `insert_ask`
- `sort_bids`
- `sort_asks`

### MUDA/State.v
- Total symbols: 8
- Unused outside file: 0
- Unused anywhere (heuristic): 0

(Every symbol is referenced from another file.)

### MUDA/Transitions.v
- Total symbols: 6
- Unused outside file: 2
- Unused anywhere (heuristic): 0

Unused outside file:
- `finish_matching`
- `wf_state_step_preservation`

### MUDA/Types.v
- Total symbols: 12
- Unused outside file: 6
- Unused anywhere (heuristic): 0

Unused outside file:
- `AgentType`
- `agent_type_eq_dec`
- `nat_eq_dec`
- `agent_eq_dec`
- `bid_eq_dec_spec`
- `ask_eq_dec_spec`
