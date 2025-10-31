# Linear Temporal Logic Foundation Layer

This directory contains the LTL foundation layer for the MUDA fairness verification project.

## Architecture

The LTL layer is split into five main components:

1. **Syntax.v** — Core LTL syntax (formulas, notation)
2. **Semantics.v** — Trace semantics and satisfaction
3. **Axioms.v** — Proof system
   - Inductive `Provable` type
   - Schematic axioms (A1, A2, A3) and rules (MP, restricted Nec)
4. **Soundness.v** — Soundness theorem (⊢ φ → ⊨ φ)
   - Proves validity of each axiom schema
   - Proves rule preservation (MP, restricted Nec)
5. **Completeness.v** — Completeness and meta-theory
   - `WeakCompleteness` (⊨ φ → ⊢ φ) cited as axiom
   - Proves `Consistency` and `Adequacy` as theorems

## Design Decisions

### Provable System
- Uses an inductive type for derivability (`Provable` in `Axioms.v`)
- Constructors for common LTL axioms and rules (A1, A2, A3, MP)
- Restricted necessitation rule (only for propositional tautologies)

### Meta-Theory Strategy
- **Soundness**: Fully mechanized proof that all derivable formulas are valid
- **Completeness**: Cited as axiom (avoids heavy canonical model construction)
- **Adequacy**: Derived as a theorem from Soundness and WeakCompleteness

### Dependencies
- Minimal stdlib imports (List, Bool, Classical, Arith)
- Clean layer boundary (only LTL concepts here)
- MUDA-specific code lives in higher layers

## Usage

To use the LTL layer in client code:

```coq
From LTL Require Import LTL.  (* Gets everything via the master export *)
```

Or import specific modules:

```coq
From LTL Require Import Syntax Semantics.  (* Just syntax and semantics *)
```

## References

The Hilbert system follows standard presentations of propositional LTL:
- Axioms A1-A3 for Next/Until operators
- Restricted necessitation (avoids certain circularity issues)
- Full details in Section 4 of the thesis