# MUDA Fairness Verification

Formal verification of fairness properties in Multi-Unit Double Auction (MUDA) using Coq and Linear Temporal Logic (LTL).

## Structure
```
LTL/       - Linear Temporal Logic foundation (5 files)
MUDA/      - MUDA protocol model (7 files)
Fairness/  - Fairness property proofs (7 files)
```

## Quick Start

### Build everything
```bash
./build.sh
```

### Clean build artifacts
```bash
./clean.sh
```

### Check for admitted lemmas
```bash
./check.sh
```

### Show project statistics
```bash
./stats.sh
```

## Requirements

- **Coq:** 8.18.0 or higher
- **Bash:** For build scripts

## Build Process

The `build.sh` script:
1. Cleans old artifacts
2. Verifies directory structure
3. Generates `_CoqProject`
4. Creates `Makefile.coq`
5. Builds with parallel jobs
6. Checks for admitted lemmas

## Statistics

- **4,826 lines** of Coq code
- **15 main theorems** (3 meta + 7 fairness + 5 supporting)
- **0 admitted lemmas** - All proofs complete

## Verification Results

| Property | Formula | Status |
|----------|---------|--------|
| Quantity Fairness | G(allocOK) | ✓ Proven |
| Priority Fairness | G(priority constraints) | ✓ Proven |
| Match Finality | G(matched → G matched) | ✓ Proven |
| Termination | F(terminal) | ✓ Proven |
| Price Fairness | F(unique(c*) ∧ bounds(c*)) | ✓ Proven |
| Rejection Fairness | G(terminal ∧ rejected → justified) | ✓ Proven |

## Development Workflow

### Edit a file
```bash
vim MUDA/State.v
```

### Compile just that file
```bash
coqc -R MUDA MUDA.MUDA MUDA/State.v
```

### Full rebuild
```bash
./build.sh
```

### Watch mode (auto-rebuild)
```bash
./watch.sh
```

## License

MIT License