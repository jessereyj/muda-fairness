# Learning Pack: MUDA Fairness Thesis (Internal)

This folder is an internal study pack to help you *learn / rehearse / defend* the thesis and to connect the PDF narrative to the verified Rocq development in this repo.

For the project overview, build instructions, and the high-level list of verified properties, start at the repo root: [README.md](../../README.md).

Contents:
- `SUMMARY.md` — executive summary (problem, contribution, what is proved)
- `CHAPTER_NOTES.md` — compressed chapter-by-chapter notes
- `THESIS_CODE_CROSSWALK.md` — thesis concepts ↔ Rocq modules (with links)
- `PROOF_WALKTHROUGH.md` — line-by-line walkthrough plan for the Rocq proofs
- `DEFENSE_QA.md` — likely defense questions + crisp answers

## Important
- The thesis document is marked restricted. These notes are meant for private use inside this workspace.
- The Rocq development is treated as the source of truth for definitions and theorems.

## If you want precise PDF alignment
The tooling here can’t directly search/quote binary PDFs. If you want section-level alignment:
- Convert the PDF to text and add it to the workspace, e.g. `docs/thesis/thesis.txt`.
- Or add the LaTeX sources.

Suggested local command:

```bash
# macOS (poppler): brew install poppler
pdftotext -layout UPD-CoE-Thesis-Template.pdf docs/thesis.txt
```
