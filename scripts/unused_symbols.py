from __future__ import annotations

import re
from pathlib import Path

TOP_PAT = re.compile(
    r"^(?:#\[export\]\s+)?(Definition|Lemma|Theorem|Fixpoint|CoFixpoint|Inductive|Record|Class|Instance)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return path.read_text(encoding="latin-1")


def collect_symbols(text: str) -> list[tuple[str, str]]:
    symbols: list[tuple[str, str]] = []
    for line in text.splitlines():
        match = TOP_PAT.match(line)
        if match:
            symbols.append((match.group(1), match.group(2)))
    # de-dup while preserving order
    seen: set[str] = set()
    out: list[tuple[str, str]] = []
    for kind, sym in symbols:
        if sym not in seen:
            seen.add(sym)
            out.append((kind, sym))
    return out


def main() -> None:
    v_files = sorted(Path(".").rglob("*.v"))
    texts = {p: read_text(p) for p in v_files}
    symbols_by_file = {p: collect_symbols(txt) for p, txt in texts.items()}

    regex_cache: dict[str, re.Pattern[str]] = {}

    def sym_re(sym: str) -> re.Pattern[str]:
        cached = regex_cache.get(sym)
        if cached is None:
            cached = re.compile(r"\b" + re.escape(sym) + r"\b")
            regex_cache[sym] = cached
        return cached

    unused_external: dict[Path, list[str]] = {}
    unused_anywhere: dict[Path, list[str]] = {}

    for p, symbols in symbols_by_file.items():
        if not symbols:
            continue
        unused: list[str] = []
        unused_global: list[str] = []
        for kind, sym in symbols:
            r = sym_re(sym)
            found = any(r.search(qtxt) for q, qtxt in texts.items() if q != p)
            if not found:
                unused.append(sym)
            # Heuristic: if the symbol occurs only once in its own file and
            # never in other files, it is likely unused anywhere.
            # We exclude `Instance`s from this bucket because typeclass usage
            # is typically implicit (i.e., the instance name won't appear).
            if (kind != "Instance") and (not found) and (len(r.findall(texts[p])) <= 1):
                unused_global.append(sym)
        unused_external[p] = unused
        unused_anywhere[p] = unused_global

    lines: list[str] = []
    lines.append("# Unused Coq symbols (external references)\n")
    lines.append(
        "This flags top-level identifiers with **no textual references in other `.v` files**.\n"
    )
    lines.append(
        "Heuristic only: comments are not stripped; qualified names/notations can confuse matching.\n"
    )

    lines.append("\n## Summary\n")
    lines.append(
        "| File | Top-level symbols | Unused outside file | Unused anywhere (heuristic) |\n"
    )
    lines.append("|---|---:|---:|---:|\n")

    rows: list[tuple[int, int, str, int]] = []
    for p in v_files:
        total = len(symbols_by_file.get(p, []))
        if total == 0:
            continue
        unused = len(unused_external.get(p, []))
        unused_global = len(unused_anywhere.get(p, []))
        rows.append((unused, unused_global, str(p), total))

    for unused, unused_global, f, total in sorted(
        rows, key=lambda x: (-x[0], -x[1], x[2])
    ):
        lines.append(f"| {f} | {total} | {unused} | {unused_global} |\n")

    lines.append("\n## Per-file details\n")
    for p in v_files:
        symbols = symbols_by_file.get(p, [])
        if not symbols:
            continue
        unused = unused_external.get(p, [])
        unused_global = unused_anywhere.get(p, [])
        lines.append(f"\n### {p}\n")
        lines.append(f"- Total symbols: {len(symbols)}\n")
        lines.append(f"- Unused outside file: {len(unused)}\n")
        lines.append(f"- Unused anywhere (heuristic): {len(unused_global)}\n")
        if unused:
            lines.append("\nUnused outside file:\n")
            for sym in unused:
                lines.append(f"- `{sym}`\n")
        else:
            lines.append("\n(Every symbol is referenced from another file.)\n")

        if unused_global:
            lines.append("\nUnused anywhere (heuristic):\n")
            for sym in unused_global:
                lines.append(f"- `{sym}`\n")

    Path("UNUSED_SYMBOLS.md").write_text("".join(lines), encoding="utf-8")


if __name__ == "__main__":
    main()
