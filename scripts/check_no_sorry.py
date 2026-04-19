#!/usr/bin/env python3
"""
check_no_sorry.py — audit sorry/axiom counts with correct comment handling.

This script strips Lean block comments (/- ... -/ possibly nested),
docstrings (/-- ... -/ and /-! ... -/), line comments (-- ...), and
string literals ("...") from each source file, then counts remaining
occurrences of actual sorry-closing patterns. This avoids the false
positives that a pure grep approach produces when documentation prose
quotes Lean code (e.g., "theorem X : True := sorry" inside a /-! -/
docstring).

Exit codes:
  0 — counts match the expected values
  1 — drift detected

Output on stderr:
  For each drifting metric, the actual count and (if nonzero) the
  offending file:line locations after comment-stripping.

Matching rules, applied AFTER comment/string stripping:
  AXIOMS: lines matching ^\\s*axiom\\s+ (the `^axiom ` column-0 check
          used by the previous CI step is equivalent given TauLib's
          style; the explicit \\s* makes the intent clearer).
  SORRY:  any remaining occurrence of the whole word `sorry`. After
          stripping, the only places `sorry` can appear are term or
          tactic positions — i.e., real proof debt.

Usage:
  python3 scripts/check_no_sorry.py \\
    --root TauLib --expected-axioms 3 --expected-sorry 0
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# Comment / string stripping
# ---------------------------------------------------------------------------

# Lean block comments nest (/- /- ... -/ -/). The /-- docstring and /-!
# module-docstring variants behave like /- for nesting purposes. A
# character-level scan is the simplest way to get this right.

def strip_comments_and_strings(src: str) -> str:
    """Return `src` with all Lean comments and string literals replaced
    by equivalent whitespace (so line numbers are preserved)."""
    out = []
    i = 0
    n = len(src)
    while i < n:
        c = src[i]
        c2 = src[i:i+2]

        # Line comment: -- ... \n
        if c2 == "--":
            # Emit spaces until end of line (keep newline).
            j = src.find("\n", i)
            if j == -1:
                j = n
            out.append(" " * (j - i))
            i = j
            continue

        # Block comment (incl. /-- and /-! docstrings). These nest.
        if c2 == "/-":
            depth = 1
            j = i + 2
            # Preserve newlines inside; replace other chars with space.
            chunk = ["/", "-"]
            while j < n and depth > 0:
                d2 = src[j:j+2]
                if d2 == "/-":
                    depth += 1
                    chunk.append("  ")
                    j += 2
                elif d2 == "-/":
                    depth -= 1
                    chunk.append("  ")
                    j += 2
                else:
                    ch = src[j]
                    chunk.append(ch if ch == "\n" else " ")
                    j += 1
            # Replace the /- opener with spaces so downstream matchers
            # don't see it.
            out.append(" " * (j - i))
            i = j
            continue

        # String literal: "..." with \" escapes. We keep newlines inside
        # (unusual but possible in raw contexts); replace other chars.
        if c == '"':
            j = i + 1
            chunk = [" "]
            while j < n:
                if src[j] == "\\" and j + 1 < n:
                    chunk.append("  ")
                    j += 2
                    continue
                if src[j] == '"':
                    chunk.append(" ")
                    j += 1
                    break
                ch = src[j]
                chunk.append(ch if ch == "\n" else " ")
                j += 1
            out.append("".join(chunk))
            i = j
            continue

        out.append(c)
        i += 1
    return "".join(out)


# ---------------------------------------------------------------------------
# Scanners
# ---------------------------------------------------------------------------

AXIOM_RE = re.compile(r"^\s*axiom\s+", re.MULTILINE)
SORRY_RE = re.compile(r"\bsorry\b")


def find_hits(stripped: str, pattern: re.Pattern[str]) -> list[int]:
    """Return 1-based line numbers where `pattern` matches in stripped text."""
    hits = []
    for m in pattern.finditer(stripped):
        line = stripped.count("\n", 0, m.start()) + 1
        hits.append(line)
    return hits


def scan(root: Path) -> tuple[list[tuple[Path, int]], list[tuple[Path, int]]]:
    axiom_hits: list[tuple[Path, int]] = []
    sorry_hits: list[tuple[Path, int]] = []
    for path in sorted(root.rglob("*.lean")):
        src = path.read_text(encoding="utf-8", errors="replace")
        stripped = strip_comments_and_strings(src)
        for line in find_hits(stripped, AXIOM_RE):
            axiom_hits.append((path, line))
        for line in find_hits(stripped, SORRY_RE):
            sorry_hits.append((path, line))
    return axiom_hits, sorry_hits


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--root", type=Path, default=Path("TauLib"))
    p.add_argument("--expected-axioms", type=int, default=3)
    p.add_argument("--expected-sorry", type=int, default=0)
    p.add_argument("--report-only", action="store_true",
                   help="Print counts and offenders but do not exit nonzero.")
    args = p.parse_args()

    if not args.root.exists():
        print(f"::error::root not found: {args.root}", file=sys.stderr)
        return 1

    axioms, sorries = scan(args.root)
    print(f"Expected: axioms={args.expected_axioms}, sorry={args.expected_sorry}")
    print(f"Actual:   axioms={len(axioms)}, sorry={len(sorries)}")

    fail = False

    if len(axioms) != args.expected_axioms:
        print(
            f"::error::Axiom count drift: expected {args.expected_axioms}, "
            f"got {len(axioms)}.",
            file=sys.stderr,
        )
        print("::error::If this is an intentional change, update EXPECTED_AXIOMS", file=sys.stderr)
        print("::error::in .github/workflows/lean-build.yml AND the paper (§7 + Appendix C)", file=sys.stderr)
        print("::error::AND README.md.", file=sys.stderr)
        print("::error::Current axioms:", file=sys.stderr)
        for path, line in axioms:
            print(f"::error::  {path}:{line}", file=sys.stderr)
        fail = True
    else:
        print(f"✓ Axiom count: {len(axioms)} (expected {args.expected_axioms})")

    if len(sorries) != args.expected_sorry:
        print(
            f"::error::Sorry count drift: expected {args.expected_sorry}, "
            f"got {len(sorries)}.",
            file=sys.stderr,
        )
        print("::error::TauLib is sorry-free in all seven books since peer-review-fixes-v1.", file=sys.stderr)
        print("::error::If a new sorry-closed declaration is intentional, first discuss", file=sys.stderr)
        print("::error::via issue, then update EXPECTED_SORRY in this workflow and the paper.", file=sys.stderr)
        print("::error::Current sorry hits (after comment/string stripping):", file=sys.stderr)
        for path, line in sorries:
            print(f"::error::  {path}:{line}", file=sys.stderr)
        fail = True
    else:
        print(f"✓ Sorry count: {len(sorries)} (expected {args.expected_sorry})")

    if fail and not args.report_only:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
