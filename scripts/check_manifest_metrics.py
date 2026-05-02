#!/usr/bin/env python3
"""Check that public TauLib metric copy uses the Atlas release manifest."""

from __future__ import annotations

import re
import sys
from pathlib import Path


README_START = "<!-- release-metrics:start -->"
README_END = "<!-- release-metrics:end -->"

SKIP_PARTS = {".git", ".lake", "build", "node_modules", "site/_data/release"}
CHECK_SUFFIXES = {".md", ".html", ".yml", ".yaml"}

FORBIDDEN = [
    (re.compile(r"\b522\s+modules\b", re.I), "stale module count"),
    (re.compile(r"\b512\s+Lean\s+modules\b", re.I), "hardcoded manifest metric"),
    (re.compile(r"\b142,406\s+lines\b", re.I), "hardcoded line count"),
    (re.compile(r"\b4,863\s+theorem", re.I), "hardcoded theorem/lemma count"),
    (re.compile(r"\b14,601\s+declaration", re.I), "hardcoded declaration count"),
]


def strip_generated_blocks(text: str) -> str:
    return re.sub(re.escape(README_START) + r".*?" + re.escape(README_END), "", text, flags=re.S)


def should_skip(path: Path, root: Path) -> bool:
    rel = path.relative_to(root).as_posix()
    return any(part in rel for part in SKIP_PARTS)


def main() -> int:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
    failures: list[str] = []
    for path in sorted(root.rglob("*")):
        if not path.is_file() or path.suffix not in CHECK_SUFFIXES or should_skip(path, root):
            continue
        text = strip_generated_blocks(path.read_text(encoding="utf-8", errors="ignore"))
        for pattern, label in FORBIDDEN:
            for match in pattern.finditer(text):
                line = text.count("\n", 0, match.start()) + 1
                failures.append(f"{path.relative_to(root)}:{line}: {label}: {match.group(0)!r}")
    if failures:
        print("TauLib public metric drift found:", file=sys.stderr)
        for item in failures:
            print(f"- {item}", file=sys.stderr)
        return 1
    print("✓ TauLib public metric copy is manifest-owned.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
