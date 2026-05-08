#!/usr/bin/env python3
"""Check that public TauLib metric copy uses the Corpus release manifest."""

from __future__ import annotations

import os
import json
import re
import sys
from pathlib import Path
from typing import Any


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

COMPARE_FIELDS = [
    "value",
    "display_value",
    "unit",
    "public_label",
    "scope",
    "source_repo",
    "source_commit",
    "source_path",
    "filter_rule",
    "public_safe",
]


def strip_generated_blocks(text: str) -> str:
    return re.sub(re.escape(README_START) + r".*?" + re.escape(README_END), "", text, flags=re.S)


def read_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def metric_index(manifest: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {item["id"]: item for item in manifest.get("metrics", [])}


def check_internal_release_data(root: Path) -> list[str]:
    failures: list[str] = []
    js = root / "site/_data/release/current.json"
    if not js.exists():
        failures.append("site/_data/release/current.json missing")
        return failures
    json_data = read_json(js)
    json_index = metric_index(json_data)
    if not json_index:
        failures.append("site/_data/release/current.json contains no metrics")
    return failures


def dynamic_manifest_patterns(root: Path) -> list[tuple[re.Pattern[str], str]]:
    manifest_path = root / "site/_data/release/current.json"
    if not manifest_path.exists():
        return []
    data = read_json(manifest_path)
    patterns: list[tuple[re.Pattern[str], str]] = []
    for metric in data.get("metrics", []):
        display = str(metric.get("display_value", "")).strip()
        unit = str(metric.get("unit", "")).strip()
        if not display or not unit:
            continue
        if unit in {"mentions", "registry items", "axiom declarations", "sorry assignments"} and display in {"0", "1", "2", "3"}:
            continue
        forms = {display}
        if "," in display:
            forms.add(display.replace(",", ""))
        unit_pattern = re.escape(unit).replace(r"\ ", r"\s+")
        for number in forms:
            patterns.append((
                re.compile(rf"\b{re.escape(number)}\s+{unit_pattern}\b", re.I),
                f"hardcoded manifest metric {metric.get('id', '<unknown>')}",
            ))
    return patterns


def should_skip(path: Path, root: Path) -> bool:
    rel = path.relative_to(root).as_posix()
    return any(part in rel for part in SKIP_PARTS)


def iter_check_files(root: Path):
    for directory, dirnames, filenames in os.walk(root):
        dir_path = Path(directory)
        dirnames[:] = [
            name for name in dirnames
            if not should_skip(dir_path / name, root)
        ]
        for filename in filenames:
            path = dir_path / filename
            if path.suffix in CHECK_SUFFIXES and not should_skip(path, root):
                yield path


def main() -> int:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
    failures: list[str] = check_internal_release_data(root)
    manifest_patterns = dynamic_manifest_patterns(root)
    for path in sorted(iter_check_files(root)):
        text = strip_generated_blocks(path.read_text(encoding="utf-8", errors="ignore"))
        for pattern, label in FORBIDDEN + manifest_patterns:
            for match in pattern.finditer(text):
                line = text.count("\n", 0, match.start()) + 1
                failures.append(f"{path.relative_to(root)}:{line}: {label}: {match.group(0)!r}")
    if failures:
        print("TauLib public metric drift found:", file=sys.stderr)
        for item in failures:
            print(f"- {item}", file=sys.stderr)
        return 1
    print("✓ TauLib public metric copy is Corpus-manifest-owned.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
