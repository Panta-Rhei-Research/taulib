#!/usr/bin/env python3
"""
Audit the Lean import closure for the final RH spine slice.

This is intentionally narrower than `check_no_sorry.py --root TauLib`: it
follows the dependency graph from a single proof-spine module and checks only
the source files reachable from that module.  The legacy Book III ambient bridge
axioms remain in TauLib for compatibility, but the final RH spine must not
depend on their modules.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from check_no_sorry import (  # noqa: E402
    AXIOM_RE,
    SORRY_RE,
    find_hits,
    strip_comments_and_strings,
)

IMPORT_RE = re.compile(
    r"^\s*(?:public\s+|private\s+)?import\s+(?:all\s+)?([^\s]+)",
    re.MULTILINE,
)

DEFAULT_DENIED_MODULES = (
    "TauLib.BookIII.Bridge.BridgeAxiom",
    "TauLib.BookIII.Doors.SpectralCorrespondence",
    "TauLib.BookIII.Doors.GrandGRH",
)


def module_to_path(module: str, cwd: Path) -> Path | None:
    """Resolve a local Lean module name to a source file, if present."""
    candidate = cwd.joinpath(*module.split(".")).with_suffix(".lean")
    if candidate.exists():
        return candidate
    return None


def imported_modules(path: Path) -> list[str]:
    src = path.read_text(encoding="utf-8", errors="replace")
    stripped = strip_comments_and_strings(src)
    return [m.group(1) for m in IMPORT_RE.finditer(stripped)]


def import_closure(root_module: str, cwd: Path) -> tuple[list[Path], list[str]]:
    """Return reachable local Lean files and local module names."""
    seen_modules: set[str] = set()
    seen_files: set[Path] = set()
    ordered_files: list[Path] = []
    ordered_modules: list[str] = []
    stack = [root_module]

    while stack:
        module = stack.pop()
        if module in seen_modules:
            continue
        seen_modules.add(module)

        path = module_to_path(module, cwd)
        if path is None:
            continue

        ordered_modules.append(module)
        resolved = path.resolve()
        if resolved not in seen_files:
            seen_files.add(resolved)
            ordered_files.append(path)

        imports = imported_modules(path)
        stack.extend(reversed(imports))

    return ordered_files, ordered_modules


def scan_files(files: list[Path]) -> tuple[list[tuple[Path, int]], list[tuple[Path, int]]]:
    axiom_hits: list[tuple[Path, int]] = []
    sorry_hits: list[tuple[Path, int]] = []
    for path in files:
        src = path.read_text(encoding="utf-8", errors="replace")
        stripped = strip_comments_and_strings(src)
        for line in find_hits(stripped, AXIOM_RE):
            axiom_hits.append((path, line))
        for line in find_hits(stripped, SORRY_RE):
            sorry_hits.append((path, line))
    return axiom_hits, sorry_hits


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--module",
        default="TauLib.BookIII.Bridge.G8BookIIICharacterAcceptedRealizationReduction",
        help="Root Lean module whose local import closure should be audited.",
    )
    parser.add_argument("--expected-axioms", type=int, default=0)
    parser.add_argument("--expected-sorry", type=int, default=0)
    parser.add_argument(
        "--deny-module",
        action="append",
        default=[],
        help="Lean module name forbidden in the reachable import closure.",
    )
    parser.add_argument(
        "--print-files",
        action="store_true",
        help="Print the reachable local Lean source files.",
    )
    args = parser.parse_args()

    cwd = Path.cwd()
    files, modules = import_closure(args.module, cwd)
    denied_modules = set(DEFAULT_DENIED_MODULES).union(args.deny_module)
    reached_denied = sorted(denied_modules.intersection(modules))
    axioms, sorries = scan_files(files)

    if args.print_files:
        print("Reachable local Lean files:")
        for path in files:
            print(f"  {path}")

    print(f"Root module: {args.module}")
    print(f"Reachable local Lean modules: {len(modules)}")
    print(f"Reachable local Lean files:   {len(files)}")
    print(f"Expected: axioms={args.expected_axioms}, sorry={args.expected_sorry}")
    print(f"Actual:   axioms={len(axioms)}, sorry={len(sorries)}")

    failed = False

    if reached_denied:
        failed = True
        print("::error::Forbidden legacy axiom modules are reachable:", file=sys.stderr)
        for module in reached_denied:
            print(f"::error::  {module}", file=sys.stderr)

    if len(axioms) != args.expected_axioms:
        failed = True
        print(
            f"::error::Axiom count drift in final RH spine closure: "
            f"expected {args.expected_axioms}, got {len(axioms)}.",
            file=sys.stderr,
        )
        for path, line in axioms:
            print(f"::error::  {path}:{line}", file=sys.stderr)
    else:
        print(f"✓ Axiom count: {len(axioms)} (expected {args.expected_axioms})")

    if len(sorries) != args.expected_sorry:
        failed = True
        print(
            f"::error::Sorry count drift in final RH spine closure: "
            f"expected {args.expected_sorry}, got {len(sorries)}.",
            file=sys.stderr,
        )
        for path, line in sorries:
            print(f"::error::  {path}:{line}", file=sys.stderr)
    else:
        print(f"✓ Sorry count: {len(sorries)} (expected {args.expected_sorry})")

    if reached_denied:
        print("✗ Legacy Book III bridge axiom modules excluded: no", file=sys.stderr)
    else:
        print("✓ Legacy Book III bridge axiom modules excluded")

    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
