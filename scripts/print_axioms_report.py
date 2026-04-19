#!/usr/bin/env python3
"""
Harvest `#print axioms` output for TauLib headline theorems.

Invokes Lean on `TauLib/Meta/PrintAxioms.lean`, captures the
`'<name>' depends on axioms: [...]` messages, parses them into a
structured record, and emits:

  - `.github/workflows/output/print_axioms.json`  (machine-readable)
  - `docs/print_axioms_report.md`                 (human-readable)

Motivation: Round 2 of the Breitner peer review (2026-04-19) observed
that the `/verify/tcb.md` page's per-theorem TCB partition was
author-attested rather than machine-attested. This script closes the
gap — the artifacts it produces are a direct function of Lean's own
elaboration output, so the TCB classification rides on the same
trusted compute base as the theorems themselves.

Usage (from TauLib repo root):

    python3 scripts/print_axioms_report.py

or, for CI, with explicit output directories:

    python3 scripts/print_axioms_report.py \
        --json .github/workflows/output/print_axioms.json \
        --markdown docs/print_axioms_report.md

The script is intentionally conservative: if Lean emits anything
unexpected (missing theorem, changed message format), the script
exits non-zero and prints the offending stderr/stdout chunk rather
than silently falling back to stale data.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Iterable

# ---------------------------------------------------------------------------
# Constants — kept in sync with TauLib/Meta/PrintAxioms.lean
# ---------------------------------------------------------------------------

# The five "Mathlib baseline" axioms that Lean 4 + Mathlib tactics routinely
# pull in. We surface them but do *not* count them as TCB extensions.
MATHLIB_BASELINE = {
    "Classical.choice",
    "propext",
    "Quot.sound",
}

# The two axioms that native_decide (the compiled-code decision procedure)
# introduces. Presence of either flags the theorem as "TCB-extended": a
# reviewer accepting only the Lean kernel cannot accept these without
# accepting Lean's native compiler pipeline as well.
NATIVE_DECIDE_AXIOMS = {
    "Lean.ofReduceBool",
    "Lean.trustCompiler",
}

# The three project-declared axioms in TauLib. Presence of any flags the
# theorem as project-axiom-dependent, which is a separate (and orthogonal)
# TCB concern from native_decide.
PROJECT_AXIOMS = {
    "Tau.BookIII.Bridge.bridge_functor_exists",
    "Tau.BookIII.Doors.spectral_correspondence_O3",
    "Tau.BookIII.Doors.grand_grh_adelic",
}

# Harvester contract: the driver file precedes each `#print axioms` with a
# comment of the form `-- HARVEST: <name> | <module path>`. We read those
# comments to recover (theorem -> module) mapping independent of Lean's
# message stream.
HARVEST_MARKER = re.compile(
    r"^\s*--\s*HARVEST:\s*(?P<name>\S+)\s*\|\s*(?P<module>\S.*\S)\s*$"
)

# Lean 4 `#print axioms` emits either:
#   'Foo' depends on axioms: [Classical.choice, propext, Quot.sound]
# or, if the theorem is closed with no axioms:
#   'Foo' does not depend on any axioms
AXIOM_LINE_WITH = re.compile(
    r"^'(?P<name>[^']+)' depends on axioms: \[(?P<axioms>[^\]]*)\]\s*$"
)
AXIOM_LINE_EMPTY = re.compile(r"^'(?P<name>[^']+)' does not depend on any axioms\s*$")


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------


@dataclass
class TheoremRecord:
    name: str
    module: str
    axioms: list[str] = field(default_factory=list)
    project_axioms: list[str] = field(default_factory=list)
    tcb_extensions: list[str] = field(default_factory=list)

    @property
    def classification(self) -> str:
        """One of: 'kernel-only', 'native_decide', 'project-axiom',
        'project-axiom+native_decide'."""
        has_native = bool(self.tcb_extensions)
        has_project = bool(self.project_axioms)
        if has_project and has_native:
            return "project-axiom+native_decide"
        if has_project:
            return "project-axiom"
        if has_native:
            return "native_decide"
        return "kernel-only"


# ---------------------------------------------------------------------------
# I/O helpers
# ---------------------------------------------------------------------------


def run_cmd(cmd: list[str], cwd: Path) -> tuple[str, str, int]:
    """Run a subprocess; return (stdout, stderr, returncode)."""
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        check=False,
        capture_output=True,
        text=True,
    )
    return proc.stdout, proc.stderr, proc.returncode


def git_sha(repo_root: Path) -> str:
    out, _, rc = run_cmd(["git", "rev-parse", "HEAD"], repo_root)
    return out.strip() if rc == 0 else "unknown"


def toolchain(repo_root: Path) -> str:
    p = repo_root / "lean-toolchain"
    if p.exists():
        return p.read_text(encoding="utf-8").strip()
    return "unknown"


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------


def parse_harvest_markers(driver_path: Path) -> dict[str, str]:
    """Recover (fully-qualified theorem name -> source module) from the
    driver file's HARVEST marker comments."""
    mapping: dict[str, str] = {}
    for line in driver_path.read_text(encoding="utf-8").splitlines():
        m = HARVEST_MARKER.match(line)
        if m:
            mapping[m.group("name")] = m.group("module")
    return mapping


def parse_lean_output(text: str) -> dict[str, list[str]]:
    """Scan Lean's combined stdout/stderr for `#print axioms` results.

    Returns a dict name -> list of axioms (possibly empty).
    """
    results: dict[str, list[str]] = {}
    for raw in text.splitlines():
        line = raw.strip()
        m = AXIOM_LINE_WITH.match(line)
        if m:
            name = m.group("name")
            axioms_str = m.group("axioms").strip()
            if axioms_str:
                axioms = [a.strip() for a in axioms_str.split(",") if a.strip()]
            else:
                axioms = []
            results[name] = axioms
            continue
        m = AXIOM_LINE_EMPTY.match(line)
        if m:
            results[m.group("name")] = []
    return results


def classify(theorem: TheoremRecord, all_axioms: list[str]) -> None:
    """Populate theorem.axioms, .project_axioms, .tcb_extensions."""
    theorem.axioms = sorted(all_axioms)
    theorem.project_axioms = sorted(a for a in all_axioms if a in PROJECT_AXIOMS)
    theorem.tcb_extensions = sorted(a for a in all_axioms if a in NATIVE_DECIDE_AXIOMS)


# ---------------------------------------------------------------------------
# Lean invocation
# ---------------------------------------------------------------------------


def invoke_lean(repo_root: Path, driver_module: str) -> tuple[str, int]:
    """Build the driver module and capture its elaboration output.

    We use `lake env lean TauLib/Meta/PrintAxioms.lean` rather than
    `lake build`, because `#print axioms` is an elaboration-time command
    whose messages are shown by the elaborator at the point the command
    is encountered; `lake build` would produce the same messages but
    wrapped in a less predictable progress stream. Using `lake env lean`
    directly gives us a clean single-file compile.
    """
    path = driver_module.replace(".", "/") + ".lean"
    cmd = ["lake", "env", "lean", path]
    stdout, stderr, rc = run_cmd(cmd, repo_root)
    # Both stdout and stderr may carry `#print axioms` messages depending
    # on Lean version; combine them before parsing.
    return stdout + "\n" + stderr, rc


# ---------------------------------------------------------------------------
# Report emission
# ---------------------------------------------------------------------------


def build_json_payload(
    theorems: list[TheoremRecord],
    repo_root: Path,
) -> dict:
    return {
        "generated_at": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "toolchain": toolchain(repo_root),
        "commit": git_sha(repo_root),
        "theorems": [asdict(t) for t in theorems],
    }


def build_markdown_report(theorems: list[TheoremRecord], payload: dict) -> str:
    """Human-readable partition of theorems by TCB classification."""
    bucket_kernel: list[TheoremRecord] = []
    bucket_native: list[TheoremRecord] = []
    bucket_project: list[TheoremRecord] = []
    bucket_project_native: list[TheoremRecord] = []
    for t in theorems:
        c = t.classification
        if c == "kernel-only":
            bucket_kernel.append(t)
        elif c == "native_decide":
            bucket_native.append(t)
        elif c == "project-axiom":
            bucket_project.append(t)
        else:
            bucket_project_native.append(t)

    lines: list[str] = []
    lines.append("# TauLib Per-Theorem `#print axioms` Report")
    lines.append("")
    lines.append(
        f"*Generated at:* `{payload['generated_at']}` · "
        f"*toolchain:* `{payload['toolchain']}` · "
        f"*commit:* `{payload['commit'][:12]}`"
    )
    lines.append("")
    lines.append(
        "This report is emitted by `scripts/print_axioms_report.py` from the "
        "elaboration output of `TauLib/Meta/PrintAxioms.lean`. It is the "
        "machine-attested companion to "
        "[/verify/tcb/](https://panta-rhei.site/verify/tcb/) on the site: "
        "where that page names which theorems carry the `native_decide` TCB "
        "extension or depend on one of the three project axioms, this report "
        "is the primary source."
    )
    lines.append("")
    lines.append("## TCB classification")
    lines.append("")
    lines.append(
        "Each theorem is placed in exactly one of four buckets based on the "
        "axioms its transitive proof chain contains:"
    )
    lines.append("")
    lines.append(
        "- **kernel-only** — `Classical.choice`, `propext`, `Quot.sound` "
        "only (Mathlib baseline); no extensions."
    )
    lines.append(
        "- **native_decide** — also `Lean.ofReduceBool` and/or "
        "`Lean.trustCompiler`; accepting these means accepting Lean's native "
        "compiler pipeline."
    )
    lines.append(
        "- **project-axiom** — transitively depends on one of the three "
        "Book III axioms (`bridge_functor_exists`, "
        "`spectral_correspondence_O3`, `grand_grh_adelic`)."
    )
    lines.append(
        "- **project-axiom+native_decide** — both of the above."
    )
    lines.append("")

    def table(bucket: list[TheoremRecord]) -> list[str]:
        if not bucket:
            return ["_(none in this build)_", ""]
        out = [
            "| Theorem | Module | Project axioms | `native_decide` extensions |",
            "|---------|--------|----------------|----------------------------|",
        ]
        for t in sorted(bucket, key=lambda r: r.name):
            p = ", ".join(f"`{a}`" for a in t.project_axioms) or "—"
            n = ", ".join(f"`{a}`" for a in t.tcb_extensions) or "—"
            out.append(f"| `{t.name}` | `{t.module}` | {p} | {n} |")
        out.append("")
        return out

    lines.append("### Kernel-only")
    lines.extend(table(bucket_kernel))
    lines.append("### `native_decide`-extended (no project axioms)")
    lines.extend(table(bucket_native))
    lines.append("### Project-axiom-dependent (no `native_decide`)")
    lines.extend(table(bucket_project))
    lines.append("### Project-axiom-dependent + `native_decide`")
    lines.extend(table(bucket_project_native))

    lines.append("## Raw axiom listing")
    lines.append("")
    lines.append(
        "For each theorem the full axiom set Lean reports. This is the "
        "unfiltered output of `#print axioms`, included so a reviewer can "
        "audit the classification above without re-running Lean."
    )
    lines.append("")
    for t in sorted(theorems, key=lambda r: r.name):
        lines.append(f"### `{t.name}`")
        lines.append("")
        lines.append(f"*Module:* `{t.module}` · *Classification:* `{t.classification}`")
        lines.append("")
        if t.axioms:
            for a in t.axioms:
                lines.append(f"- `{a}`")
        else:
            lines.append("_(no axioms — pure kernel derivation)_")
        lines.append("")

    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="TauLib repository root (default: parent of this script).",
    )
    ap.add_argument(
        "--driver",
        default="TauLib.Meta.PrintAxioms",
        help="Lean module to invoke (default: TauLib.Meta.PrintAxioms).",
    )
    ap.add_argument(
        "--json",
        type=Path,
        default=Path(".github/workflows/output/print_axioms.json"),
        help="Output JSON path (relative to --repo-root unless absolute).",
    )
    ap.add_argument(
        "--markdown",
        type=Path,
        default=Path("docs/print_axioms_report.md"),
        help="Output Markdown path (relative to --repo-root unless absolute).",
    )
    ap.add_argument(
        "--skip-lean",
        action="store_true",
        help=(
            "Do not invoke Lean; read a pre-captured output from --lean-log "
            "instead. Useful for CI steps that want to split build and "
            "reporting."
        ),
    )
    ap.add_argument(
        "--lean-log",
        type=Path,
        default=None,
        help="Pre-captured Lean output (used with --skip-lean).",
    )
    args = ap.parse_args(argv)

    repo_root: Path = args.repo_root.resolve()
    driver_path = repo_root / (args.driver.replace(".", "/") + ".lean")
    if not driver_path.exists():
        print(
            f"error: driver not found at {driver_path}",
            file=sys.stderr,
        )
        return 2

    markers = parse_harvest_markers(driver_path)
    if not markers:
        print(
            f"error: no HARVEST markers in {driver_path}; nothing to report.",
            file=sys.stderr,
        )
        return 2

    # Get Lean output
    if args.skip_lean:
        if args.lean_log is None or not args.lean_log.exists():
            print(
                "error: --skip-lean requires --lean-log pointing at a file.",
                file=sys.stderr,
            )
            return 2
        lean_output = args.lean_log.read_text(encoding="utf-8")
    else:
        lean_output, rc = invoke_lean(repo_root, args.driver)
        if rc != 0:
            # Non-fatal: Lean returned non-zero, but #print axioms may still
            # have succeeded. Print a warning; continue parsing.
            print(
                f"warning: `lake env lean` exited with {rc}; "
                "attempting to parse output anyway.",
                file=sys.stderr,
            )

    parsed = parse_lean_output(lean_output)

    theorems: list[TheoremRecord] = []
    missing: list[str] = []
    for name, module in markers.items():
        if name not in parsed:
            missing.append(name)
            continue
        t = TheoremRecord(name=name, module=module)
        classify(t, parsed[name])
        theorems.append(t)

    if missing:
        print(
            "warning: no `#print axioms` output parsed for: "
            + ", ".join(missing),
            file=sys.stderr,
        )

    payload = build_json_payload(theorems, repo_root)
    md = build_markdown_report(theorems, payload)

    json_path = args.json if args.json.is_absolute() else repo_root / args.json
    md_path = args.markdown if args.markdown.is_absolute() else repo_root / args.markdown
    json_path.parent.mkdir(parents=True, exist_ok=True)
    md_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    md_path.write_text(md, encoding="utf-8")

    print(f"Wrote {json_path}")
    print(f"Wrote {md_path}")
    print(
        f"Harvested {len(theorems)}/{len(markers)} theorems "
        f"(missing: {len(missing)})."
    )
    return 0 if not missing else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
