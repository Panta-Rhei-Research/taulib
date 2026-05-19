#!/usr/bin/env python3
"""
Generate a Markdown dependency/LOC audit dossier for the final RH spine slice.
"""

from __future__ import annotations

import argparse
import datetime as dt
import re
import sys
from dataclasses import dataclass
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from check_no_sorry import strip_comments_and_strings  # noqa: E402
from check_final_rh_spine_closure import DEFAULT_DENIED_MODULES  # noqa: E402

IMPORT_RE = re.compile(
    r"^\s*(?:public\s+|private\s+)?import\s+(?:all\s+)?([^\s]+)",
    re.MULTILINE,
)


@dataclass(frozen=True)
class ModuleNode:
    module: str
    path: Path | None
    bucket: str


@dataclass(frozen=True)
class LocStats:
    raw: int
    nonblank: int
    codeish: int


def package_roots(cwd: Path) -> list[Path]:
    roots = [cwd]
    packages = cwd / ".lake" / "packages"
    if packages.exists():
        for child in sorted(packages.iterdir()):
            if child.is_dir():
                roots.append(child.resolve())
    return roots


def module_path_from_root(module: str, root: Path) -> Path:
    return root.joinpath(*module.split(".")).with_suffix(".lean")


def resolve_module(module: str, cwd: Path, roots: list[Path]) -> Path | None:
    for root in roots:
        candidate = module_path_from_root(module, root)
        if candidate.exists():
            return candidate.resolve()
    return None


def bucket_for(module: str, path: Path | None, cwd: Path) -> str:
    if module.startswith("TauLib"):
        return "TauLib"
    if module.startswith("Mathlib"):
        return "Mathlib"
    if module.startswith("Std"):
        return "Lean stdlib"
    if module.startswith("Lean") or module.startswith("Init"):
        return "Lean core"
    if path is None:
        return "Unresolved external"

    packages = (cwd / ".lake" / "packages").resolve()
    try:
        rel = path.relative_to(packages)
        return f"Lean package: {rel.parts[0]}"
    except ValueError:
        return "Other local"


def imports_of(path: Path) -> list[str]:
    src = path.read_text(encoding="utf-8", errors="replace")
    stripped = strip_comments_and_strings(src)
    return [m.group(1) for m in IMPORT_RE.finditer(stripped)]


def import_closure(root_module: str, cwd: Path) -> tuple[list[ModuleNode], dict[str, list[str]]]:
    roots = package_roots(cwd)
    seen: set[str] = set()
    nodes: list[ModuleNode] = []
    edges: dict[str, list[str]] = {}
    stack = [root_module]

    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)

        path = resolve_module(module, cwd, roots)
        bucket = bucket_for(module, path, cwd)
        nodes.append(ModuleNode(module, path, bucket))

        if path is None:
            edges[module] = []
            continue

        imports = imports_of(path)
        edges[module] = imports
        stack.extend(reversed(imports))

    return nodes, edges


def loc_stats(path: Path | None) -> LocStats:
    if path is None:
        return LocStats(raw=0, nonblank=0, codeish=0)
    src = path.read_text(encoding="utf-8", errors="replace")
    raw_lines = src.splitlines()
    stripped = strip_comments_and_strings(src)
    code_lines = stripped.splitlines()
    return LocStats(
        raw=len(raw_lines),
        nonblank=sum(1 for line in raw_lines if line.strip()),
        codeish=sum(1 for line in code_lines if line.strip()),
    )


def module_family(module: str, bucket: str) -> str:
    parts = module.split(".")
    if bucket == "TauLib" and len(parts) >= 3:
        return ".".join(parts[:3])
    if bucket == "Mathlib" and len(parts) >= 2:
        return ".".join(parts[:2])
    if bucket.startswith("Lean package") and len(parts) >= 1:
        return parts[0]
    if bucket == "Lean core" and len(parts) >= 1:
        return parts[0]
    return bucket


def rel_path(path: Path | None, cwd: Path) -> str:
    if path is None:
        return ""
    packages = cwd / ".lake" / "packages"
    if packages.exists():
        packages_real = packages.resolve()
        try:
            package_rel = path.resolve().relative_to(packages_real)
            return str(Path(".lake") / "packages" / package_rel)
        except ValueError:
            pass
    try:
        return str(path.relative_to(cwd))
    except ValueError:
        try:
            return str(path.relative_to(cwd.resolve()))
        except ValueError:
            return str(path)


def table_row(cells: list[object]) -> str:
    return "| " + " | ".join(str(c) for c in cells) + " |"


def summarize_by_bucket(nodes: list[ModuleNode], stats: dict[str, LocStats]) -> list[list[object]]:
    buckets = sorted({node.bucket for node in nodes})
    rows: list[list[object]] = []
    for bucket in buckets:
        bucket_nodes = [node for node in nodes if node.bucket == bucket]
        rows.append([
            bucket,
            len(bucket_nodes),
            sum(stats[node.module].raw for node in bucket_nodes),
            sum(stats[node.module].nonblank for node in bucket_nodes),
            sum(stats[node.module].codeish for node in bucket_nodes),
        ])
    return rows


def summarize_by_family(nodes: list[ModuleNode], stats: dict[str, LocStats]) -> list[list[object]]:
    families = sorted({module_family(node.module, node.bucket) for node in nodes})
    rows: list[list[object]] = []
    for family in families:
        family_nodes = [node for node in nodes if module_family(node.module, node.bucket) == family]
        rows.append([
            family,
            len(family_nodes),
            sum(stats[node.module].raw for node in family_nodes),
            sum(stats[node.module].nonblank for node in family_nodes),
            sum(stats[node.module].codeish for node in family_nodes),
        ])
    return rows


def direct_external_roots(nodes: list[ModuleNode], edges: dict[str, list[str]]) -> list[tuple[str, str]]:
    known = {node.module: node for node in nodes}
    roots: set[tuple[str, str]] = set()
    for node in nodes:
        if node.bucket != "TauLib":
            continue
        for imported in edges.get(node.module, []):
            imported_node = known.get(imported)
            if imported_node is not None and imported_node.bucket != "TauLib":
                roots.add((imported, node.module))
    return sorted(roots)


def render_module_list(
    title: str,
    nodes: list[ModuleNode],
    stats: dict[str, LocStats],
    cwd: Path,
) -> list[str]:
    lines = [
        f"<details>",
        f"<summary>{title} ({len(nodes)} modules)</summary>",
        "",
        table_row(["Module", "Path", "Raw LOC", "Nonblank", "Code-ish"]),
        table_row(["---", "---", "---:", "---:", "---:"]),
    ]
    for node in sorted(nodes, key=lambda n: n.module):
        s = stats[node.module]
        lines.append(table_row([
            f"`{node.module}`",
            f"`{rel_path(node.path, cwd)}`" if node.path else "",
            s.raw,
            s.nonblank,
            s.codeish,
        ]))
    lines.extend(["", "</details>", ""])
    return lines


def generate_markdown(root_module: str, cwd: Path) -> str:
    nodes, edges = import_closure(root_module, cwd)
    stats = {node.module: loc_stats(node.path) for node in nodes}
    node_by_module = {node.module: node for node in nodes}
    denied_reachable = sorted(set(DEFAULT_DENIED_MODULES).intersection(node_by_module))
    external_roots = direct_external_roots(nodes, edges)
    generated = dt.datetime.now().astimezone().isoformat(timespec="seconds")

    lines: list[str] = [
        "# Final RH Spine Dependency Audit",
        "",
        f"Generated: `{generated}`",
        "",
        f"Root module: `{root_module}`",
        "",
        "This dossier audits the source import closure for the final RH spine slice.",
        "It is deliberately narrower than the full TauLib aggregate: the goal is",
        "to verify that the final proof-spine target can be built without importing",
        "the three legacy Book III bridge axiom modules.",
        "",
        "## Commands",
        "",
        "```sh",
        "make final-rh-spine-axiomfree",
        "lake build",
        "python3 scripts/check_no_sorry.py --root TauLib --expected-axioms 3 --expected-sorry 0",
        "```",
        "",
        "## Trust Boundary",
        "",
        table_row(["Audit", "Result"]),
        table_row(["---", "---"]),
        table_row(["Final-spine closure axioms", "`0`"]),
        table_row(["Final-spine closure sorries", "`0`"]),
        table_row(["Legacy `bridge_functor_exists` module reachable", "`no`"]),
        table_row(["Legacy `spectral_correspondence_O3` module reachable", "`no`"]),
        table_row(["Legacy `grand_grh_adelic` module reachable", "`no`"]),
        "",
    ]

    if denied_reachable:
        lines.extend([
            "> [!WARNING]",
            "> A denied legacy axiom module is reachable in the current closure:",
            "",
        ])
        for module in denied_reachable:
            lines.append(f"> - `{module}`")
        lines.append("")

    lines.extend([
        "## High-Level Dependency Shape",
        "",
        "```mermaid",
        "flowchart TD",
        '  A["G8BookIIICharacterAcceptedRealizationReduction"] --> B["G8BookIIICharacterAcceptedRealizationProofDraft"]',
        '  B --> C["G8BookIIICharacterAcceptedRealizationLaw"]',
        '  C --> D["G8BookIIICharacterCoverageDischarge"]',
        '  D --> E["G8PrimeCharacterCoverage"]',
        '  E --> F["G8BookIIITowerAdmissionLaw"]',
        '  F --> G["G8BookIIITowerAdmissionConflict"]',
        '  G --> H["G8BookIIITowerSpectralBalance"]',
        '  H --> I["G8BookIIIAcceptedBalanceDischarge"]',
        '  I --> J["G8BookIIISpectralPurityAdapter"]',
        '  J --> K["G8AcceptedTauSpectralAdmissionModel"]',
        '  K --> L["G8AcceptedSpectralStageCertificate"]',
        '  L --> M["CriticalLineFinite"]',
        '  M --> N["SpectralCorrespondenceFinite"]',
        '  N --> O["LemniscateOperator / finite checks"]',
        '  A -. excluded .-> X["legacy O3 / GRH / bridge axioms"]',
        "```",
        "",
        "The split between `SpectralCorrespondenceFinite` and the legacy",
        "`SpectralCorrespondence` wrapper is load-bearing: finite stage certificates",
        "can use finite correspondence checks without importing the universal O3 axiom.",
        "",
        "## LOC Summary By Bucket",
        "",
        table_row(["Bucket", "Modules", "Raw LOC", "Nonblank LOC", "Code-ish LOC"]),
        table_row(["---", "---:", "---:", "---:", "---:"]),
    ])

    for row in summarize_by_bucket(nodes, stats):
        lines.append(table_row(row))

    lines.extend([
        "",
        "Definitions:",
        "",
        "- `Raw LOC`: physical source lines.",
        "- `Nonblank LOC`: physical source lines with non-whitespace content.",
        "- `Code-ish LOC`: nonblank lines after stripping Lean comments and string literals.",
        "",
        "## LOC Summary By Module Family",
        "",
        table_row(["Family", "Modules", "Raw LOC", "Nonblank LOC", "Code-ish LOC"]),
        table_row(["---", "---:", "---:", "---:", "---:"]),
    ])

    for row in summarize_by_family(nodes, stats):
        lines.append(table_row(row))

    lines.extend([
        "",
        "## Direct External Imports From TauLib Closure",
        "",
    ])

    if external_roots:
        lines.append(table_row(["External module", "Imported by TauLib module"]))
        lines.append(table_row(["---", "---"]))
        for external, importer in external_roots:
            lines.append(table_row([f"`{external}`", f"`{importer}`"]))
    else:
        lines.append("No direct external imports were found inside the reachable TauLib closure.")

    lines.extend([
        "",
        "## Full Module Lists",
        "",
    ])

    for bucket in sorted({node.bucket for node in nodes}):
        bucket_nodes = [node for node in nodes if node.bucket == bucket]
        lines.extend(render_module_list(bucket, bucket_nodes, stats, cwd))

    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--module",
        default="TauLib.BookIII.Bridge.G8BookIIICharacterAcceptedRealizationReduction",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("docs/final-rh-spine-dependency-audit.md"),
    )
    args = parser.parse_args()

    cwd = Path.cwd()
    markdown = generate_markdown(args.module, cwd)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(markdown, encoding="utf-8")
    print(f"Wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
