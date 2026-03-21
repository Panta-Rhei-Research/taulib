#!/usr/bin/env python3
"""Generate TauLib statistics dashboard HTML from registry JSONL and Lean source files.

Usage:
    python3 generate_stats.py --output stats.html --registry-dir ../registry --lean-src TauLib
"""

import json
import os
import re
import argparse
from pathlib import Path
from collections import Counter


BOOK_META = {
    1: ("I",   "Categorical Foundations",  "BookI"),
    2: ("II",  "Categorical Holomorphy",   "BookII"),
    3: ("III", "Categorical Spectrum",     "BookIII"),
    4: ("IV",  "Categorical Microcosm",    "BookIV"),
    5: ("V",   "Categorical Macrocosm",    "BookV"),
    6: ("VI",  "Categorical Life",         "BookVI"),
    7: ("VII", "Categorical Metaphysics",  "BookVII"),
}

SCOPE_COLORS = {
    "established":   "#8fb6ff",      # Book I blue
    "tau-effective":  "#95f3a1",      # Book IV green
    "conjectural":   "#ffb24d",      # Book V amber
    "metaphorical":  "#a9b8d0",      # ink-300 (muted)
    "framework":     "#b28fff",      # accent lavender
}


def load_registry(registry_dir, book_num):
    """Load a book's registry JSONL file."""
    path = Path(registry_dir) / f"book{book_num}_registry.jsonl"
    entries = []
    if not path.exists():
        return entries
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                try:
                    entries.append(json.loads(line))
                except json.JSONDecodeError:
                    pass
    return entries


def scan_lean_dir(lean_src, book_dir):
    """Scan Lean source files for a book and collect statistics."""
    src = Path(lean_src) / book_dir
    stats = {
        "files": 0, "lines": 0, "theorems": 0, "defs": 0,
        "evals": 0, "sorry": 0, "axioms": 0,
        "structures": 0, "examples": 0,
    }
    if not src.exists():
        return stats

    for lean_file in src.rglob("*.lean"):
        stats["files"] += 1
        try:
            content = lean_file.read_text(encoding="utf-8")
        except Exception:
            continue
        lines = content.split("\n")
        stats["lines"] += len(lines)
        for line in lines:
            stripped = line.strip()
            if stripped.startswith(("theorem ", "lemma ", "private theorem ", "private lemma ",
                                    "protected theorem ", "protected lemma ")):
                stats["theorems"] += 1
            elif stripped.startswith(("def ", "noncomputable def ", "private def ", "protected def ")):
                stats["defs"] += 1
            elif stripped.startswith(("#eval ",)):
                stats["evals"] += 1
            elif stripped.startswith(("structure ", "class ", "inductive ")):
                stats["structures"] += 1
            elif stripped.startswith("example "):
                stats["examples"] += 1
            elif ":= sorry" in stripped and not stripped.startswith("--"):
                stats["sorry"] += 1
            elif stripped.startswith("axiom "):
                stats["axioms"] += 1
    return stats


def generate_html(all_stats, all_registry, output_path):
    """Generate the complete stats.html page."""

    # Compute totals
    totals = {k: sum(s[k] for s in all_stats.values()) for k in
              ["files", "lines", "theorems", "defs", "evals", "sorry", "axioms",
               "structures", "examples"]}
    total_registry = sum(len(r) for r in all_registry.values())
    total_formalized = sum(
        sum(1 for e in r if e.get("formalization") == "formalized")
        for r in all_registry.values()
    )

    # Compute per-book registry stats
    book_rows = []
    for bnum in range(1, 8):
        roman, title, bdir = BOOK_META[bnum]
        s = all_stats.get(bnum, {})
        r = all_registry.get(bnum, [])
        n_reg = len(r)
        n_form = sum(1 for e in r if e.get("formalization") == "formalized")
        pct = (n_form / n_reg * 100) if n_reg > 0 else 0

        # Scope breakdown
        scopes = Counter(e.get("scope", "unknown") for e in r)

        # Type breakdown
        types = Counter(e.get("type", "unknown") for e in r)

        book_rows.append({
            "num": bnum, "roman": roman, "title": title,
            "files": s.get("files", 0), "lines": s.get("lines", 0),
            "theorems": s.get("theorems", 0), "defs": s.get("defs", 0),
            "evals": s.get("evals", 0), "sorry": s.get("sorry", 0),
            "axioms": s.get("axioms", 0),
            "registry": n_reg, "formalized": n_form, "pct": pct,
            "scopes": scopes, "types": types,
        })

    # Build HTML
    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>TauLib &mdash; Statistics Dashboard</title>
<style>
  @font-face {{
    font-family: 'Manrope';
    src: url('fonts/manrope-latin.woff2') format('woff2');
    font-weight: 400 800;
    font-display: swap;
    unicode-range: U+0000-00FF, U+0131, U+0152-0153, U+02BB-02BC, U+02C6,
                   U+02DA, U+02DC, U+0304, U+0308, U+0329, U+2000-206F,
                   U+20AC, U+2122, U+2191, U+2193, U+2212, U+2215, U+FEFF, U+FFFD;
  }}
  @font-face {{
    font-family: 'Manrope';
    src: url('fonts/manrope-latin-ext.woff2') format('woff2');
    font-weight: 400 800;
    font-display: swap;
    unicode-range: U+0100-02AF, U+0304, U+0308, U+0329, U+1E00-1E9F,
                   U+1EF2-1EFF, U+2020, U+20A0-20AB, U+20AD-20C0, U+2113,
                   U+2C60-2C7F, U+A720-A7FF;
  }}

  :root {{
    --pr-bg: #f7f4ee;
    --pr-surface: #ffffff;
    --pr-text: #121a2a;
    --pr-text-muted: #32415b;
    --pr-accent: #b28fff;
    --pr-accent-soft: rgba(178, 143, 255, 0.06);
    --pr-border: #dce5f2;
    --pr-header-bg: #09101d;
    --pr-header-text: #f6fbff;
    --pr-bar-track: #dce5f2;
    --pr-shadow: 0 4px 16px rgba(18, 26, 42, 0.08);
    --pr-transition: 200ms cubic-bezier(.22, 1, .36, 1);
  }}

  @media (prefers-color-scheme: dark) {{
    :root {{
      --pr-bg: #0b1020;
      --pr-surface: #12192b;
      --pr-text: #f6fbff;
      --pr-text-muted: #a9b8d0;
      --pr-accent-soft: rgba(178, 143, 255, 0.12);
      --pr-border: #172033;
      --pr-header-bg: #03060f;
      --pr-bar-track: #172033;
      --pr-shadow: 0 4px 16px rgba(0, 0, 0, 0.4);
    }}
  }}

  *, *::before, *::after {{ box-sizing: border-box; }}

  body {{
    font-family: 'Manrope', system-ui, -apple-system, "Segoe UI", sans-serif;
    max-width: 900px;
    margin: 0 auto;
    padding: 2em 1em;
    background: var(--pr-bg);
    color: var(--pr-text);
    line-height: 1.6;
    letter-spacing: -0.01em;
    -webkit-font-smoothing: antialiased;
    -moz-osx-font-smoothing: grayscale;
    animation: pr-fade-in 400ms ease-out;
  }}
  @keyframes pr-fade-in {{ from {{ opacity: 0; transform: translateY(6px); }} to {{ opacity: 1; transform: none; }} }}

  a {{ color: var(--pr-accent); text-decoration-thickness: 1px; text-underline-offset: 2px; transition: opacity var(--pr-transition); }}
  a:hover {{ opacity: 0.8; }}

  h1 {{
    border-bottom: 3px solid transparent;
    border-image: linear-gradient(90deg, #7fb3ff, #b28fff, #80ebff, #8ff0b0, #ffbd58, #ff6b62) 1;
    padding-bottom: 0.3em;
    font-weight: 700;
  }}
  h2 {{ margin-top: 2em; color: var(--pr-text); font-weight: 700; }}

  table {{ border-collapse: collapse; width: 100%; margin: 1em 0; }}
  th {{ background: var(--pr-header-bg); color: var(--pr-header-text); padding: 8px 12px; text-align: left; font-weight: 600; font-size: 0.9em; letter-spacing: 0.02em; }}
  th:first-child {{ border-radius: 8px 0 0 0; }}
  th:last-child {{ border-radius: 0 8px 0 0; }}
  td {{ padding: 6px 12px; border-bottom: 1px solid var(--pr-border); transition: background var(--pr-transition); }}
  tr:hover td {{ background: var(--pr-accent-soft); }}

  .num {{ text-align: right; font-variant-numeric: tabular-nums; }}
  .bar-container {{ width: 100%; background: var(--pr-bar-track); border-radius: 999px; height: 20px; position: relative; overflow: hidden; }}
  .bar-fill {{ height: 100%; border-radius: 999px; background: linear-gradient(90deg, #7fb3ff, #b28fff); transition: width 0.4s cubic-bezier(.22, 1, .36, 1); }}
  .bar-label {{ position: absolute; right: 8px; top: 1px; font-size: 0.8em; color: var(--pr-text); font-weight: 600; }}
  .scope-dot {{ display: inline-block; width: 10px; height: 10px; border-radius: 50%; margin-right: 4px; vertical-align: middle; }}

  .overview-grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(180px, 1fr)); gap: 12px; margin: 1em 0; }}
  .overview-card {{
    background: var(--pr-surface);
    border: 1px solid var(--pr-border);
    border-radius: 12px;
    padding: 20px 16px;
    text-align: center;
    box-shadow: var(--pr-shadow);
    transition: transform var(--pr-transition), box-shadow var(--pr-transition);
  }}
  .overview-card:hover {{ transform: translateY(-2px); }}
  .overview-card .value {{ font-size: 2em; font-weight: 700; color: var(--pr-accent); }}
  .overview-card .label {{ font-size: 0.85em; color: var(--pr-text-muted); margin-top: 4px; }}

  .sorry-zero {{ color: #95f3a1; font-weight: 700; }}
  .sorry-nonzero {{ color: #ffb24d; }}

  .total-row {{ font-weight: 700; }}
  .total-row td {{ border-top: 2px solid var(--pr-header-bg); }}

  footer {{ margin-top: 3em; padding-top: 1em; border-top: 1px solid var(--pr-border); color: var(--pr-text-muted); font-size: 0.85em; text-align: center; }}
  footer a {{ color: var(--pr-text-muted); }}
</style>
</head>
<body>

<h1>TauLib &mdash; Statistics Dashboard</h1>
<p><a href="index.html">&larr; Back to documentation</a></p>

<div class="overview-grid">
  <div class="overview-card">
    <div class="value">{totals['files']}</div>
    <div class="label">Lean Modules</div>
  </div>
  <div class="overview-card">
    <div class="value">{totals['lines']:,}</div>
    <div class="label">Lines of Code</div>
  </div>
  <div class="overview-card">
    <div class="value">{totals['theorems']:,}</div>
    <div class="label">Theorems &amp; Lemmas</div>
  </div>
  <div class="overview-card">
    <div class="value">{totals['defs']:,}</div>
    <div class="label">Definitions</div>
  </div>
  <div class="overview-card">
    <div class="value">{totals['evals']:,}</div>
    <div class="label"><code>#eval</code> Computations</div>
  </div>
  <div class="overview-card">
    <div class="value">{total_registry:,}</div>
    <div class="label">Registry Entries</div>
  </div>
  <div class="overview-card">
    <div class="value">{total_formalized:,}</div>
    <div class="label">Formalized</div>
  </div>
  <div class="overview-card">
    <div class="value">{totals['sorry']}</div>
    <div class="label">Sorry (Book VII only)</div>
  </div>
</div>

<h2>Per-Book Breakdown</h2>

<table>
<tr>
  <th>Book</th>
  <th class="num">Modules</th>
  <th class="num">Lines</th>
  <th class="num">Theorems</th>
  <th class="num">Defs</th>
  <th class="num">#eval</th>
  <th class="num">Axioms</th>
  <th class="num">Sorry</th>
</tr>
"""
    for b in book_rows:
        sorry_cls = "sorry-zero" if b["sorry"] == 0 else "sorry-nonzero"
        html += f"""<tr>
  <td><strong>{b['roman']}</strong> &mdash; {b['title']}</td>
  <td class="num">{b['files']}</td>
  <td class="num">{b['lines']:,}</td>
  <td class="num">{b['theorems']:,}</td>
  <td class="num">{b['defs']:,}</td>
  <td class="num">{b['evals']:,}</td>
  <td class="num">{b['axioms']}</td>
  <td class="num {sorry_cls}">{b['sorry']}</td>
</tr>
"""
    html += f"""<tr class="total-row">
  <td>Total</td>
  <td class="num">{totals['files']}</td>
  <td class="num">{totals['lines']:,}</td>
  <td class="num">{totals['theorems']:,}</td>
  <td class="num">{totals['defs']:,}</td>
  <td class="num">{totals['evals']:,}</td>
  <td class="num">{totals['axioms']}</td>
  <td class="num">{totals['sorry']}</td>
</tr>
</table>

<h2>Registry Formalization Coverage</h2>

<table>
<tr>
  <th>Book</th>
  <th class="num">Registry</th>
  <th class="num">Formalized</th>
  <th style="min-width: 200px;">Coverage</th>
</tr>
"""
    for b in book_rows:
        html += f"""<tr>
  <td><strong>{b['roman']}</strong> &mdash; {b['title']}</td>
  <td class="num">{b['registry']:,}</td>
  <td class="num">{b['formalized']:,}</td>
  <td>
    <div class="bar-container">
      <div class="bar-fill" style="width: {b['pct']:.1f}%;"></div>
      <span class="bar-label">{b['pct']:.1f}%</span>
    </div>
  </td>
</tr>
"""
    total_pct = (total_formalized / total_registry * 100) if total_registry > 0 else 0
    html += f"""<tr class="total-row">
  <td>Total</td>
  <td class="num">{total_registry:,}</td>
  <td class="num">{total_formalized:,}</td>
  <td>
    <div class="bar-container">
      <div class="bar-fill" style="width: {total_pct:.1f}%;"></div>
      <span class="bar-label">{total_pct:.1f}%</span>
    </div>
  </td>
</tr>
</table>

<h2>Scope Distribution</h2>

<table>
<tr>
  <th>Book</th>
"""
    for scope, color in SCOPE_COLORS.items():
        html += f'  <th class="num"><span class="scope-dot" style="background:{color}"></span>{scope}</th>\n'
    html += "</tr>\n"

    for b in book_rows:
        html += f'<tr>\n  <td><strong>{b["roman"]}</strong></td>\n'
        for scope in SCOPE_COLORS:
            count = b["scopes"].get(scope, 0)
            html += f'  <td class="num">{count}</td>\n'
        html += "</tr>\n"

    # Totals row
    html += '<tr class="total-row">\n  <td>Total</td>\n'
    for scope in SCOPE_COLORS:
        total = sum(b["scopes"].get(scope, 0) for b in book_rows)
        html += f'  <td class="num">{total}</td>\n'
    html += "</tr>\n</table>\n"

    html += f"""
<h2>Registry Type Distribution</h2>

<table>
<tr>
  <th>Book</th>
  <th class="num">Theorem</th>
  <th class="num">Definition</th>
  <th class="num">Proposition</th>
  <th class="num">Remark</th>
  <th class="num">Lemma</th>
  <th class="num">Corollary</th>
  <th class="num">Other</th>
</tr>
"""
    type_keys = ["theorem", "definition", "proposition", "remark", "lemma", "corollary"]
    for b in book_rows:
        html += f'<tr>\n  <td><strong>{b["roman"]}</strong></td>\n'
        counted = 0
        for tk in type_keys:
            c = b["types"].get(tk, 0)
            counted += c
            html += f'  <td class="num">{c}</td>\n'
        other = b["registry"] - counted
        html += f'  <td class="num">{other}</td>\n</tr>\n'

    html += "</table>\n"

    html += """
<footer>
  <p>Generated by <code>scripts/generate_stats.py</code> from registry JSONL and Lean source files.</p>
  <p><a href="index.html">&larr; Back to documentation</a></p>
</footer>

</body>
</html>
"""

    Path(output_path).parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        f.write(html)
    print(f"Statistics dashboard written to {output_path}")


def main():
    parser = argparse.ArgumentParser(description="Generate TauLib statistics dashboard")
    parser.add_argument("--output", default="stats.html", help="Output HTML file path")
    parser.add_argument("--registry-dir", required=True, help="Path to registry/ directory with JSONL files")
    parser.add_argument("--lean-src", required=True, help="Path to TauLib/ Lean source directory")
    args = parser.parse_args()

    print("Loading registry files...")
    all_registry = {}
    for bnum in range(1, 8):
        entries = load_registry(args.registry_dir, bnum)
        all_registry[bnum] = entries
        print(f"  Book {bnum}: {len(entries)} entries")

    print("Scanning Lean source files...")
    all_stats = {}
    for bnum in range(1, 8):
        _, _, bdir = BOOK_META[bnum]
        stats = scan_lean_dir(args.lean_src, bdir)
        all_stats[bnum] = stats
        print(f"  {bdir}: {stats['files']} files, {stats['lines']:,} lines, "
              f"{stats['theorems']} theorems, {stats['sorry']} sorry")

    print("Generating HTML...")
    generate_html(all_stats, all_registry, args.output)


if __name__ == "__main__":
    main()
