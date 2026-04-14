#!/usr/bin/env python3
"""Extract doc-gen4 module pages into Jekyll collection files.

Reads each TauLib module HTML page from the filtered doc-gen4 output,
extracts the <main> content, and writes a Jekyll-compatible .html file
with YAML front matter into the site/_taulib_docs/ directory.

Usage:
    python3 scripts/extract_docs.py --input _docgen_output --output site/_taulib_docs

Each output file gets:
  - layout: taulib-doc
  - title: module name (from <title> or path)
  - module_name: full qualified name
  - book: roman numeral (I-VII) or "Tour"
  - book_label: human-readable label
  - permalink: /docs/{slug}/
  - right_rail metadata
  - The raw <main> content as the page body
"""

import argparse
import os
import re
from pathlib import Path

BOOK_LABELS = {
    "I": "Foundations",
    "II": "Holomorphy",
    "III": "Spectrum",
    "IV": "Microcosm",
    "V": "Macrocosm",
    "VI": "Life",
    "VII": "Metaphysics",
    "Tour": "Guided Tours",
}

ROMAN_MAP = {
    "BookI": "I", "BookII": "II", "BookIII": "III",
    "BookIV": "IV", "BookV": "V", "BookVI": "VI", "BookVII": "VII",
    "Tour": "Tour",
}


def extract_title(html: str) -> str:
    """Extract page title from <title> or <h1>."""
    m = re.search(r'<title>(.*?)</title>', html, re.DOTALL)
    if m:
        title = m.group(1).strip()
        title = re.sub(r'\s*[-–—]\s*(doc-gen4|TauLib).*$', '', title)
        if title:
            return title
    m = re.search(r'<h1[^>]*>(.*?)</h1>', html, re.DOTALL)
    if m:
        return re.sub(r'<[^>]+>', '', m.group(1)).strip()
    return "TauLib"


def extract_main(html: str) -> str:
    """Extract inner content of <main>."""
    m = re.search(r'<main[^>]*>(.*?)</main>', html, re.DOTALL)
    if m:
        return m.group(1).strip()
    m = re.search(r'<div\s+class="main"[^>]*>(.*?)</div>\s*(?:</body>|$)', html, re.DOTALL)
    if m:
        return m.group(1).strip()
    return html


def path_to_module_info(rel_path: str) -> dict:
    """Derive book, module_name, and slug from a relative file path.

    Example: TauLib/BookI/Kernel/Signature.html
    → book="I", module_name="TauLib.BookI.Kernel.Signature", slug="book-i-kernel-signature"
    """
    parts = Path(rel_path).with_suffix('').parts  # ('TauLib', 'BookI', 'Kernel', 'Signature')

    # Determine book
    book = "Tour"
    if len(parts) >= 2:
        book = ROMAN_MAP.get(parts[1], "Tour")

    # Full module name
    module_name = ".".join(parts)  # TauLib.BookI.Kernel.Signature

    # Slug for permalink
    slug_parts = [p.lower() for p in parts[1:]]  # skip 'TauLib' prefix
    slug = "-".join(slug_parts)
    # Clean up: booki → book-i, etc.
    slug = re.sub(r'book([ivx]+)', lambda m: f'book-{m.group(1)}', slug)

    return {
        "book": book,
        "book_label": BOOK_LABELS.get(book, ""),
        "module_name": module_name,
        "slug": slug,
    }


def write_jekyll_file(output_dir: Path, info: dict, title: str, content: str):
    """Write a Jekyll collection .html file with YAML front matter."""
    front_matter = f"""---
layout: taulib-doc
title: "{title}"
module_name: "{info['module_name']}"
book: "{info['book']}"
book_label: "{info['book_label']}"
permalink: /docs/{info['slug']}/
right_rail:
  artifacts:
    - title: Source on GitHub
      url: https://github.com/Panta-Rhei-Framework/taulib
      external: true
  meta:
    type: "API Documentation"
    book: "Book {info['book']}"
    status: "Canonical"
    updated: "April 2026"
---
"""
    filepath = output_dir / f"{info['slug']}.html"
    filepath.write_text(front_matter + content, encoding="utf-8")
    return filepath


def main():
    parser = argparse.ArgumentParser(
        description="Extract doc-gen4 HTML into Jekyll collection files"
    )
    parser.add_argument("--input", default="_docgen_output",
                        help="Filtered doc-gen4 output directory")
    parser.add_argument("--output", default="site/_taulib_docs",
                        help="Jekyll collection output directory")
    args = parser.parse_args()

    input_dir = Path(args.input).resolve()
    output_dir = Path(args.output).resolve()

    taulib_dir = input_dir / "TauLib"
    if not taulib_dir.exists():
        print(f"ERROR: TauLib/ not found in {input_dir}")
        raise SystemExit(1)

    output_dir.mkdir(parents=True, exist_ok=True)

    # Clear existing collection files
    for f in output_dir.glob("*.html"):
        f.unlink()

    print("=" * 60)
    print("Extracting doc-gen4 modules → Jekyll collection")
    print("=" * 60)
    print(f"Input:  {input_dir}")
    print(f"Output: {output_dir}")
    print()

    count = 0
    for filepath in sorted(taulib_dir.rglob("*.html")):
        rel = filepath.relative_to(input_dir)
        html = filepath.read_text(encoding="utf-8")

        title = extract_title(html)
        content = extract_main(html)
        info = path_to_module_info(str(rel))

        write_jekyll_file(output_dir, info, title, content)
        count += 1

        if count <= 5 or count % 50 == 0:
            print(f"  Extracted: {rel} → {info['slug']}.html")

    print()
    print(f"Extracted {count} modules to {output_dir}")
    print("=" * 60)


if __name__ == "__main__":
    main()
