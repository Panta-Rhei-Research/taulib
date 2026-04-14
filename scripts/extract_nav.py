#!/usr/bin/env python3
"""Extract doc-gen4 navbar into Jekyll YAML data file.

Parses the TauLib-filtered navbar.html and outputs a structured YAML
file for use in Jekyll Liquid templates (left-rail module navigation).

Usage:
    python3 scripts/extract_nav.py --input _docgen_output/navbar.html --output site/_data/nav_modules.yml
"""

import argparse
import re
import yaml
from pathlib import Path

ROMAN_MAP = {
    "BookI": "I", "BookII": "II", "BookIII": "III",
    "BookIV": "IV", "BookV": "V", "BookVI": "VI", "BookVII": "VII",
}

BOOK_TITLES = {
    "I": "Categorical Foundations",
    "II": "Categorical Holomorphy",
    "III": "Categorical Spectrum",
    "IV": "Categorical Microcosm",
    "V": "Categorical Macrocosm",
    "VI": "Categorical Life",
    "VII": "Categorical Metaphysics",
}


def html_path_to_jekyll_url(href: str) -> str:
    """Convert doc-gen4 HTML path to Jekyll permalink.

    Example: ./TauLib/BookI/Kernel/Signature.html → /docs/book-i-kernel-signature/
    """
    path = href.replace("./", "").replace("TauLib/", "")
    path = Path(path).with_suffix("")
    parts = [p.lower() for p in path.parts]
    slug = "-".join(parts)
    slug = re.sub(r'book([ivx]+)', lambda m: f'book-{m.group(1)}', slug)
    return f"/docs/{slug}/"


def parse_navbar(html: str) -> dict:
    """Parse the TauLib navbar HTML into a structured dict.

    The navbar has nested <details> elements:
    <details class="nav_sect" data-path="./TauLib.html">
      <summary>TauLib</summary>
      <details class="nav_sect" data-path="./TauLib/BookI.html">
        <summary>BookI</summary>
        <details class="nav_sect" data-path="./TauLib/BookI/Kernel.html">
          <summary>Kernel</summary>
          <div class="nav_link"><a href="./TauLib/BookI/Kernel/Signature.html">Signature</a></div>
          ...
        </details>
      </details>
    </details>
    """
    books = []
    tours = []

    # Find each Book-level <details> section
    book_pattern = re.compile(
        r'<details[^>]*data-path="\.\/TauLib\/(Book[IVX]+)\.html"[^>]*>'
        r'.*?<summary>\s*(Book[IVX]+)\s*</summary>(.*?)(?=<details[^>]*data-path="\.\/TauLib\/Book|'
        r'<details[^>]*data-path="\.\/TauLib\/Tour|</details>\s*</div>\s*</nav>)',
        re.DOTALL
    )

    # Alternative: find all section-level details within the TauLib block
    # Strategy: find the TauLib root, then extract child details blocks
    taulib_block_match = re.search(
        r'data-path="\.\/TauLib\.html".*?<summary>\s*TauLib\s*</summary>(.*)',
        html, re.DOTALL
    )

    if not taulib_block_match:
        print("WARNING: Could not find TauLib root in navbar")
        return {"books": [], "tour": []}

    taulib_content = taulib_block_match.group(1)

    # Extract Book sections
    section_pattern = re.compile(
        r'<details[^>]*data-path="\.\/TauLib\/(Book[IVX]+|Tour)\.html"[^>]*>\s*'
        r'<summary>\s*(Book[IVX]+|Tour)\s*</summary>(.*?)</details>',
        re.DOTALL
    )

    # Use a simpler recursive approach — find all nav_link entries with their paths
    link_pattern = re.compile(
        r'<a\s+href="(\./TauLib/[^"]+\.html)"[^>]*>([^<]+)</a>'
    )

    # Build a tree from all links
    all_links = link_pattern.findall(taulib_content)

    # Group by book and section
    book_sections = {}  # book_key -> section_name -> [(name, url)]
    tour_entries = []

    for href, name in all_links:
        # Parse path: ./TauLib/BookI/Kernel/Signature.html
        path_parts = href.replace("./TauLib/", "").replace(".html", "").split("/")

        if len(path_parts) < 2:
            continue  # Skip root-level (BookI.html etc.)

        book_key = path_parts[0]  # BookI, BookII, ..., Tour

        if book_key == "Tour":
            if len(path_parts) >= 2:
                tour_entries.append({
                    "name": name.strip(),
                    "url": html_path_to_jekyll_url(href),
                })
            continue

        roman = ROMAN_MAP.get(book_key)
        if not roman:
            continue

        if roman not in book_sections:
            book_sections[roman] = {}

        section_name = path_parts[1] if len(path_parts) >= 3 else "Root"

        if section_name not in book_sections[roman]:
            book_sections[roman][section_name] = []

        # Module name is the last part
        mod_name = name.strip()
        mod_url = html_path_to_jekyll_url(href)

        book_sections[roman][section_name].append({
            "name": mod_name,
            "url": mod_url,
        })

    # Build ordered output
    for roman in ["I", "II", "III", "IV", "V", "VI", "VII"]:
        if roman not in book_sections:
            continue
        sections = []
        for section_name, modules in sorted(book_sections[roman].items()):
            sections.append({
                "name": section_name,
                "modules": modules,
            })
        books.append({
            "roman": roman,
            "title": BOOK_TITLES.get(roman, ""),
            "sections": sections,
        })

    return {"books": books, "tour": tour_entries}


def main():
    parser = argparse.ArgumentParser(
        description="Extract doc-gen4 navbar into Jekyll YAML data"
    )
    parser.add_argument("--input", default="_docgen_output/navbar.html",
                        help="Filtered navbar.html from doc-gen4")
    parser.add_argument("--output", default="site/_data/nav_modules.yml",
                        help="Jekyll data file output")
    args = parser.parse_args()

    input_path = Path(args.input).resolve()
    output_path = Path(args.output).resolve()

    if not input_path.exists():
        print(f"ERROR: navbar.html not found at {input_path}")
        raise SystemExit(1)

    html = input_path.read_text(encoding="utf-8")
    nav_data = parse_navbar(html)

    output_path.parent.mkdir(parents=True, exist_ok=True)

    with open(output_path, "w", encoding="utf-8") as f:
        yaml.dump(nav_data, f, default_flow_style=False, allow_unicode=True, sort_keys=False)

    # Report
    total_modules = sum(
        len(mod)
        for book in nav_data["books"]
        for section in book["sections"]
        for mod in [section["modules"]]
    )
    total_tours = len(nav_data.get("tour", []))

    print(f"Nav extracted: {len(nav_data['books'])} books, "
          f"{total_modules} modules, {total_tours} tours → {output_path}")


if __name__ == "__main__":
    main()
