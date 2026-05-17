#!/usr/bin/env python3
"""Generate TauLib OG / social-preview cards.

Mirrors the panta-rhei.site canonical OG card design (dark Panta Blue
gradient, spectrum strip, π ρ wordmark + "Panta Rhei Research" attribution
in the top-right) and substitutes the lowercase τ (tau) glyph as TauLib's
large visual centerpiece — the standard sub-brand mark for everything
TauLib-related.

Outputs (1200 × 630 each):

  assets/og/svg/og-default.svg     →  assets/og-image.png          site-wide fallback
  assets/og/svg/og-docs.svg        →  assets/og/png/og-docs.png    /docs/ override
  assets/og/svg/og-github.svg      →  .github/social-preview.png   GitHub repo Settings upload

Run from the site/ directory (or anywhere — paths are resolved relative
to the script location). Requires `rsvg-convert` on PATH.

    cd site/
    python3 scripts/generate_og_images.py

"""
from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path

# Paths -----------------------------------------------------------------
SCRIPT_DIR = Path(__file__).resolve().parent          # site/scripts
SITE_ROOT  = SCRIPT_DIR.parent                        # site/
ASSETS     = SITE_ROOT / "assets" / "og"
SVG_DIR    = ASSETS / "svg"
PNG_DIR    = ASSETS / "png"
LOCKUP_DIR = ASSETS / "lockup"
SITE_ROOT_PNG = SITE_ROOT / "assets" / "og-image.png"  # site-wide fallback consumed by head.html
REPO_ROOT  = SITE_ROOT.parent                          # taulib/
GH_PREVIEW = REPO_ROOT / ".github" / "social-preview.png"

# Canonical brand lockup — used as the corner mark on every TauLib OG card.
# Vendored from atlas/design/logo/logo-ug-images{,-light}.svg.
LOCKUP_DARK_PATH  = LOCKUP_DIR / "logo-lockup-dark.svg"
LOCKUP_LIGHT_PATH = LOCKUP_DIR / "logo-lockup-light.svg"
# Lockup viewBox is 2128 × 1074 (aspect ratio ≈ 1.98 : 1).
LOCKUP_VIEWBOX_W = 2128
LOCKUP_VIEWBOX_H = 1074

# Brand tokens (mirrors panta-rhei v4 OG card) -------------------------
CARD_W, CARD_H = 1200, 630
BG_GRAD_STOPS = [
    (0.00, "#13395E"),
    (0.48, "#163E64"),
    (1.00, "#1A4874"),
]
SPECTRUM_STOPS = [
    (0.00, "#5A7EB3"),
    (0.34, "#1B8278"),
    (0.68, "#9F5B5C"),
    (1.00, "#896092"),
]
TITLE_COLOR     = "#F8FAF7"
SUBTITLE_COLOR  = "#D8E3EC"
URL_COLOR       = "#B9CFE2"
PILL_FILL       = "#F8FAF7"
PILL_TEXT       = "#163E64"
TAU_COLOR       = "#F8FAF7"        # white τ on dark
TAU_OPACITY     = "0.22"           # subtle watermark intensity

# Per-card config ------------------------------------------------------
CARDS = {
    "og-default": {
        "pill":     "LEAN 4 FORMALIZATION",
        "title":    "TauLib",
        "subtitle": [
            "Lean 4 formalization layer of the",
            "Panta Rhei Research Program.",
        ],
        "url":      "taulib.site",
        "outputs":  ["assets/og-image.png"],  # site-wide fallback
    },
    "og-docs": {
        "pill":     "API DOCUMENTATION",
        "title":    "TauLib",
        "subtitle": [
            "Generated Lean 4 module documentation",
            "organized by book and subject area.",
        ],
        "url":      "taulib.site/docs",
        "outputs":  ["assets/og/png/og-docs.png"],
    },
    "og-github": {
        "pill":     "LEAN 4 FORMALIZATION",
        "title":    "TauLib",
        "subtitle": [
            "Public Lean 4 formalization repo",
            "of the Panta Rhei Research Program.",
        ],
        "url":      "github.com/Panta-Rhei-Research/taulib",
        "outputs":  [],  # not under site/, written explicitly to repo .github/
    },
}


# SVG template ----------------------------------------------------------
def _gradient_xml(grad_id: str, stops, x2: int = 0, y2: int = 630, x1: int = 0, y1: int = 0) -> str:
    stops_xml = "".join(f'<stop offset="{int(o*100)}%" stop-color="{c}"/>' for o, c in stops)
    return (
        f'<linearGradient id="{grad_id}" x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" '
        f'gradientUnits="userSpaceOnUse">{stops_xml}</linearGradient>'
    )


def _load_lockup_inner(svg_path: Path) -> str:
    """Read a vendored brand lockup and strip the outer `<svg>` wrapper.

    The lockup SVGs from atlas/design/logo/ wrap their content in a single
    `<svg viewBox="0 0 2128 1074" ...>...</svg>` root. To re-embed the
    content inside another SVG, we extract the inner part and let the
    caller place it inside a nested `<svg x=".." y=".." width=".." height=".."
    viewBox="0 0 2128 1074">...inner...</svg>` block.
    """
    text = svg_path.read_text(encoding="utf-8")
    # Drop the XML/DOCTYPE prolog and the outer <svg ...> open tag.
    body = re.sub(r"^.*?<svg[^>]*>", "", text, count=1, flags=re.DOTALL)
    # Drop the closing </svg>.
    body = re.sub(r"</svg>\s*$", "", body, count=1, flags=re.DOTALL)
    return body.strip()


LOCKUP_DARK_INNER = _load_lockup_inner(LOCKUP_DARK_PATH)


def render_svg(*, pill: str, title: str, subtitle: list[str], url: str, **_) -> str:
    """Return the SVG source for a TauLib OG card.

    Visual structure (mirrors panta-rhei.site/assets/og/svg/index.svg
    with τ glyph as the centerpiece and the official Panta Rhei brand
    lockup as the corner mark):

      ┌────────────────────────────────────────────────┐
      │ ┌─────────────┐               ┌──────────────┐ │
      │ │   PILL      │               │  π ρ  PANTA  │ │  ← official
      │ └─────────────┘               │       RHEI   │ │     lockup
      │                               │   RESEARCH   │ │     (dark
      │                               │   PROGRAM    │ │     variant)
      │                               └──────────────┘ │
      │                                                │
      │                                       τ        │  ← large τ
      │  Title (EB Garamond, 112pt)                    │     centerpiece
      │  Subtitle (Source Sans 3, 34pt)                │
      │                                                │
      │  url (Source Code Pro, 30pt)                   │
      └────────────────────────────────────────────────┘
      ▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓ ← 12px spectrum strip
    """
    # Subtitle: wrap into <tspan>s.
    subtitle_lines = "".join(
        f'<tspan x="82" y="{474 + i * 42}">{line}</tspan>'
        for i, line in enumerate(subtitle)
    )
    # Pill width adapts to text length (rough heuristic: ~13px per char + 36px padding).
    pill_w = 36 + len(pill) * 13

    # Brand lockup positioning in the top-right.
    # 2128 × 1074 viewBox scaled to 380 × 191.8 — sits comfortably above the title.
    lockup_w = 380
    lockup_h = round(lockup_w * LOCKUP_VIEWBOX_H / LOCKUP_VIEWBOX_W, 2)  # ≈ 191.81
    lockup_x = CARD_W - lockup_w - 50
    lockup_y = 40

    return f"""<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="{CARD_W}" height="{CARD_H}" viewBox="0 0 {CARD_W} {CARD_H}" role="img" aria-label="TauLib — Panta Rhei Research Program preview card for {title}.">
  <defs>
    <style>
      @font-face {{ font-family: "EB Garamond OG"; src: url("../fonts-local/EBGaramond-Regular.ttf"); }}
      @font-face {{ font-family: "Source Sans 3 OG"; src: url("../fonts-local/SourceSans3-Regular.ttf"); }}
      @font-face {{ font-family: "Source Code Pro OG"; src: url("../fonts-local/SourceCodePro-Regular.ttf"); }}
    </style>
    {_gradient_xml("panta-og-dark", BG_GRAD_STOPS, x2=CARD_W, y2=CARD_H)}
    {_gradient_xml("spectrum-rule", SPECTRUM_STOPS, x2=CARD_W, y2=0)}
  </defs>

  <!-- Background: Panta Blue diagonal gradient. -->
  <rect width="{CARD_W}" height="{CARD_H}" fill="url(#panta-og-dark)"/>

  <!-- Bottom 12px spectrum strip — TauLib inherits the canonical Panta Rhei brand signature. -->
  <rect x="0" y="618" width="{CARD_W}" height="12" fill="url(#spectrum-rule)"/>

  <!-- Large τ watermark: TauLib's standard sub-brand mark.
       EB Garamond italic for elegance; sits in the right half, below the
       brand lockup so the two marks read as a stacked composition rather
       than overlapping. -->
  <text x="970" y="585" font-family="EB Garamond OG, Georgia, serif" font-size="430" font-style="italic" font-weight="400" fill="{TAU_COLOR}" opacity="{TAU_OPACITY}" text-anchor="middle" aria-hidden="true">τ</text>

  <!-- Top-right: official Panta Rhei brand lockup (dark variant).
       Vendored from atlas/design/logo/logo-ug-images.svg. -->
  <svg x="{lockup_x}" y="{lockup_y}" width="{lockup_w}" height="{lockup_h}" viewBox="0 0 {LOCKUP_VIEWBOX_W} {LOCKUP_VIEWBOX_H}" preserveAspectRatio="xMidYMid meet" aria-label="Panta Rhei Research Program">
    {LOCKUP_DARK_INNER}
  </svg>

  <!-- Top-left pill: category label (LEAN 4 FORMALIZATION etc.). -->
  <g transform="translate(70 76)">
    <rect width="{pill_w}" height="44" rx="22" fill="{PILL_FILL}" opacity="0.96"/>
    <text x="18" y="29" font-family="Source Code Pro OG, ui-monospace, monospace" font-size="19" font-weight="700" letter-spacing="1.8" fill="{PILL_TEXT}">{pill}</text>
  </g>

  <!-- Primary title (EB Garamond, large). -->
  <text font-family="EB Garamond OG, Georgia, serif" font-size="112" font-weight="400" fill="{TITLE_COLOR}">
    <tspan x="78" y="320">{title}</tspan>
  </text>

  <!-- Subtitle (Source Sans 3). -->
  <text font-family="Source Sans 3 OG, Inter, Arial, sans-serif" font-size="34" font-weight="400" fill="{SUBTITLE_COLOR}">
    {subtitle_lines}
  </text>

  <!-- Bottom-left URL anchor (Source Code Pro). -->
  <text x="82" y="582" font-family="Source Code Pro OG, ui-monospace, monospace" font-size="30" font-weight="500" fill="{URL_COLOR}">{url}</text>
</svg>
"""


# Rasterizer ------------------------------------------------------------
def rasterize(svg_path: Path, png_path: Path) -> None:
    """Rasterize SVG → PNG via rsvg-convert at 1200×630."""
    png_path.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        [
            "rsvg-convert",
            "-w", str(CARD_W),
            "-h", str(CARD_H),
            "-f", "png",
            "-o", str(png_path),
            str(svg_path),
        ],
        check=True,
    )


# Main ------------------------------------------------------------------
def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--skip-png", action="store_true", help="Write SVGs only, skip rasterization.")
    args = parser.parse_args()

    if not args.skip_png and not shutil.which("rsvg-convert"):
        print("error: rsvg-convert not on PATH (install librsvg)", file=sys.stderr)
        return 1

    SVG_DIR.mkdir(parents=True, exist_ok=True)
    PNG_DIR.mkdir(parents=True, exist_ok=True)
    GH_PREVIEW.parent.mkdir(parents=True, exist_ok=True)

    for card_id, cfg in CARDS.items():
        svg_path = SVG_DIR / f"{card_id}.svg"
        svg_path.write_text(render_svg(**cfg))
        print(f"wrote  {svg_path.relative_to(REPO_ROOT)}")

        if args.skip_png:
            continue

        if card_id == "og-github":
            rasterize(svg_path, GH_PREVIEW)
            print(f"wrote  {GH_PREVIEW.relative_to(REPO_ROOT)}")
            continue

        for out_rel in cfg["outputs"]:
            out_path = SITE_ROOT / out_rel
            rasterize(svg_path, out_path)
            print(f"wrote  site/{out_rel}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
