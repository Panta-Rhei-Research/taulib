# TauLib Visual Assets

## `social-preview.png` (1280 × 640)

The GitHub repository social preview card — the image that appears when the repo is linked from Twitter/X, Hacker News, LinkedIn, Lean Zulip, and other platforms that follow Open Graph / Twitter-Card metadata.

**Uploaded to GitHub via** Repository → Settings → General → Social preview.

### Design language

- Deep-navy gradient background (`#061221 → #0b1f3a`) matching the author's X profile banner.
- Sparse constellation/network pattern on the right half, biased so the large τ glyph reads as emerging from the network.
- Large serif τ glyph anchoring the right third with a soft radial blue glow.
- Left stack (top → bottom):
  1. Eyebrow label: `PANTA RHEI RESEARCH PROGRAM · LEAN 4`
  2. Title: `TauLib`
  3. Subtitle: *Mechanized Formalization of Category τ*
  4. Upper separator rule (fade-gradient)
  5. Metrics row: `LINES 125,771 · THEOREMS 4,332 · MODULES 450 · AXIOMS 3 · SORRY 0`
  6. Lower separator rule (frames the metrics row symmetrically)
  7. Footer: `taulib.site · github.com/Panta-Rhei-Research/taulib`

### Regenerating after a metrics change

`social-preview.svg` is the source of truth. When the library's numerical metrics change (new theorems, new sorry/axiom state, new module count), edit the five `<text>` elements inside the "Metrics row" group and re-rasterize:

```bash
rsvg-convert -w 1280 -h 640 assets/social-preview.svg -o assets/social-preview.png
```

Then re-upload via Repository → Settings → General → Social preview.

### Typography fallback

The SVG specifies `Inter` (sans) and a Playfair/Caslon/Georgia stack (serif τ). If a rendering host doesn't have these fonts installed, the SVG falls back to Helvetica/Arial and Georgia/Times respectively. The PNG in this directory was pre-rendered with fonts resolved, so the shipped card is font-independent.
