---
layout: default
title: "TauLib"
right_rail:
  related:
    - title: "API Documentation"
      url: /docs/
    - title: "Panta Rhei Research"
      url: https://panta-rhei.site
    - title: "Integrated Docs"
      url: https://panta-rhei.site/verify/taulib/
  artifacts:
    - title: "TauLib GitHub"
      url: https://github.com/Panta-Rhei-Research/taulib
      external: true
  meta:
    type: "Landing"
    status: "Canonical"
    updated: "April 2026"
---

<div class="hero-card">
  <span class="eyebrow">Lean 4 Formalization</span>
  <h1>TauLib</h1>
  <p>Lean 4 formalization layer of the <a href="https://panta-rhei.site">Panta Rhei Research Program</a>.</p>
  <div class="btn-group">
    <a href="https://panta-rhei.site/" class="btn-primary">Open Research Program</a>
    <a href="{{ '/docs/' | relative_url }}" class="btn-secondary">Browse All Modules</a>
    <a href="https://github.com/Panta-Rhei-Research/taulib" class="btn-ghost" target="_blank" rel="noopener">View on GitHub</a>
  </div>
  <p class="hero-supporting-line">450 Lean 4 modules · 125,771 lines · 4,332 machine-checked theorems · 0 sorry across all seven books · 3 custom axioms (all conjectural, all Book III) · Mathlib restricted to proof tactics.</p>
</div>

<div class="content-card" markdown="1">

## About TauLib

TauLib is the Lean 4 formalization layer of the Panta Rhei Research Program. It contains the formal kernel and proof-oriented implementation work that supports the program's public verification surface.

The full public documentation for TauLib also lives inside the [main research-program site](https://panta-rhei.site/verify/taulib/). The [GitHub repository](https://github.com/Panta-Rhei-Research/taulib) remains the live source and community-facing development home.

## Library at a Glance

| Metric | Value |
|--------|------:|
| **Source files** | 450 |
| **Lines of Lean 4** | 125,771 |
| **Theorems & lemmas** | 4,332 |
| **Definitions** | 3,542 |
| **Axioms** | 3 (all conjectural, all Book III) |
| **Sorry** | 0 (all seven books sorry-free) |
| **Mathlib usage** | Tactics only — all math from scratch |

*As of v2.0.0 (2026-04-19, commit `b743f4c`). The 4th axiom `central_theorem_physical : True` was retired in `peer-review-fixes-v1` as a no-op. The three Book VII structural commitments are encoded as `def` values of a [`Commitment`](https://github.com/Panta-Rhei-Research/taulib/blob/main/TauLib/BookVII/Meta/Commitment.lean) structure (inspectable data), not as `theorem X : True := sorry`. See [CHANGELOG.md](https://github.com/Panta-Rhei-Research/taulib/blob/main/CHANGELOG.md) for the full history.*

## Browse the Documentation

<div class="btn-group section-ctas">
  <a href="{{ '/docs/' | relative_url }}" class="btn-secondary">Browse All Modules</a>
  <a href="https://github.com/Panta-Rhei-Research/taulib" class="btn-ghost">View on GitHub</a>
</div>

</div>
