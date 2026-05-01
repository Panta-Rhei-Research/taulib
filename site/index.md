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
  <p>Dedicated Lean documentation site for the <a href="https://panta-rhei.site">Panta Rhei Research Program</a>.</p>
  <div class="btn-group">
    <a href="https://panta-rhei.site/verify/taulib/" class="btn-primary">Open Verify / TauLib</a>
    <a href="{{ '/docs/' | relative_url }}" class="btn-secondary">Browse All Modules</a>
    <a href="https://panta-rhei.site/verify/release-manifest/" class="btn-tertiary">Release Manifest</a>
    <a href="https://github.com/Panta-Rhei-Research/taulib" class="btn-lean" target="_blank" rel="noopener">View on GitHub</a>
  </div>
  <p class="hero-supporting-line">This site is the dedicated Lean documentation surface. Current metrics, trusted-base details, and count reconciliation live in the Panta Rhei Release Manifest.</p>
</div>

<div class="content-card" markdown="1">

## About TauLib

TauLib is the Lean 4 formalization layer of the Panta Rhei Research Program. It contains the formal kernel and proof-oriented implementation work that supports the program's public verification surface.

This site is intentionally narrow: it hosts Lean-oriented documentation generated from the public TauLib repository. The full verification context lives on [Verify / TauLib](https://panta-rhei.site/verify/taulib/), and current release metrics live in the [Release Manifest](https://panta-rhei.site/verify/release-manifest/).

## What This Site Is

- A generated documentation shell for TauLib modules and source-facing readers.
- A companion to the active [TauLib GitHub repository](https://github.com/Panta-Rhei-Research/taulib).
- A route back to the full public verification matrix on `panta-rhei.site`.

TauLib checks Lean-formalized proof obligations where they are represented in source. It does not, by itself, settle empirical truth, bridge adequacy, semantic correspondence, life-recovery interpretation, or external acceptance.

## Browse the Documentation

<div class="btn-group section-ctas">
  <a href="{{ '/docs/' | relative_url }}" class="btn-secondary">Browse All Modules</a>
  <a href="https://panta-rhei.site/verify/release-manifest/" class="btn-tertiary">Read Release Manifest</a>
  <a href="https://github.com/Panta-Rhei-Research/taulib" class="btn-lean" target="_blank" rel="noopener">View on GitHub</a>
</div>

</div>
