---
layout: default
title: "TauLib"
right_rail:
  related:
    - title: "WP003 — Technical Overview"
      url: https://panta-rhei.site/publications/anchor-documents/wp003-taulib-technical-overview/
    - title: "Verify / TauLib"
      url: https://panta-rhei.site/verify/taulib/
    - title: "Release Manifest"
      url: https://panta-rhei.site/verify/release-manifest/
    - title: "API Documentation"
      url: /docs/
    - title: "Panta Rhei Research"
      url: https://panta-rhei.site
  artifacts:
    - title: "TauLib GitHub"
      url: https://github.com/Panta-Rhei-Research/taulib
      external: true
  meta:
    type: "Landing"
    status: "Canonical"
    updated: "May 2026"
---

<div class="hero-card">
  <span class="eyebrow">Lean 4 Formalization &middot; Panta Rhei Research Program</span>
  <h1>TauLib</h1>
  <p>Generated Lean 4 documentation for the public TauLib repository — with release facts, trust-budget boundaries, and inspection routes owned by the Panta Rhei <a href="https://panta-rhei.site/verify/">Verify</a> lane.</p>
  <div class="btn-group">
    <a href="https://panta-rhei.site/publications/anchor-documents/wp003-taulib-technical-overview/" class="btn-primary" {% include cta-attrs.html location="hero" lane="taulib" label="Read WP003 Technical Overview" href="https://panta-rhei.site/publications/anchor-documents/wp003-taulib-technical-overview/" variant="wp003" %}>Read WP003 Technical Overview</a>
    <a href="https://panta-rhei.site/verify/taulib/" class="btn-secondary" {% include cta-attrs.html location="hero" label="Open Verify / TauLib" href="https://panta-rhei.site/verify/taulib/" variant="verify-taulib" %}>Open Verify / TauLib</a>
    <a href="{{ '/docs/' | relative_url }}" class="btn-secondary" {% include cta-attrs.html location="hero" label="Browse All Modules" href="/docs/" %}>Browse All Modules</a>
    <a href="https://github.com/Panta-Rhei-Research/taulib" class="btn-lean" target="_blank" rel="noopener" {% include cta-attrs.html location="hero" label="View on GitHub" href="https://github.com/Panta-Rhei-Research/taulib" variant="taulib-source" %}>View on GitHub</a>
    <a href="https://panta-rhei.site/verify/release-manifest/" class="btn-tertiary" {% include cta-attrs.html location="hero" label="Release Manifest" href="https://panta-rhei.site/verify/release-manifest/" variant="release-manifest" %}>Release Manifest</a>
  </div>
  <p class="hero-supporting-line">This site is the dedicated Lean documentation surface. For the full trust budget, custom-axiom inventory, no-sorry status, and bridge-boundary language, use Verify / TauLib and the Release Manifest.</p>
</div>

<div class="content-card" markdown="1">

## WP003 — TauLib Technical Overview

WP003 is the canonical technical white paper for TauLib: architecture, release snapshot, trust budget, inspection routes, and reviewer protocols. Read it first if you want one self-contained document explaining what TauLib is, what it does, and what it does not do.

<div class="btn-group section-ctas">
  <a href="https://panta-rhei.site/publications/anchor-documents/wp003-taulib-technical-overview/" class="btn-primary" {% include cta-attrs.html location="section" label="Read WP003 landing" href="https://panta-rhei.site/publications/anchor-documents/wp003-taulib-technical-overview/" variant="wp003-landing" %}>Read WP003 (landing)</a>
  <a href="https://panta-rhei.site/assets/pdfs/anchor-documents/wp003-taulib-technical-overview.pdf" class="btn-secondary" target="_blank" rel="noopener" {% include cta-attrs.html location="section" label="WP003 PDF" href="https://panta-rhei.site/assets/pdfs/anchor-documents/wp003-taulib-technical-overview.pdf" variant="wp003-pdf" %}>Download PDF</a>
  <a href="https://prrp.site/wp003" class="btn-tertiary" {% include cta-attrs.html location="section" label="prrp.site/wp003" href="https://prrp.site/wp003" variant="wp003-short" %}>Short route: prrp.site/wp003</a>
</div>

## About TauLib

TauLib is the public Lean 4 formalization surface of the Panta Rhei Research Program. This site hosts generated Lean documentation from the public TauLib repository. It is intentionally narrow: it helps reviewers browse modules, declarations, source routes, and formalization structure.

The full verification context lives on [Verify / TauLib](https://panta-rhei.site/verify/taulib/), and authoritative release metrics live in the [Release Manifest](https://panta-rhei.site/verify/release-manifest/).

## Manifest-pinned snapshot

<div class="summary-cards">
  <article class="summary-card">
    <div class="summary-card-title">{% include release-metric.html id="taulib.modules" unit=true %}</div>
    <div class="summary-card-body">Modules in the pinned v4.0 release snapshot. <a href="https://panta-rhei.site/verify/release-manifest/">Release Manifest is authoritative</a>.</div>
  </article>
  <article class="summary-card">
    <div class="summary-card-title">{% include release-metric.html id="taulib.lines" unit=true %}</div>
    <div class="summary-card-body">Lean source lines counted by the release manifest.</div>
  </article>
  <article class="summary-card">
    <div class="summary-card-title">{% include release-metric.html id="taulib.theorems_lemmas" unit=true %}</div>
    <div class="summary-card-body">Theorem and lemma records in the release snapshot.</div>
  </article>
  <article class="summary-card">
    <div class="summary-card-title">{% include release-metric.html id="taulib.declarations" unit=true %}</div>
    <div class="summary-card-body">Declarations and <code>#eval</code> computations across the library.</div>
  </article>
  <article class="summary-card">
    <div class="summary-card-title">{% include release-metric.html id="taulib.custom_axioms" unit=true %}</div>
    <div class="summary-card-body">Disclosed custom axioms (all Book III, all conjectural). <a href="https://panta-rhei.site/verify/release-manifest/">See manifest</a>.</div>
  </article>
  <article class="summary-card">
    <div class="summary-card-title">{% include release-metric.html id="taulib.sorry" unit=true %}</div>
    <div class="summary-card-body">Incomplete proof assignments in the release snapshot.</div>
  </article>
</div>

<p class="release-authority-note"><em>Release snapshot: May 2026 &middot; The <a href="https://panta-rhei.site/verify/release-manifest/">Release Manifest</a> is authoritative for current metrics.</em></p>

## What TauLib does — and does not do

<div class="notice note">
<p><strong>TauLib checks Lean-formalized proof obligations where they are represented in source.</strong></p>

<p>It does <em>not</em> by itself establish empirical truth, bridge adequacy, semantic correspondence to prose, life-recovery interpretation, public-good relevance, external acceptance, or deployment readiness. Those boundaries live on <a href="https://panta-rhei.site/verify/taulib/">Verify / TauLib</a> and across the broader <a href="https://panta-rhei.site/verify/">Verify lane</a>.</p>
</div>

## How to inspect

A short reviewer route, in order:

1. **Read [WP003](https://panta-rhei.site/publications/anchor-documents/wp003-taulib-technical-overview/)** for architecture and trust budget.
2. **Open [Verify / TauLib](https://panta-rhei.site/verify/taulib/)** for release status and boundary.
3. **Browse [generated module docs]({{ '/docs/' | relative_url }})** for declarations, source routes, and module structure.
4. **Inspect [source on GitHub](https://github.com/Panta-Rhei-Research/taulib)**.
5. **Use the [Release Manifest](https://panta-rhei.site/verify/release-manifest/)** for pinned counts and source ownership.

## Browse the documentation

<div class="btn-group section-ctas">
  <a href="{{ '/docs/' | relative_url }}" class="btn-secondary" {% include cta-attrs.html location="section" label="Browse All Modules (footer)" href="/docs/" variant="docs-bottom" %}>Browse All Modules</a>
  <a href="https://panta-rhei.site/verify/release-manifest/" class="btn-tertiary" {% include cta-attrs.html location="section" label="Read Release Manifest" href="https://panta-rhei.site/verify/release-manifest/" variant="release-manifest" %}>Read Release Manifest</a>
  <a href="https://github.com/Panta-Rhei-Research/taulib" class="btn-lean" target="_blank" rel="noopener" {% include cta-attrs.html location="section" label="View on GitHub (footer)" href="https://github.com/Panta-Rhei-Research/taulib" variant="taulib-source" %}>View on GitHub</a>
</div>

</div>
