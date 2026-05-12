---
layout: default
title: "API Documentation"
permalink: /docs/
og_image: /assets/og/png/og-docs.png
og_image_alt: "TauLib API Documentation — generated Lean 4 module docs"
right_rail:
  related:
    - title: "Home"
      url: /
    - title: "WP003 — Technical Overview"
      url: https://panta-rhei.site/publications/anchor-documents/wp003-taulib-technical-overview/
    - title: "Verify / TauLib"
      url: https://panta-rhei.site/verify/taulib/
    - title: "Release Manifest"
      url: https://panta-rhei.site/verify/release-manifest/
  meta:
    type: "Documentation Index"
    status: "Canonical"
    updated: "May 2026"
---

<div class="hero-card">
  <span class="eyebrow">TauLib &middot; API Reference</span>
  <h1>Module Documentation</h1>
  <p>Generated Lean 4 module documentation, organized by book and subject area. For release metrics and trust budget, use the Release Manifest and WP003.</p>
  <div class="btn-group">
    <a href="https://panta-rhei.site/publications/anchor-documents/wp003-taulib-technical-overview/" class="btn-primary">WP003</a>
    <a href="https://panta-rhei.site/verify/taulib/" class="btn-secondary">Verify / TauLib</a>
    <a href="https://panta-rhei.site/verify/release-manifest/" class="btn-tertiary">Release Manifest</a>
    <a href="https://github.com/Panta-Rhei-Research/taulib" class="btn-lean" target="_blank" rel="noopener">GitHub</a>
  </div>
</div>

<div class="content-card" markdown="1">

{% if site.data.nav_modules %}
{% for book in site.data.nav_modules.books %}

## Book {{ book.roman }} — {{ book.title }}

{% for section in book.sections %}

### {{ section.name }}

{% for mod in section.modules %}
- [{{ mod.name }}]({{ mod.url | relative_url }})
{% endfor %}

{% endfor %}
{% endfor %}

{% if site.data.nav_modules.tour %}

## Guided Tours

{% for tour in site.data.nav_modules.tour %}
- [{{ tour.name }}]({{ tour.url | relative_url }})
{% endfor %}
{% endif %}

{% else %}

*Module index will be populated after the next doc-gen4 build.*

{% endif %}

</div>
