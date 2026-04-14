---
layout: default
title: "API Documentation"
permalink: /docs/
right_rail:
  related:
    - title: "Home"
      url: /
    - title: "Panta Rhei Verify"
      url: https://panta-rhei.site/verify/taulib/
  meta:
    type: "Documentation Index"
    status: "Canonical"
    updated: "April 2026"
---

<div class="hero-card">
  <span class="eyebrow">TauLib &middot; API Reference</span>
  <h1>Module Documentation</h1>
  <p>Browse the 450 Lean 4 modules organized by book and subject area.</p>
</div>

<div class="content-card">

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
