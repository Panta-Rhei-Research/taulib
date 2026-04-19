# Doc-Gen4 Documentation Pipeline — Full Implementation Plan

## Goal

Generate a self-contained, browsable, searchable HTML documentation site for TauLib using [doc-gen4](https://github.com/leanprover/doc-gen4), enhanced with Panta Rhei theming, a statistics dashboard, an interactive dependency graph, and filtered to show **only TauLib content** (no Lean/Mathlib/Batteries noise).

All output is **hosting-agnostic**: every link is relative, the entire `docbuild/.lake/build/doc/` directory can be served from any static host — GitHub Pages, Netlify, Vercel, S3, a local HTTP server, or a subdirectory on `panta-rhei.site`. The deployment target is chosen at publish time, not at build time.

---

## Current State (Post-Sprint 2)

| Metric | Status |
|--------|--------|
| Module docstrings (`/-! ... -/`) | **445/445 (100%)** |
| Declaration docstrings (`/-- ... -/`) | **7,622 total across 22,673 indexed declarations** |
| Lean toolchain | `leanprover/lean4:v4.28.0-rc1` |
| `docbuild/` infrastructure | Created and functional |
| `lake build TauLib:docs` | **3,903 jobs, all 445 module pages generated** |
| `build_docs.sh` | Functional: doc-gen4 + CSS theme + landing page + stats + depgraph |
| Custom landing page | `scripts/landing_page.html` — injected into `index.html` |
| Panta Rhei CSS theme | `scripts/taulib_theme.css` — appended to `style.css` |
| Statistics dashboard | `scripts/generate_stats.py` → `stats.html` |
| Dependency graph | `scripts/generate_depgraph.py` → `depgraph.html` (vis.js) |

### The Problem: Transitive Dependency Bloat

Doc-gen4 **always generates documentation for all transitive dependencies**. There is no flag to suppress this. The result:

| Component | HTML Files | Size | Wanted? |
|-----------|----------:|-----:|:-------:|
| **TauLib/** | 445 | 36 MB | Yes |
| Init/ | 515 | 61 MB | No |
| Std/ | 393 | 83 MB | No |
| Mathlib/ | 533 | 60 MB | No |
| Lean/ | 1,058 | 42 MB | No |
| Lake/ | 135 | 6 MB | No |
| Aesop/ | 134 | 6 MB | No |
| Batteries/ | 80 | 5 MB | No |
| Other (5 dirs) | 45 | 2 MB | No |
| **Total** | **3,338** | **323 MB** | — |

The navbar (325 KB) shows all 13 namespaces. The search index (`declaration-data.bmp`, 19 MB) contains 137,084 declarations — only 22,673 (17%) are TauLib. **89% of the generated output is noise.**

---

## Architecture

### Directory Structure

```
TauLib/
├── lakefile.lean              # Main library (unchanged)
├── lean-toolchain             # Pinned Lean version
├── lake-manifest.json         # Dependency lock
├── TauLib/                    # 445 Lean source files
├── docbuild/                  # Nested doc-gen4 project
│   ├── lakefile.toml          # References parent TauLib + doc-gen4
│   ├── lean-toolchain         # Symlink → ../lean-toolchain
│   ├── .gitignore             # Ignores .lake/
│   └── .lake/build/doc/       # Generated output (not committed)
├── scripts/
│   ├── build_docs.sh          # Master build script (all steps)
│   ├── filter_docs.py         # NEW: Strip non-TauLib content
│   ├── taulib_theme.css       # Panta Rhei CSS overrides
│   ├── landing_page.html      # Custom index.html content
│   ├── generate_stats.py      # Statistics dashboard generator
│   ├── generate_depgraph.py   # Dependency graph generator
│   └── vendor/
│       └── vis-network.min.js # Bundled vis.js (no CDN dependency)
├── .github/workflows/
│   ├── lean-build.yml         # Library CI
│   └── docs.yml               # NEW: Documentation CI + deploy
└── docs/                      # Markdown docs (this plan lives here)
```

### Design Principles

1. **All links relative** — no hardcoded URLs anywhere in generated output
2. **Hosting-agnostic** — serve from any static host, any subdirectory
3. **TauLib-only** — strip all transitive dependency docs post-build
4. **Single build command** — `./scripts/build_docs.sh` does everything
5. **Idempotent** — safe to re-run; `--skip-*` flags for incremental builds
6. **Self-contained** — vis.js bundled locally, no CDN dependencies

---

## Sprint Plan

### Sprint 1: Docbuild Infrastructure (DONE)

Created `docbuild/lakefile.toml`, symlinked `lean-toolchain`, ran initial `lake update doc-gen4`.

**Files:**
- `docbuild/lakefile.toml` — references parent TauLib + doc-gen4
- `docbuild/lean-toolchain` → `../lean-toolchain`
- `docbuild/.gitignore` — ignores `.lake/`

### Sprint 2: Doc-Gen4 Build (DONE)

Ran `lake build TauLib:docs` — 3,903 jobs, all 445 module pages generated. 323 MB raw output.

### Sprint 3: Panta Rhei CSS Theme (DONE)

`scripts/taulib_theme.css` — appended to `style.css` during post-build. Provides:
- Header: deep sienna (#2c1810) matching book cover spines
- Body: warm parchment off-white (#faf8f5)
- Declaration badges: semantic color coding (golden definitions, sage green theorems, saddle brown axioms, burnt orange structures)
- Full dark mode support
- Subtle header border matching the Panta Rhei series aesthetic

### Sprint 4: Custom Landing Page (DONE)

`scripts/landing_page.html` — injected into `index.html` via `build_docs.sh`. Contains:
- Library-at-a-glance statistics table
- Browse-by-book table with module counts and "Start Here" links
- Reading paths for 4 audiences (mathematician, physicist, Lean user, philosopher)
- Links to stats dashboard, dependency graph, and root module page
- All links relative

### Sprint 5: Statistics Dashboard (DONE)

`scripts/generate_stats.py` → `stats.html`. Reads registry JSONL files and scans Lean source:
- Overview grid: 8 metric cards (modules, lines, theorems, defs, #eval, registry, formalized, sorry)
- Per-book breakdown table: modules, lines, theorems, defs, #eval, axioms, sorry
- Registry formalization coverage with progress bars
- Scope distribution table (established / &tau;-effective / conjectural / metaphorical)
- Registry type distribution (theorem / definition / proposition / remark / lemma / corollary)

### Sprint 6: Interactive Dependency Graph (DONE)

`scripts/generate_depgraph.py` → `depgraph.html`. Uses vis.js (bundled, no CDN):
- 4,500+ registry entry nodes with scope-colored dots
- Dependency edges from registry `depends_on` fields
- Filter by book (dropdown) and scope (checkboxes)
- Search box for ID or name
- Click to show info panel; double-click to navigate to doc page
- Node size proportional to dependent count
- Formalized entries: solid border; unformalized: dashed

### Sprint 7: TauLib-Only Filtering (TODO)

**The critical missing piece.** A post-build script that strips all non-TauLib content.

#### `scripts/filter_docs.py`

**What it does:**

1. **Delete 12 non-TauLib directories:**
   ```
   Aesop/ Batteries/ ImportGraph/ Init/ Lake/ Lean/
   LeanSearchClient/ Mathlib/ Plausible/ ProofWidgets/ Qq/ Std/
   ```
   Plus their root-level `.html` files (`Aesop.html`, `Init.html`, etc.)

2. **Rebuild `navbar.html`:**
   - Parse the existing navbar HTML
   - Extract only the TauLib `<details>` section
   - Re-wrap in the navbar HTML skeleton (head, body, nav tags)
   - Write back — sidebar now shows only BookI–BookVII + Tour

3. **Filter `declarations/declaration-data.bmp`:**
   - Parse the JSON (it's actually uncompressed JSON despite the `.bmp` extension)
   - Keep only entries whose `docLink` starts with `./TauLib`
   - Write back — search now returns only TauLib results
   - Reduces from 137,084 entries (19 MB) to 22,673 entries (~3 MB)

4. **Clean up static references:**
   - Remove `foundational_types.html` (references Lean core types)
   - Update any remaining cross-references if needed

**Actual result (verified):**

| Metric | Before | After | Reduction |
|--------|-------:|------:|:---------:|
| Total size | 326 MB | 44 MB | **87%** |
| HTML files | 3,354 | 454 | **87%** |
| Search entries | 137,084 | 22,673 | **83%** |
| Navbar size | 333 KB (13 namespaces) | 53 KB (TauLib only) | **84%** |
| Search index | 19.7 MB | 5.0 MB | **75%** |

**Integration into `build_docs.sh`:** Add as Step 3 (after doc-gen4, before CSS theme), so all subsequent steps operate on the filtered output.

#### Build Script Step Order (After This Sprint)

```
Step 1: lake build TauLib                    (compile library)
Step 2: lake build TauLib:docs               (generate raw doc-gen4 output)
Step 3: python3 filter_docs.py               (strip non-TauLib content)    ← NEW
Step 4: cat taulib_theme.css >> style.css     (apply CSS theme)
Step 5: inject landing_page.html             (replace index.html content)
Step 6: python3 generate_stats.py            (statistics dashboard)
Step 7: python3 generate_depgraph.py         (dependency graph)
```

### Sprint 8: Build Script Integration

Update `build_docs.sh` to:
1. Call `filter_docs.py` as Step 3
2. Add `--skip-filter` flag for debugging (to keep full output)
3. Print before/after size in summary
4. Verify that TauLib cross-links still resolve after filtering

### Sprint 9: Quality Audit

Serve the filtered docs locally and verify:

1. **Sidebar** — shows only TauLib modules (BookI–BookVII + Tour)
2. **Search** — returns only TauLib declarations
3. **Cross-module links** — TauLib types link correctly to other TauLib modules
4. **Landing page** — all links resolve
5. **Stats dashboard** — accessible from index
6. **Dependency graph** — loads, filters, navigates to doc pages
7. **Dark mode** — CSS theme applies correctly
8. **Mobile** — responsive layout works

### Sprint 10: CI Workflow for Deployment (DONE)

Created `.github/workflows/docs.yml` — the definitive CI/CD workflow using the modern artifact-based GitHub Pages deployment (no `gh-pages` branch needed).

**Architecture:**
```
Push to main
     │
     ▼
┌─────────────────────────────────────────┐
│ Job 1: build-docs                       │
│                                         │
│ 1. Checkout                             │
│ 2. lean-action (build + cache)          │
│ 3. Cache docbuild/.lake                 │
│ 4. lake update doc-gen4 (if needed)     │
│ 5. lake build TauLib:docs               │
│ 6. filter_docs.py (strip non-TauLib)    │
│ 7. CSS theme + landing page             │
│ 8. Stats dashboard + dependency graph   │
│ 9. configure-pages + upload-pages-artifact│
└────────────────────┬────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────┐
│ Job 2: deploy                           │
│                                         │
│ deploy-pages@v4 → GitHub Pages CDN      │
│ (OIDC-authenticated, no token needed)   │
└─────────────────────────────────────────┘
```

**Key design decisions:**
- **No `gh-pages` branch** — uses the modern `actions/deploy-pages@v4` artifact-based approach
- **Path filtering** — only triggers when Lean source, scripts, or docbuild config changes
- **Docbuild caching** — `docbuild/.lake` is cached separately from the library `.lake`
- **Registry fallback** — looks for `registry/` in the repo; skips stats/depgraph if absent
- **`workflow_dispatch`** — can be triggered manually from the Actions tab
- **One-time setup** — requires: Settings → Pages → Source → "GitHub Actions"

**Pages URL:** `https://panta-rhei-research.github.io/taulib/` (once enabled)

### Sprint 11: README Integration

Once the pipeline is validated, add to `README.md`:

1. **Badge** (URL filled in at publish time):
   ```markdown
   [![API Docs](https://img.shields.io/badge/API_Docs-online-blue)](./docbuild/.lake/build/doc/index.html)
   ```

2. **Documentation table entry:**
   ```markdown
   | API Documentation | Browsable, searchable HTML docs for every module and declaration |
   ```

3. **Build instructions** (already present in current README — verify accuracy)

---

## Resource Estimates

| Resource | Raw (Before Filter) | After Filter |
|----------|--------------------:|-------------:|
| Total HTML size | 323 MB | ~55 MB |
| HTML files | 3,338 | ~450 |
| Search index | 19 MB (137K entries) | ~3 MB (23K entries) |
| Navbar | 325 KB (13 namespaces) | ~30 KB (1 namespace) |
| Build time (doc-gen pass) | ~10 min | same |
| Filter pass | — | ~5 sec |

| CI Resource | Estimate |
|-------------|----------|
| Total CI time (build + docs + filter) | 30–60 min |
| CI runner memory | 7–16 GB |
| Artifact upload size | ~55 MB |
| Disk in repo | 0 (nothing committed) |

---

## Risks and Mitigations

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| doc-gen4 `rev = "main"` breaks on toolchain bump | Medium | Pin to specific commit SHA; test locally first |
| Mathlib cache conflict in docbuild | Low | `MATHLIB_NO_CACHE_ON_UPDATE=1` on `lake update` |
| Navbar structure changes in doc-gen4 update | Medium | `filter_docs.py` uses robust HTML parsing (regex + fallback) |
| Search data format changes | Low | JSON structure is stable; validation in filter script |
| GitHub runner OOM | Low | Standard runner (7 GB) worked for Sprint 2; monitor |
| Cross-links break after filtering | Low | TauLib types only link to TauLib; audit in Sprint 9 |
| vis.js CDN unavailable | None | vis.js is bundled locally in `scripts/vendor/` |

---

## Deployment Flexibility

The build output at `docbuild/.lake/build/doc/` is a **self-contained static site** with all relative links. It can be deployed to:

| Target | How |
|--------|-----|
| **Local preview** | `cd docbuild/.lake/build/doc && python3 -m http.server 8000` |
| **GitHub Pages** | CI workflow with `deploy-pages@v4` (Sprint 10) |
| **panta-rhei.site subdirectory** | Copy `doc/` to web server at any path |
| **Netlify / Vercel** | Point to `docbuild/.lake/build/doc` as publish directory |
| **S3 / CloudFront** | Upload `doc/` contents to bucket |
| **CI artifact download** | `actions/upload-artifact` — available from any CI run |

The deployment target is **not baked into the build**. Choose at publish time.

---

## Sprint Summary

| Sprint | Scope | Status | Effort |
|--------|-------|:------:|-------:|
| 1 | Docbuild infrastructure | DONE | 10 min |
| 2 | Doc-gen4 build (3,903 jobs) | DONE | 45 min |
| 3 | Panta Rhei CSS theme | DONE | 15 min |
| 4 | Custom landing page | DONE | 20 min |
| 5 | Statistics dashboard | DONE | 30 min |
| 6 | Interactive dependency graph | DONE | 40 min |
| 7 | TauLib-only filtering | DONE | 45 min |
| 8 | Build script integration | DONE | 15 min |
| 9 | Quality audit | DONE | 30 min |
| 10 | CI workflow (GitHub Pages) | DONE | 20 min |
| 11 | **README integration** | **TODO** | 10 min |

**Remaining effort: ~10 min** (Sprint 11 — update README badge once the site URL is known).

---

## Appendix: Key File Inventory

| File | Purpose | Lines |
|------|---------|------:|
| `docbuild/lakefile.toml` | Nested project referencing TauLib + doc-gen4 | 12 |
| `scripts/build_docs.sh` | Master orchestrator (7 steps) | 174 |
| `scripts/filter_docs.py` | Strip non-TauLib content from generated docs | ~150 (est.) |
| `scripts/taulib_theme.css` | Panta Rhei CSS overrides (light + dark) | 65 |
| `scripts/landing_page.html` | Custom index.html content | 143 |
| `scripts/generate_stats.py` | Registry → stats dashboard HTML | 381 |
| `scripts/generate_depgraph.py` | Registry → vis.js dependency graph | 424 |
| `.github/workflows/docs.yml` | CI: build + filter + deploy | ~50 (est.) |
