<p align="center">
  <strong>TauLib</strong><br>
  <em>Mechanized Formalization of Category &tau;</em>
</p>

<p align="center">
  <a href="https://lean-lang.org"><img src="https://img.shields.io/badge/Lean_4-v4.28.0--rc1-blue?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHdpZHRoPSIxNiIgaGVpZ2h0PSIxNiI+PHJlY3Qgd2lkdGg9IjE2IiBoZWlnaHQ9IjE2IiBmaWxsPSJub25lIi8+PHRleHQgeD0iMyIgeT0iMTIiIGZpbGw9IndoaXRlIiBmb250LXNpemU9IjEyIj5MPC90ZXh0Pjwvc3ZnPg==" alt="Lean 4"></a>
  <a href="https://github.com/panta-rhei-framework/taulib/actions"><img src="https://github.com/panta-rhei-framework/taulib/actions/workflows/lean-build.yml/badge.svg" alt="CI"></a>
  <a href="LICENSE"><img src="https://img.shields.io/badge/License-Apache_2.0-green.svg" alt="License"></a>
  <a href="https://panta-rhei.site"><img src="https://img.shields.io/badge/Panta_Rhei-Books-8B4513" alt="Panta Rhei"></a>
</p>

---

TauLib is a **125,000-line Lean 4 formalization** of **Category &tau;** &mdash; a categorical framework built from 7 axioms (K0&ndash;K6) on 5 generators (&alpha;, &pi;, &gamma;, &eta;, &omega;) with a single primitive iterator &rho;. Starting from these axioms alone, TauLib derives arithmetic, analysis, geometry, physics, biology, and philosophy as earned consequences &mdash; all compiled and verified by Lean's kernel with **zero sorry in Books I&ndash;VI**.

Companion to the 7-book [**Panta Rhei**](https://panta-rhei.site) series by Thorsten Fuchs and Anna-Sophie Fuchs (2nd Edition, 2026).

---

## At a Glance

| Metric | Value |
|--------|------:|
| Source files | 450 |
| Lines of Lean 4 | 125,771 |
| Theorems &amp; lemmas | 4,332 |
| Definitions | 3,542 |
| Structures, classes &amp; inductives | 1,685 |
| Instances | 28 |
| Examples | 350 |
| Computations (`#eval`) | 3,721 |
| Axioms | 4 (3 conjectural, 1 structural) |
| Sorry | 3 (methodological, Book VII only) |
| Books I&ndash;VI sorry | **0** |
| Mathlib usage | Tactics only &mdash; all mathematics from scratch |

---

## What Makes TauLib Unique

- **Everything from scratch.** TauLib does not import mathematical content from Mathlib or any other library. All arithmetic, algebra, analysis, topology, category theory, quantum mechanics, and cosmology are derived within the framework, from the 5 generators and 7 axioms. Mathlib is used for proof *tactics* only (`simp`, `omega`, `ring`, `decide`, `linarith`, `norm_num`).

- **3,721 live computations.** Every quantitative claim is backed by `#eval` statements that execute in the Lean kernel, producing concrete numerical values from the master constant &iota;<sub>&tau;</sub> = 2/(&pi; + e).

- **Physics predictions at ppm accuracy.** The library formalizes predictions for 9 electroweak quantities, CMB first peak position (+69 ppm), 20 galaxy rotation curves, baryon asymmetry, and more &mdash; all derived from a single constant with zero free parameters.

- **Transparent foundations.** The 4 axioms and 3 sorry are explicitly documented, with precise classification (conjectural, structural, methodological). The conjectural axioms follow a "compute-then-axiomatize" pattern: finite checks pass computationally; the axiom asserts the infinite extension.

---

## Quick Start

### Prerequisites

- [Lean 4](https://lean-lang.org/lean4/doc/setup.html) via [elan](https://github.com/leanprover/elan) (version managed by `lean-toolchain`)

### Clone and Build

```bash
git clone https://github.com/panta-rhei-framework/taulib.git
cd TauLib
lake build
```

The first build downloads Mathlib (for tactics) and compiles ~1,256 lake jobs. Subsequent builds use the cache and are fast.

### Use as a Dependency

Add to your `lakefile.lean`:

```lean
require TauLib from git
  "https://github.com/panta-rhei-framework/taulib.git" @ "main"
```

Or in `lakefile.toml`:

```toml
[[require]]
name = "TauLib"
git = "https://github.com/panta-rhei-framework/taulib.git"
rev = "main"
```

### Build API Documentation

TauLib includes a full [doc-gen4](https://github.com/leanprover/doc-gen4) documentation pipeline with Panta Rhei theming, a statistics dashboard, and an interactive dependency graph:

```bash
# First build (initializes doc-gen4):
cd docbuild && MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4 && cd ..

# Generate full documentation:
./scripts/build_docs.sh

# Preview locally:
cd docbuild/.lake/build/doc && python3 -m http.server 8000
```

The generated documentation includes:
- **API pages** for all 450 modules with rendered docstrings and cross-linked types
- **Statistics dashboard** with per-book formalization coverage from the registry
- **Interactive dependency graph** visualizing 4,500+ mathematical registry entries across 7 books

---

## Start Here

Open these files in VS Code with the Lean 4 extension and step through line by line:

| Tour | Time | What You'll See |
|------|:----:|----------------|
| [`Tour/VerifyItYourself.lean`](TauLib/Tour/VerifyItYourself.lean) | 15 min | **Start here.** 5 surprising claims, verified live &mdash; the skeptic&rsquo;s tour |
| [`Tour/Foundations.lean`](TauLib/Tour/Foundations.lean) | 10 min | 5 generators, 7 axioms, &rho; operator, master constant, rigidity |
| [`Tour/CentralTheorem.lean`](TauLib/Tour/CentralTheorem.lean) | 10 min | Split-complex ring, &tau;&sup3; fibration, O(&tau;&sup3;) &cong; A<sub>spec</sub>(&Lscr;) |
| [`Tour/Physics.lean`](TauLib/Tour/Physics.lean) | 15 min | EW synthesis, 3 generations, CMB, rotation curves, baryogenesis |
| [`Tour/OneConstant.lean`](TauLib/Tour/OneConstant.lean) | 10 min | Full constants ledger: &alpha;, h, &ell;&#8321;, &omega;<sub>b</sub>, r &mdash; all from &iota;<sub>&tau;</sub> |
| [`Tour/MillenniumProblems.lean`](TauLib/Tour/MillenniumProblems.lean) | 15 min | GRH, BSD, Poincar&eacute;, Hodge, Navier-Stokes through the &tau;-lens |
| [`Tour/LifeFromPhysics.lean`](TauLib/Tour/LifeFromPhysics.lean) | 10 min | 4+1 life sectors, genetic code, neural architecture, crossing limit |
| [`Tour/MindAndEthics.lean`](TauLib/Tour/MindAndEthics.lean) | 15 min | Categorical Imperative, consciousness, free will, Logos, the 3 sorry |

### Pick Your Path

| Audience | Start With | Then Explore |
|----------|-----------|-------------|
| **Skeptic / Reviewer** | `Tour/VerifyItYourself` | `Tour/OneConstant` &rarr; any module you doubt |
| **Mathematician** | `Tour/Foundations` &rarr; `Tour/CentralTheorem` | `Tour/MillenniumProblems` &rarr; `BookIII/Doors/GrandGRH` |
| **Physicist** | `Tour/Physics` &rarr; `Tour/OneConstant` | `BookIV/Electroweak/EWSynthesis` &rarr; `BookV/Cosmology/CMBSpectrum` |
| **Biologist** | `Tour/LifeFromPhysics` | `BookVI/Source/GeneticCode` &rarr; `BookVI/Consumer/Neural` |
| **Philosopher** | `Tour/MindAndEthics` | `BookVII/Ethics/CIProof` &rarr; `BookVII/Final/Boundary` |
| **Lean user** | `Tour/Foundations` &rarr; `lakefile.lean` | Browse any module &mdash; all 450 files have 30+ line docstrings |

See the [Architecture Guide](docs/ARCHITECTURE.md) for detailed reading paths, dependency graphs, and per-book start files.

---

## Module Architecture

All 450 modules are organized under seven book namespaces. The dependency order is strict: each book builds only on what came before.

```
TauLib
 ├── BookI    Categorical Foundations    94 files   20,554 lines
 ├── BookII   Categorical Holomorphy     65 files   18,069 lines
 ├── BookIII  Categorical Spectrum       70 files   16,807 lines
 ├── BookIV   Categorical Microcosm      89 files   29,730 lines
 ├── BookV    Categorical Macrocosm      80 files   28,394 lines
 ├── BookVI   Categorical Life           30 files    5,221 lines
 ├── BookVII  Categorical Metaphysics     7 files    4,278 lines
 └── Tour     Interactive Guides          3 files      674 lines
```

### Book I &mdash; Categorical Foundations (94 files, 20,554 lines)

The foundation builds everything from the 5 generators, using 12 module families:

| Family | Files | Content |
|--------|------:|---------|
| `Kernel` | 4 | 5 generators, axioms K0&ndash;K6, &rho; operator |
| `Orbit` | 8 | Orbit generation, closure, iterator ladder, rigidity: Aut(&tau;) = {id} |
| `Denotation` | 9 | &tau;-Idx (earned natural numbers), rank transfers, program monoid |
| `Coordinates` | 10 | Normal form, ABCD chart, hyperfactorization, Chebyshev coordinates |
| `Polarity` | 14 | Prime Polarity Theorem, lemniscate &Lscr;, CRT, bipolar algebra |
| `Boundary` | 14 | Split-complex ring &Hopf;[j], number tower, &iota;<sub>&tau;</sub>, characters |
| `Sets` | 8 | Internal set theory, Cantor refutation, counting |
| `Logic` | 3 | Truth&#8324; logic, explosion barrier, Boolean recovery |
| `Holomorphy` | 9 | &omega;-germ transformers, Global Hartogs, presheaf essence |
| `Topos` | 7 | Earned arrows, functors, sites, sheaves |
| `MetaLogic` | 7 | Proof-theoretic mirror, linear discipline, structural exclusion |
| `CF` | 1 | Continued fraction window algebra |

### Books II&ndash;VII

| Book | Files | Lines | Key Content |
|------|------:|------:|-------------|
| **II** Holomorphy | 65 | 18,069 | &tau;&sup3; = &tau;&sup1; &times;<sub>f</sub> T&sup2;, Central Theorem: O(&tau;&sup3;) &cong; A<sub>spec</sub>(&Lscr;) |
| **III** Spectrum | 70 | 16,807 | 8 spectral forces, Millennium Problems, &tau;-Turing machine |
| **IV** Microcosm | 89 | 29,730 | Electroweak synthesis, 3 generations, Majorana, strong CP, Higgs |
| **V** Macrocosm | 80 | 28,394 | Gravity, CMB (+69 ppm), rotation curves, baryogenesis, lensing |
| **VI** Life | 30 | 5,221 | 5-condition life predicate, origin of life, consciousness |
| **VII** Metaphysics | 7 | 4,278 | Saturation, archetypes, Categorical Imperative, social ontology |

---

## Key Results

Formalized results with their Lean entry points:

| Result | Lean Identifier | ppm | Book |
|--------|----------------|----:|-----:|
| **Central Theorem**: O(&tau;&sup3;) &cong; A<sub>spec</sub>(&Lscr;) | `central_fwd_3_15` | &mdash; | II |
| **Rigidity**: Aut(&tau;) = {id} | `rigidity_non_omega` | &mdash; | I |
| **Three Generations**: H&#8321;(&tau;&sup3;; &Zopf;) &cong; &Zopf;&sup3; | `gen_count_three` | exact | IV |
| **9 EW Quantities** from &iota;<sub>&tau;</sub> + m<sub>n</sub> | `nine_ew_quantities` | sub-ppm | IV |
| **Majorana Neutrinos**: &sigma; = C<sub>&tau;</sub> | `all_neutrinos_majorana` | &mdash; | IV |
| **Strong CP**: &theta;<sub>QCD</sub> = 0 | `theta_qcd_zero_from_sa_i` | exact | IV |
| **CMB First Peak**: &ell;&#8321; (NLO) | `first_peak_holonomy_thm` | +69 | V |
| **20 Galaxy Rotation Curves** | `flat_rotation_theorem` | RMS 0.067 dex | V |
| **Baryogenesis**: &eta;<sub>B</sub> = &alpha; &middot; &iota;<sub>&tau;</sub><sup>15</sup> &middot; (5/6) | `sakharov_reduction` | ~1% | V |
| **S&#8328; Tension Resolved**: S&#8328; = 0.783 | `s8_tau_value` | within 1&sigma; | V |
| **Categorical Imperative** as j-closed fixed point | `ci_j_closed_fixed_point` | &mdash; | VII |
| **Saturation**: Enrich(E&#8323;) = E&#8323; | `saturation_theorem` | &mdash; | VII |

---

## Axioms and Sorry

TauLib is maximally transparent about its foundations.

### 4 Axioms

| Axiom | Module | Classification | Pattern |
|-------|--------|---------------|---------|
| `bridge_functor_exists` | `BookIII/Bridge/BridgeAxiom` | Conjectural | Finite checks pass; axiom asserts &forall; n |
| `spectral_correspondence_O3` | `BookIII/Doors/SpectralCorrespondence` | Conjectural | Finite checks pass; axiom asserts &forall; n |
| `grand_grh_adelic` | `BookIII/Doors/GrandGRH` | Conjectural | Finite checks pass; axiom asserts &forall; n |
| `central_theorem_physical` | `BookIV/Arena/BoundaryHolonomy` | Structural | References Central Theorem (Book II) |

The 3 conjectural axioms follow a **"compute-then-axiomatize"** pattern: a decidable finite check is verified computationally via `native_decide`, then an axiom asserts the property holds universally. This makes the conjectural boundary maximally sharp and auditable.

### 3 Sorry (Book VII only)

| Theorem | Module | Assertion |
|---------|--------|-----------|
| `omega_point_theorem` | `BookVII/Logos/Sector` | `True := sorry` |
| `science_faith_boundary` | `BookVII/Logos/Sector` | `True := sorry` |
| `no_forced_stance` | `BookVII/Final/Boundary` | `True := sorry` |

All three are typed `True := sorry` &mdash; the goal is trivially `True`; the sorry marks a **philosophical boundary** where formalization itself is the content under discussion. They involve the &omega;-generator, which is non-diagrammatic by design. **Books I&ndash;VI contain zero sorry.**

---

## Dependency Policy

TauLib uses Mathlib for **proof tactics only**:

| Allowed | Not Allowed |
|---------|-------------|
| `simp`, `omega`, `ring`, `aesop` | `Mathlib.Order.*` |
| `decide`, `native_decide`, `norm_num` | `Mathlib.Algebra.*` |
| `linarith`, `positivity`, `field_simp` | `Mathlib.CategoryTheory.*` |
| `constructor`, `exact`, `apply` | `Mathlib.Topology.*` |

**All mathematical content** &mdash; natural numbers, rings, fields, groups, topology, analysis, category theory &mdash; is **built from scratch** within TauLib, derived from the 5 generators and 7 axioms. This is a deliberate design choice: the framework claims to generate all of mathematics from its foundation, and TauLib proves this claim mechanically.

---

## The Books

TauLib formalizes content from the *Panta Rhei* series (2nd Edition, 2026):

| # | Title | Chapters | LaTeX Pages |
|---|-------|:--------:|------------:|
| I | Categorical Foundations | 83 | 461 |
| II | Categorical Holomorphy | 66 | 484 |
| III | Categorical Spectrum | 104 | 415 |
| IV | Categorical Microcosm | 83 | 455 |
| V | Categorical Macrocosm | 97 | 504 |
| VI | Categorical Life | 45 | 412 |
| VII | Categorical Metaphysics | 74 | 521 |
| | **Total** | **552** | **3,252** |

Available at [panta-rhei.site](https://panta-rhei.site).

---

## Documentation

| Document | Description |
|----------|-------------|
| [Architecture Guide](docs/ARCHITECTURE.md) | Module dependency graph, reading paths by audience, per-book start files |
| [Scope Labels](docs/SCOPE_LABELS.md) | The 4-tier scope discipline: established, &tau;-effective, conjectural, metaphorical |
| [Glossary](docs/GLOSSARY.md) | Key terms, symbols, constants, and registry ID format |
| [Formalization Status](docs/FORMALIZATION_STATUS.md) | Per-book formalization coverage and sorry/axiom inventory |
| [Contributing](CONTRIBUTING.md) | Issue reporting, code style, citation, and fork guidelines |

---

## Building and Development

```bash
# Build the full library (~1,256 lake jobs)
lake build

# Build a specific book
lake build TauLib.BookI

# Check Lean version
cat lean-toolchain
```

### Continuous Integration

Every push to `main` triggers a full `lake build` via GitHub Actions. The CI badge at the top of this README reflects the latest build status.

---

## Citation

If you use TauLib in academic work, please cite:

```bibtex
@software{taulib2026,
  author    = {Fuchs, Thorsten and Fuchs, Anna-Sophie},
  title     = {{TauLib}: Mechanized Formalization of Category $\tau$},
  year      = {2026},
  version   = {2.0.0},
  url       = {https://github.com/panta-rhei-framework/taulib},
  note      = {450 modules, 125{,}771 lines of Lean 4, 4{,}332 theorems},
  license   = {Apache-2.0}
}
```

Or use GitHub's "Cite this repository" feature, which reads from [CITATION.cff](CITATION.cff).

---

## License

Copyright 2025&ndash;2026 Thorsten Fuchs and Anna-Sophie Fuchs.

Licensed under the [Apache License, Version 2.0](LICENSE).
