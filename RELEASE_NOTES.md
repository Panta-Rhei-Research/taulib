# TauLib v1.0.0 Release Notes

**Release date**: April 12, 2026
**Lean version**: 4.28.0-rc1
**License**: Apache 2.0

---

## What is TauLib?

TauLib is a 126,000-line Lean 4 formalization of **Category tau** -- a categorical framework built from 7 axioms (K0-K6) on 5 generators with a single primitive iterator. Starting from these axioms alone, TauLib derives arithmetic, analysis, geometry, physics, biology, and philosophy as earned consequences -- all compiled and verified by Lean's kernel.

Companion to the 7-book **Panta Rhei** series by Thorsten Fuchs and Anna-Sophie Fuchs (2nd Edition, 2026). Published at [panta-rhei.site](https://panta-rhei.site).

---

## At a Glance

| Metric | Value |
|--------|------:|
| Modules | 450 |
| Lines of Lean 4 | 125,771 |
| Theorems | 4,332 |
| Definitions | 3,542 |
| Live computations | 3,721 |
| Axioms | 4 |
| Sorry (Book VII) | 3 |
| Sorry (Books I-VI) | **0** |

---

## What Makes This Release Significant

### Everything from scratch

TauLib imports no mathematical content from Mathlib or any other library. Arithmetic, algebra, analysis, topology, category theory, quantum mechanics, and cosmology are all derived within the framework from 5 generators and 7 axioms. Mathlib is used for proof tactics only.

### Physics predictions with zero free parameters

The master constant iota_tau = 2/(pi + e) generates predictions for the fine-structure constant, CMB first peak position (+69 ppm), Hubble parameter, baryon density, tensor-to-scalar ratio, and galaxy rotation curves -- all without fitting.

### Transparent foundations

The 4 axioms and 3 sorry are explicitly documented with precise classification. The 3 conjectural axioms follow a compute-then-axiomatize pattern: finite checks pass computationally; the axiom asserts the infinite extension. The 3 sorry mark the precise boundary between formal proof and existential commitment.

### 8 guided tours

Interactive step-through tours for mathematicians, physicists, biologists, philosophers, skeptics, and Lean users. Open any tour in VS Code and evaluate line by line.

---

## Known Limitations

### Axioms (4 total)

| Axiom | Location | Type | Finite check |
|-------|----------|------|:------------:|
| `bridge_functor_exists` | BookIII/Bridge | Conjectural | `bridge_functor_check` |
| `grand_grh_adelic` | BookIII/Doors | Conjectural | `grand_grh_finite_check` |
| `spectral_correspondence_O3` | BookIII/Doors | Conjectural | `spectral_correspondence_finite` |
| `central_theorem_physical` | BookIV/Arena | Structural | Proof in Book II |

### Sorry (3 total, Book VII only)

| Sorry | Location | Classification |
|-------|----------|----------------|
| `no_forced_stance` | BookVII/Final | Methodological: self-referential boundary |
| `omega_point_theorem` | BookVII/Logos | Methodological: non-diagrammatic content |
| `science_faith_boundary` | BookVII/Logos | Methodological: commitment register content |

### Lean version

This release targets Lean 4.28.0-rc1 (release candidate). Build compatibility with future Lean versions is not guaranteed but expected to be straightforward.

---

## Build Instructions

```bash
# Install Lean 4 via elan (if not already installed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Clone and build
git clone https://github.com/panta-rhei-research/taulib.git
cd TauLib
lake build
```

First build downloads Mathlib (for tactics) and compiles ~1,256 lake jobs.

---

## Citation

```bibtex
@software{taulib2026,
  author    = {Fuchs, Thorsten and Fuchs, Anna-Sophie},
  title     = {{TauLib}: Mechanized Formalization of Category $\tau$},
  year      = {2026},
  version   = {1.0.0},
  url       = {https://github.com/panta-rhei-research/taulib},
  note      = {450 modules, 125,771 lines of Lean 4, 4,332 theorems},
  license   = {Apache-2.0}
}
```

---

## Quality Assurance

This release has undergone three comprehensive audits:

1. **Cross-Reference Audit**: All 545 chapters x 445 modules x 4,547 registry entries verified
2. **Content Audit**: 220 audit units checked for bidirectional consistency
3. **Codebase Audit**: 745 documentation fixes applied across 235 files

Audit reports are available in the `audits/` directory.
