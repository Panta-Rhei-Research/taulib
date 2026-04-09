# Formalization Status

This document provides a detailed inventory of TauLib's formalization coverage, axiom usage, and sorry count.

---

## Summary

| Metric | Value |
|--------|------:|
| Total modules | 450 |
| Total lines | 125,771 |
| Theorems & lemmas | 4,332 |
| Definitions | 3,542 |
| Structures & types | 1,685 |
| Computations (`#eval`) | 3,721 |
| Examples | 350 |
| Axioms | 4 |
| Sorry | 3 |

---

## Per-Book Breakdown

| Book | Modules | Lines | Theorems | `#eval` | Axioms | Sorry |
|------|--------:|------:|---------:|--------:|-------:|------:|
| I &mdash; Foundations | 94 | 20,554 | ~900 | ~700 | 0 | **0** |
| II &mdash; Holomorphy | 65 | 18,069 | ~700 | ~500 | 0 | **0** |
| III &mdash; Spectrum | 70 | 16,807 | ~600 | ~450 | 3 | **0** |
| IV &mdash; Microcosm | 89 | 29,730 | ~1,000 | ~900 | 1 | **0** |
| V &mdash; Macrocosm | 80 | 28,394 | ~900 | ~850 | 0 | **0** |
| VI &mdash; Life | 30 | 5,221 | ~200 | ~200 | 0 | **0** |
| VII &mdash; Metaphysics | 7 | 4,278 | ~120 | ~100 | 0 | 3 |
| Tour | 8 | ~1,850 | &mdash; | &mdash; | 0 | **0** |
| **Total** | **450** | **125,771** | **~4,332** | **~3,721** | **4** | **3** |

---

## Axiom Inventory

TauLib contains exactly **4 axioms**, each explicitly declared and documented.

### Conjectural Axioms (3)

These follow the "compute-then-axiomatize" pattern: a decidable check function is verified computationally via `native_decide` at all tested finite bounds. The axiom asserts that the property holds universally.

| # | Axiom | Module | What It Asserts |
|---|-------|--------|-----------------|
| 1 | `bridge_functor_exists` | `BookIII.Bridge.BridgeAxiom` | The bridge functor from the canonical enrichment ladder to the spectral decomposition exists for all n |
| 2 | `spectral_correspondence_O3` | `BookIII.Doors.SpectralCorrespondence` | The O(3) spectral correspondence holds universally |
| 3 | `grand_grh_adelic` | `BookIII.Doors.GrandGRH` | The adelic Generalized Riemann Hypothesis (used for spectral completeness) |

### Structural Axiom (1)

| # | Axiom | Module | What It Asserts |
|---|-------|--------|-----------------|
| 4 | `central_theorem_physical` | `BookIV.Arena.BoundaryHolonomy` | The Central Theorem O(&tau;&sup3;) &cong; A<sub>spec</sub>(&Lscr;) holds in the physical interpretation; references the algebraic proof in Book II |

---

## Sorry Inventory

TauLib contains exactly **3 sorry**, all in Book VII. Each is typed `True := sorry` &mdash; the goal is trivially `True`, and the sorry marks a philosophical boundary where formalization itself is the content under discussion.

| # | Theorem | Module | Why Sorry |
|---|---------|--------|-----------|
| 1 | `omega_point_theorem` | `BookVII.Logos.Sector` | Involves &omega;, which is non-diagrammatic by design (K2: &rho;(&omega;) = &omega;). The theorem asserts convergence toward the &omega;-attractor, which lies outside the diagrammatic fragment. |
| 2 | `science_faith_boundary` | `BookVII.Logos.Sector` | Full convergence claim involves non-computable limits on &omega;-directed sequences. The boundary between science and faith is itself the philosophical content. |
| 3 | `no_forced_stance` | `BookVII.Final.Boundary` | Asserts that the lemniscate closure does not force a metaphysical stance. This is a meta-theorem about the framework's neutrality, and formalizing it fully would require the framework to step outside itself. |

**Key property:** All three sorry are reachable only through Book VII's philosophical modules. No mathematical or physical result in Books I&ndash;VI depends on any sorry.

---

## Scope Tier Distribution

Every module and registry entry carries a scope label from the [4-tier system](SCOPE_LABELS.md):

| Tier | Meaning | Approximate Coverage |
|------|---------|---------------------|
| **established** | Classical mathematics, independently verifiable | Books I&ndash;II foundations, standard analysis |
| **&tau;-effective** | Quantitative prediction derived from &iota;<sub>&tau;</sub> | Most of Books IV&ndash;V physics |
| **conjectural** | Structural claim, computationally verified | 3 axioms in Book III, select Book V claims |
| **metaphorical** | Philosophical/analogical | Book VII ethics and metaphysics |

---

## Verification Chain

The trust chain from axioms to results:

```
Lean 4 kernel (trusted)
    │
    ├── Lean core library (Nat, Prop, etc.)
    │
    ├── Mathlib tactics (simp, omega, ring, decide, ...)
    │       └── No mathematical content imported
    │
    └── TauLib
            ├── 7 axioms K0–K6 (K0 implicit in Lean's type system)
            │       └── 6 structural axioms → all of Book I
            │
            ├── 4 explicit axioms (3 conjectural, 1 structural)
            │       └── Isolated in Book III/IV; not needed for Books I–II
            │
            ├── 3 sorry (methodological, Book VII only)
            │       └── All typed True := sorry; no mathematical dependency
            │
            └── 4,332 theorems + 3,721 #eval computations
                    └── Verified by Lean's kernel
```

---

## What "Zero Sorry in Books I&ndash;VI" Means

This is the strongest claim a Lean formalization can make short of being fully axiom-free:

1. **Every theorem** in Books I&ndash;VI has a complete proof term verified by Lean's kernel
2. **Every `#eval`** produces a concrete value at compile time
3. **No `sorry`** appears anywhere in the proof terms of Books I&ndash;VI
4. The 4 `axiom` declarations are explicit, auditable, and isolated

The 3 sorry in Book VII are philosophical design choices, not gaps in mathematical reasoning.
