# Architecture

## Module Dependency Graph

TauLib's modules follow a strict dependency order. Each layer builds only on what came before.

```
Book I (Foundations)
  Kernel ─→ Orbit ─→ Denotation ─→ Coordinates
                                        │
                                   Polarity ─→ Boundary
                                        │          │
                                    Sets, Logic    Holomorphy
                                        │          │
                                      Topos ───────┘
                                        │
                                    MetaLogic
                                        │
                                       CF

Book II (Holomorphy)
  Interior ─→ Domains ─→ Topology ─→ Geometry
      │
  Transcendentals ─→ Enrichment ─→ CentralTheorem
      │
  Regularity ─→ Hartogs ─→ Closure ─→ Mirror

Book III (Spectrum)
  Enrichment ─→ Sectors ─→ Spectral ─→ Arithmetic
      │
  Bridge ─→ Computation ─→ Doors ─→ Hinge
      │
  Physics ─→ Mirror ─→ Spectrum (TTM)

Books IV–VII build on I–III
  BookIV (Microcosm) ──→ BookV (Macrocosm) ──→ BookVI (Life) ──→ BookVII (Metaphysics)
```

## Reading Paths by Audience

### For Mathematicians

**"Show me the axioms and what they imply."**

1. `BookI/Kernel/Signature.lean` — The 5 generators and ρ operator
2. `BookI/Kernel/Axioms.lean` — Axioms K1–K6
3. `BookI/Orbit/Rigidity.lean` — Aut(τ) = {id} (categoricity)
4. `BookI/Boundary/Iota.lean` — The master constant ι_τ = 2/(π+e)
5. `BookII/CentralTheorem/CentralTheorem.lean` — O(τ³) ≅ A_spec(L)
6. `BookIII/Bridge/BridgeAxiom.lean` — The one conjectural gap

### For Physicists

**"Show me the predictions."**

1. `Tour/Physics.lean` — Interactive overview of all key predictions
2. `BookIV/Electroweak/EWSynthesis.lean` — 9 EW quantities from ι_τ + m_n
3. `BookIV/Particles/ThreeGenerations.lean` — Why exactly 3 generations
4. `BookV/Cosmology/CMBSpectrum.lean` — CMB first peak at +69 ppm
5. `BookV/Astrophysics/RotationCurves.lean` — 20 galaxies, no dark matter
6. `BookV/Cosmology/BaryogenesisAsymmetry.lean` — Baryon asymmetry from ι_τ¹⁵

### For Lean Users

**"Show me how it's built."**

1. `Tour/Foundations.lean` — Interactive walkthrough of the axioms
2. `lakefile.lean` — Mathlib tactics-only dependency policy
3. `BookI/Kernel/Axioms.lean` — See how axioms become Lean theorems
4. `BookI/Boundary/SplitComplex.lean` — Ring axioms from scratch
5. `BookI/Sets/CantorRefutation.lean` — Cantor's theorem fails in τ
6. Browse any module — all 445 files have 30+ line docstring headers

### For Philosophers

**"Show me the ethics and metaphysics."**

1. `BookVII/Meta/Saturation.lean` — Enrichment ladder terminates at E₃
2. `BookVII/Meta/Archetypes.lean` — Three minimal j-closed fixed points
3. `BookVII/Ethics/CIProof.lean` — The Categorical Imperative as theorem
4. `BookVII/Social/Ontology.lean` — Social ontology formalized
5. `BookVII/Final/Boundary.lean` — The three methodological sorry

## Per-Book Start Files

| Book | Start Here | What You'll Find |
|------|-----------|-----------------|
| I | `BookI/Kernel/Signature.lean` | The 5 generators — where everything begins |
| II | `BookII/Interior/Tau3Fibration.lean` | The τ³ = τ¹ ×_f T² construction |
| III | `BookIII/Enrichment/CanonicalLadder.lean` | The E₀ ⊊ E₁ ⊊ E₂ ⊊ E₃ ladder |
| IV | `BookIV/Sectors/SectorParameters.lean` | The 5 sector decomposition |
| V | `BookV/Gravity/GravitationalConstant.lean` | G from the torus vacuum |
| VI | `BookVI/LifeCore/Distinction.lean` | The 5-condition life predicate |
| VII | `BookVII/Meta/Saturation.lean` | Saturation theorem |

## Module Counts

| Book | Families | Files | Lines | Axioms | Sorry |
|------|:--------:|------:|------:|:------:|:-----:|
| I &mdash; Foundations | 12 | 94 | 20,554 | 0 | 0 |
| II &mdash; Holomorphy | 12 | 65 | 18,069 | 0 | 0 |
| III &mdash; Spectrum | 12 | 70 | 16,807 | 3 | 0 |
| IV &mdash; Microcosm | 11 | 89 | 29,730 | 1 | 0 |
| V &mdash; Macrocosm | 10 | 80 | 28,394 | 0 | 0 |
| VI &mdash; Life | 9 | 30 | 5,221 | 0 | 0 |
| VII &mdash; Metaphysics | 5 | 7 | 4,278 | 0 | 3 |
| Tour | &mdash; | 3 | 674 | 0 | 0 |
| **Total** | **71** | **445** | **124,684** | **4** | **3** |

See [Formalization Status](FORMALIZATION_STATUS.md) for the full axiom and sorry inventory.
