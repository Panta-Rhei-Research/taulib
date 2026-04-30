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

### For Skeptics / Reviewers

**"I don't believe this. Show me the evidence."**

1. `Tour/VerifyItYourself.lean` — 5 extraordinary claims, verified live
2. `Tour/OneConstant.lean` — Full constants ledger from ι_τ alone
3. `BookIII/Bridge/BridgeAxiom.lean` — The scope ledger: what is proved vs. conjectured

### For Physicists

**"Show me the predictions."**

1. `Tour/Physics.lean` — Interactive overview of all key predictions
2. `Tour/OneConstant.lean` — α, h, ℓ₁, ω_b, r — all from ι_τ
3. `BookIV/Electroweak/EWSynthesis.lean` — 9 EW quantities from ι_τ + m_n
4. `BookV/Cosmology/CMBSpectrum.lean` — CMB first peak at +69 ppm
5. `BookV/Astrophysics/RotationCurves.lean` — 20 galaxies, no dark matter

### For Mathematicians

**"Show me the proofs."**

1. `Tour/Foundations.lean` — 5 generators, 7 axioms, rigidity
2. `Tour/CentralTheorem.lean` — O(τ³) ≅ A_spec(L) holographic isomorphism
3. `Tour/MillenniumProblems.lean` — GRH, BSD, Poincaré through the τ-lens
4. `BookI/Orbit/Rigidity.lean` — Aut(τ) = {id}
5. `BookIII/Doors/GrandGRH.lean` — Spectral reformulation of RH

### For Biologists

**"Show me how life emerges."**

1. `Tour/LifeFromPhysics.lean` — 4+1 life sectors, genetic code, neural arch
2. `BookVI/Source/GeneticCode.lean` — Codon degeneracy as error correction
3. `BookVI/Consumer/Neural.lean` — Neural architecture as τ³ computer
4. `BookVI/CosmicLife/CrossLimit.lean` — The Crossing-Limit Theorem

### For Philosophers

**"Show me the ethics and metaphysics."**

1. `Tour/MindAndEthics.lean` — CI formalization, consciousness, free will, Logos
2. `BookVII/Ethics/CIProof.lean` — The Categorical Imperative as theorem
3. `BookVII/Logos/Sector.lean` — Consciousness as global section
4. `BookVII/Final/Boundary.lean` — Boundary commitments encoded as inspectable data
5. `BookVII/Social/Ontology.lean` — Social ontology as sheaf theory

### For Lean Users

**"Show me how it's built."**

1. `Tour/Foundations.lean` — Interactive walkthrough of the axioms
2. `lakefile.lean` — Mathlib tactics-only dependency policy
3. `BookI/Kernel/Axioms.lean` — See how axioms become Lean theorems
4. Browse generated module documentation or the source tree

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

## Current Counts

This architecture note describes reading paths and module families. It does not own current counts. See the [Release Manifest](https://panta-rhei.site/verify/release-manifest/) for the authoritative module, declaration, axiom, sorry, and trusted-base status.
