-- ========== PROLOGUE (Part 0) ==========
import TauLib.BookII.Prologue.SplitComplexInterior

-- ========== INTERIOR (Part I) ==========
import TauLib.BookII.Interior.TauAdmissible
import TauLib.BookII.Interior.OmegaReadout
import TauLib.BookII.Interior.Tau3Fibration
import TauLib.BookII.Interior.BipolarDecomposition
import TauLib.BookII.Interior.ABCDRigidity

-- ========== DOMAINS (Part II) ==========
import TauLib.BookII.Domains.Cylinders
import TauLib.BookII.Domains.Ultrametric
import TauLib.BookII.Domains.HolImpliesCont

-- ========== TOPOLOGY (Part III) ==========
import TauLib.BookII.Topology.StoneSpace
import TauLib.BookII.Topology.Invariant
import TauLib.BookII.Topology.DimensionFour
import TauLib.BookII.Topology.BoundaryMinimality
import TauLib.BookII.Topology.TorusDegeneration
import TauLib.BookII.Topology.CoherenceConnectivity

-- ========== GEOMETRY (Part IV-A) ==========
import TauLib.BookII.Geometry.Betweenness
import TauLib.BookII.Geometry.Congruence
import TauLib.BookII.Geometry.CausalStructure

-- ========== GEOMETRY (Part IV-B) ==========
import TauLib.BookII.Geometry.PaschParallel
import TauLib.BookII.Geometry.OrthodoxBridge

-- ========== TRANSCENDENTALS (Part V) ==========
import TauLib.BookII.Transcendentals.Lines
import TauLib.BookII.Transcendentals.Circles
import TauLib.BookII.Transcendentals.PiEarned
import TauLib.BookII.Transcendentals.EEarned
import TauLib.BookII.Transcendentals.JReplacesI
import TauLib.BookII.Transcendentals.IotaTauConfirmed

-- ========== HARTOGS (Part VI-A) ==========
import TauLib.BookII.Hartogs.CalibratedSplitComplex
import TauLib.BookII.Hartogs.BndLift
import TauLib.BookII.Hartogs.MutualDetermination
import TauLib.BookII.Hartogs.EvolutionOperator

-- ========== HARTOGS (Part VI-B) ==========
import TauLib.BookII.Hartogs.CategoryStructure
import TauLib.BookII.Hartogs.LaurentResidue
import TauLib.BookII.Hartogs.CanonicalBasis
import TauLib.BookII.Hartogs.SheafCoherence
import TauLib.BookII.Hartogs.L2Space

-- ========== REGULARITY (Part VII) ==========
import TauLib.BookII.Regularity.IdempotentDecomposition
import TauLib.BookII.Regularity.ThreeLemmaChain
import TauLib.BookII.Regularity.PositiveRegularity
import TauLib.BookII.Regularity.PreYoneda
import TauLib.BookII.Regularity.CodeDecode

-- ========== ENRICHMENT (Part VIII) ==========
import TauLib.BookII.Enrichment.SelfEnrichment
import TauLib.BookII.Enrichment.YonedaTheorem
import TauLib.BookII.Enrichment.TwoCategories
import TauLib.BookII.Enrichment.SelfDescribing
import TauLib.BookII.Enrichment.EnrichmentLadder
import TauLib.BookII.Enrichment.Homological

-- ========== CENTRAL THEOREM (Part IX) ==========
import TauLib.BookII.CentralTheorem.BoundaryCharacters
import TauLib.BookII.CentralTheorem.HartogsExtension
import TauLib.BookII.CentralTheorem.ExtensionsOmegaGerms
import TauLib.BookII.CentralTheorem.YonedaApplied
import TauLib.BookII.CentralTheorem.CentralTheorem
import TauLib.BookII.CentralTheorem.Categoricity
import TauLib.BookII.CentralTheorem.SheafCohomology

-- ========== CLOSURE (Part X) ==========
import TauLib.BookII.Closure.TauManifold
import TauLib.BookII.Closure.DiffGeoAgenda
import TauLib.BookII.Closure.BSDbridge
import TauLib.BookII.Closure.ForwardBook3
import TauLib.BookII.Closure.GeometricBiSquare
import TauLib.BookII.Closure.Connection
import TauLib.BookII.Closure.Curvature

-- ========== MIRROR (Part XI) ==========
import TauLib.BookII.Mirror.SignClassification
import TauLib.BookII.Mirror.WaveHolomorphy
import TauLib.BookII.Mirror.Inventory
import TauLib.BookII.Mirror.PhysicsQuadrant
import TauLib.BookII.Mirror.DimensionalLadder

/-!
# TauLib Book II — Categorical Holomorphy

All Lean 4 modules corresponding to Book II (Parts 0–XI).
65 chapters, ~162 registry entries, 60 modules, zero sorry.

## Structure

- **Prologue** (Part 0): Split-complex codomain H_τ
- **Interior** (Part I): τ-admissible points, ω-readout, τ³ fibration
- **Domains** (Part II): Cylinders, ultrametric, Hol ⟹ Continuous
- **Topology** (Part III): Stone space, dimension, torus degeneration
- **Geometry** (Part IV): Betweenness, congruence, parallel, causal structure
- **Transcendentals** (Part V): Lines, circles, π, e, j, ι_τ
- **Hartogs** (Part VI): Mutual Determination, evolution, sheaf coherence
- **Regularity** (Part VII): Idempotent decomposition, 3-lemma chain, pre-Yoneda
- **Enrichment** (Part VIII): Self-enrichment, Yoneda, 2-categories
- **CentralTheorem** (Part IX): Boundary characters → O(τ³) ≅ A_spec(ℒ)
- **Closure** (Part X): τ-manifold, diff-geo agenda, BSD bridge, Book III export
- **Mirror** (Part XI): Sign classification, wave holomorphy, physics quadrant
-/
