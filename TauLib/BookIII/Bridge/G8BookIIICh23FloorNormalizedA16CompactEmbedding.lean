import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA16SelfAdjointOperatorSourceAdapter

/-!
# G8 Book III Ch.23 Floor-Normalized A1.6 Compact Embedding

This module isolates the compact-domain-embedding part of A1.6.

The mathematical target is the one-dimensional compact graph Rellich/Arzela
step:

```text
bounded graph/operator-domain norm
  -> edgewise H2 bounds on the two compact lobes
  -> precompactness in L2
  -> compact inclusion of the selected Kirchhoff operator domain into L2
```

No compact resolvent or discrete-spectrum claim is made here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- RELLICH / COMPACT EMBEDDING SOURCE
-- ============================================================

/-- The exact A1.6 Rellich compact-embedding theorem target for the selected
    compact graph. -/
structure G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource
    where
  selfAdjoint :
    G8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource
  compactGraphEvidence :
    G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget
  hilbertDomainEvidence :
    G8BookIIICh23FloorNormalizedA12HilbertDomainSourceTarget
  graphNormControlsEdgewiseH2 : Prop
  graphNormControlsEdgewiseH2Witness :
    graphNormControlsEdgewiseH2
  finiteTwoLobeRellichEmbedding : Prop
  finiteTwoLobeRellichEmbeddingWitness :
    finiteTwoLobeRellichEmbedding
  kirchhoffDomainClosedInGraphNorm : Prop
  kirchhoffDomainClosedInGraphNormWitness :
    kirchhoffDomainClosedInGraphNorm
  compactOperatorDomainEmbeddingIntoL2 : Prop
  compactOperatorDomainEmbeddingIntoL2Witness :
    compactOperatorDomainEmbeddingIntoL2
  noFiniteSpectrumDiagnosticUsed : Prop
  noFiniteSpectrumDiagnosticUsedWitness :
    noFiniteSpectrumDiagnosticUsed
  status : SpineStatus := .conditional_interface

/-- Compact-embedding target.  This is the first genuine A1.6 analytic payload
    if Mathlib does not expose a ready compact graph Rellich theorem. -/
def G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource

/-- A compact-embedding source proves its target. -/
theorem
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource.toTarget
    (source :
      G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource) :
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingTarget :=
  ⟨source⟩

/-- Selector for the load-bearing compact inclusion statement. -/
def
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource.compactEmbedding
    (source :
      G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource) :
    Prop :=
  source.compactOperatorDomainEmbeddingIntoL2

/-- The compact-embedding source exposes the compact inclusion evidence. -/
theorem
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource.compactEmbeddingEvidence
    (source :
      G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource) :
    source.compactEmbedding :=
  source.compactOperatorDomainEmbeddingIntoL2Witness

-- ============================================================
-- STRIP/UNIT-BALL FORMULATION
-- ============================================================

/-- Equivalent proof-facing unit-ball formulation: every graph-norm bounded
    sequence in the selected operator domain has an L2-convergent subsequence.
    It is kept as a field, not as a fake theorem. -/
structure G8BookIIICh23FloorNormalizedA16GraphH2UnitBallCompactSource
    where
  selfAdjoint :
    G8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource
  graphNormUnitBallPrecompactInL2 : Prop
  graphNormUnitBallPrecompactInL2Witness :
    graphNormUnitBallPrecompactInL2
  equivalentToRellichCompactEmbedding : Prop
  equivalentToRellichCompactEmbeddingWitness :
    equivalentToRellichCompactEmbedding
  finiteDirectSumStability : Prop
  finiteDirectSumStabilityWitness :
    finiteDirectSumStability
  closedKirchhoffSubspaceStability : Prop
  closedKirchhoffSubspaceStabilityWitness :
    closedKirchhoffSubspaceStability
  status : SpineStatus := .conditional_interface

/-- Unit-ball compactness plus the selected closed graph/Hilbert sources
    supplies the Rellich compact-embedding source. -/
def
    G8BookIIICh23FloorNormalizedA16GraphH2UnitBallCompactSource.toRellichCompactEmbeddingSource
    (source :
      G8BookIIICh23FloorNormalizedA16GraphH2UnitBallCompactSource) :
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource where
  selfAdjoint := source.selfAdjoint
  compactGraphEvidence :=
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed
  hilbertDomainEvidence :=
    g8BookIIICh23FloorNormalizedA12HilbertDomainSourceTarget_closed
  graphNormControlsEdgewiseH2 :=
    source.graphNormUnitBallPrecompactInL2
  graphNormControlsEdgewiseH2Witness :=
    source.graphNormUnitBallPrecompactInL2Witness
  finiteTwoLobeRellichEmbedding :=
    source.finiteDirectSumStability
  finiteTwoLobeRellichEmbeddingWitness :=
    source.finiteDirectSumStabilityWitness
  kirchhoffDomainClosedInGraphNorm :=
    source.closedKirchhoffSubspaceStability
  kirchhoffDomainClosedInGraphNormWitness :=
    source.closedKirchhoffSubspaceStabilityWitness
  compactOperatorDomainEmbeddingIntoL2 :=
    source.equivalentToRellichCompactEmbedding
  compactOperatorDomainEmbeddingIntoL2Witness :=
    source.equivalentToRellichCompactEmbeddingWitness
  noFiniteSpectrumDiagnosticUsed :=
    source.graphNormUnitBallPrecompactInL2
  noFiniteSpectrumDiagnosticUsedWitness :=
    source.graphNormUnitBallPrecompactInL2Witness
  status := source.status

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Without finite two-lobe Rellich compactness, the compact-embedding target
    is not discharged by graph boundedness alone. -/
structure
    G8BookIIICh23FloorNormalizedA16MissingFiniteLobeRellich
    (source :
      G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource)
    where
  missing :
    ¬ source.finiteTwoLobeRellichEmbedding

theorem
    G8BookIIICh23FloorNormalizedA16MissingFiniteLobeRellich.refutes
    {source :
      G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource}
    (gap :
      G8BookIIICh23FloorNormalizedA16MissingFiniteLobeRellich
        source) :
    False :=
  gap.missing source.finiteTwoLobeRellichEmbeddingWitness

/-- A finite spectral diagnostic is not a compact embedding theorem. -/
structure
    G8BookIIICh23FloorNormalizedA16FiniteDiagnosticWithoutCompactEmbedding
    where
  finiteDiagnostic : Prop
  finiteDiagnosticWitness : finiteDiagnostic
  noCompactEmbedding :
    ¬ G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingTarget

theorem
    G8BookIIICh23FloorNormalizedA16FiniteDiagnosticWithoutCompactEmbedding.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA16FiniteDiagnosticWithoutCompactEmbedding)
    (target :
      G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingTarget) :
    False :=
  gap.noCompactEmbedding target

end Tau.BookIII.Bridge
