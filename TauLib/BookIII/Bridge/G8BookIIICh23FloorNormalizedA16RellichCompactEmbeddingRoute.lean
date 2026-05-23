import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA16CompactEmbedding

/-!
# G8 Book III Ch.23 Floor-Normalized A1.6 Rellich Compact Embedding Route

This module refines the first live A1.6 analytic payload:

```text
graph-norm H2 control
  + finite two-lobe Rellich compactness
  + closed Kirchhoff subspace stability
  + compact-inclusion assembly
  -> selected operator-domain compact embedding into L2
```

The closed A1.2 trace/Kirchhoff closure supplies the subspace-stability side.
The genuine compact-analysis theorems remain proof-carrying targets.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- GRAPH-NORM H2 CONTROL
-- ============================================================

/-- Proof-facing source for the graph-norm estimate that controls edgewise
    `H2` data on the two selected lobes. -/
structure
    G8BookIIICh23FloorNormalizedA16GraphNormH2ControlSource
    where
  selfAdjoint :
    G8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource
  selectedA13Closed :
    selfAdjoint.a13 =
      g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed
  selectedA15Closed :
    selfAdjoint.a15Maximality =
      g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_closed
  edgewiseNegativeSecondDerivativeLaw :
    selfAdjoint.a13.edgewiseNegativeSecondDerivative
  operatorGraphNormBoundsValueL2 : Prop
  operatorGraphNormBoundsValueL2Witness :
    operatorGraphNormBoundsValueL2
  operatorGraphNormBoundsSecondDerivativeL2 : Prop
  operatorGraphNormBoundsSecondDerivativeL2Witness :
    operatorGraphNormBoundsSecondDerivativeL2
  compactGraphOneDimensionalEllipticEstimate : Prop
  compactGraphOneDimensionalEllipticEstimateWitness :
    compactGraphOneDimensionalEllipticEstimate
  graphNormControlsEdgewiseH2 : Prop
  graphNormControlsEdgewiseH2Witness :
    graphNormControlsEdgewiseH2
  noFiniteSpectrumDiagnosticUsed : Prop
  noFiniteSpectrumDiagnosticUsedWitness :
    noFiniteSpectrumDiagnosticUsed
  status : SpineStatus := .conditional_interface

/-- Exact graph-norm/H2-control target. -/
def G8BookIIICh23FloorNormalizedA16GraphNormH2ControlTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA16GraphNormH2ControlSource

/-- A graph-norm/H2-control source proves its target. -/
theorem
    G8BookIIICh23FloorNormalizedA16GraphNormH2ControlSource.toTarget
    (source :
      G8BookIIICh23FloorNormalizedA16GraphNormH2ControlSource) :
    G8BookIIICh23FloorNormalizedA16GraphNormH2ControlTarget :=
  ⟨source⟩

-- ============================================================
-- FINITE TWO-LOBE RELLICH COMPACTNESS
-- ============================================================

/-- Proof-facing source for the compactness theorem on the finite two-lobe
    graph. -/
structure
    G8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichSource
    where
  compactGraphEvidence :
    G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget
  hilbertDomainEvidence :
    G8BookIIICh23FloorNormalizedA12HilbertDomainSourceTarget
  finiteTwoLobeMeasure :
    g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
      |>.domain
      |>.trace
      |>.hilbert
      |>.measure
      |>.graphMeasureFromTwoLobeLength
  plusLobeRellichCompactness : Prop
  plusLobeRellichCompactnessWitness :
    plusLobeRellichCompactness
  minusLobeRellichCompactness : Prop
  minusLobeRellichCompactnessWitness :
    minusLobeRellichCompactness
  finiteDirectSumRellichCompactness : Prop
  finiteDirectSumRellichCompactnessWitness :
    finiteDirectSumRellichCompactness
  compactnessInSelectedL2 : Prop
  compactnessInSelectedL2Witness :
    compactnessInSelectedL2
  noPointSpectrumOrModeEnumerationUsed : Prop
  noPointSpectrumOrModeEnumerationUsedWitness :
    noPointSpectrumOrModeEnumerationUsed
  status : SpineStatus := .conditional_interface

/-- Exact finite two-lobe Rellich target. -/
def G8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichSource

/-- A finite two-lobe Rellich source proves its target. -/
theorem
    G8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichSource.toTarget
    (source :
      G8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichSource) :
    G8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichTarget :=
  ⟨source⟩

-- ============================================================
-- CLOSED KIRCHHOFF SUBSPACE STABILITY
-- ============================================================

/-- The closed selected A1.2 trace/Kirchhoff package supplies the closed
    subspace side of the Rellich route. -/
structure
    G8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilitySource
    where
  domain :
    G8BookIIICh23FloorNormalizedA12HilbertDomainSource
  domainClosed :
    domain = g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
  crossingClosure :
    domain.domain.crossingClosureFromBasepointTrace
  kirchhoffClosure :
    domain.domain.kirchhoffClosureFromOutgoingDerivativeBalance
  traceContinuity :
    domain.domain.trace.valueTraceContinuous ∧
      domain.domain.trace.derivativeTraceContinuous
  selectedKirchhoffSubspaceClosedInGraphNorm : Prop
  selectedKirchhoffSubspaceClosedInGraphNormWitness :
    selectedKirchhoffSubspaceClosedInGraphNorm
  status : SpineStatus := .conditional_interface

/-- Closed subspace-stability target. -/
def
    G8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilityTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilitySource

/-- The selected A1.2 closure data theorem-backs the closed-subspace stability
    source used by A1.6. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilitySource_closed :
    G8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilitySource where
  domain := g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
  domainClosed := rfl
  crossingClosure :=
    g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
      |>.domain
      |>.crossingClosureFromBasepointTraceWitness
  kirchhoffClosure :=
    g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
      |>.domain
      |>.kirchhoffClosureFromOutgoingDerivativeBalanceWitness
  traceContinuity :=
    ⟨g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
        |>.domain
        |>.trace
        |>.valueTraceContinuousWitness,
      g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
        |>.domain
        |>.trace
        |>.derivativeTraceContinuousWitness⟩
  selectedKirchhoffSubspaceClosedInGraphNorm :=
    (g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
        |>.domain
        |>.crossingClosureFromBasepointTrace) ∧
      (g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
          |>.domain
          |>.kirchhoffClosureFromOutgoingDerivativeBalance)
  selectedKirchhoffSubspaceClosedInGraphNormWitness :=
    ⟨g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
        |>.domain
        |>.crossingClosureFromBasepointTraceWitness,
      g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
        |>.domain
        |>.kirchhoffClosureFromOutgoingDerivativeBalanceWitness⟩
  status := .conditional_interface

/-- Target-level closure of the selected Kirchhoff closed-subspace side. -/
theorem
    g8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilityTarget_closed :
    G8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilityTarget :=
  ⟨g8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilitySource_closed⟩

-- ============================================================
-- RELLICH ROUTE ASSEMBLY
-- ============================================================

/-- Assembly source for the selected compact embedding.  The final assembly
    field is the exact theorem that the three preceding analytic stones produce
    compact inclusion of the selected operator domain into `L2`. -/
structure
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteSource
    where
  graphNorm :
    G8BookIIICh23FloorNormalizedA16GraphNormH2ControlSource
  finiteRellich :
    G8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichSource
  closedSubspace :
    G8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilitySource
  rellichAssemblyProducesCompactEmbedding : Prop
  rellichAssemblyProducesCompactEmbeddingWitness :
    rellichAssemblyProducesCompactEmbedding
  assemblyUsesOnlyCompactGraphAnalysis : Prop
  assemblyUsesOnlyCompactGraphAnalysisWitness :
    assemblyUsesOnlyCompactGraphAnalysis
  status : SpineStatus := .conditional_interface

/-- Exact selected Rellich-route target. -/
def
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteSource

/-- A Rellich route source proves its target. -/
theorem
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteSource.toTarget
    (source :
      G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteSource) :
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteTarget :=
  ⟨source⟩

/-- Convert the refined Rellich route into the existing compact-embedding
    source consumed by the later A1.6 resolvent module. -/
def
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteSource.toRellichCompactEmbeddingSource
    (source :
      G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteSource) :
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource where
  selfAdjoint := source.graphNorm.selfAdjoint
  compactGraphEvidence := source.finiteRellich.compactGraphEvidence
  hilbertDomainEvidence := source.finiteRellich.hilbertDomainEvidence
  graphNormControlsEdgewiseH2 :=
    source.graphNorm.graphNormControlsEdgewiseH2
  graphNormControlsEdgewiseH2Witness :=
    source.graphNorm.graphNormControlsEdgewiseH2Witness
  finiteTwoLobeRellichEmbedding :=
    source.finiteRellich.compactnessInSelectedL2
  finiteTwoLobeRellichEmbeddingWitness :=
    source.finiteRellich.compactnessInSelectedL2Witness
  kirchhoffDomainClosedInGraphNorm :=
    source.closedSubspace.selectedKirchhoffSubspaceClosedInGraphNorm
  kirchhoffDomainClosedInGraphNormWitness :=
    source.closedSubspace.selectedKirchhoffSubspaceClosedInGraphNormWitness
  compactOperatorDomainEmbeddingIntoL2 :=
    source.rellichAssemblyProducesCompactEmbedding
  compactOperatorDomainEmbeddingIntoL2Witness :=
    source.rellichAssemblyProducesCompactEmbeddingWitness
  noFiniteSpectrumDiagnosticUsed :=
    source.graphNorm.noFiniteSpectrumDiagnosticUsed ∧
      source.finiteRellich.noPointSpectrumOrModeEnumerationUsed ∧
        source.assemblyUsesOnlyCompactGraphAnalysis
  noFiniteSpectrumDiagnosticUsedWitness :=
    ⟨source.graphNorm.noFiniteSpectrumDiagnosticUsedWitness,
      source.finiteRellich.noPointSpectrumOrModeEnumerationUsedWitness,
      source.assemblyUsesOnlyCompactGraphAnalysisWitness⟩
  status := source.status

/-- Target-level adapter from the refined Rellich route to the existing compact
    embedding target. -/
theorem
    g8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingTarget_ofRoute
    (target :
      G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteTarget) :
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingTarget :=
  match target with
  | ⟨source⟩ => ⟨source.toRellichCompactEmbeddingSource⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- H2 control and finite two-lobe Rellich do not yield the compact embedding
    without the closed Kirchhoff-subspace theorem. -/
structure
    G8BookIIICh23FloorNormalizedA16RellichRouteWithoutClosedSubspace
    where
  graphNorm :
    G8BookIIICh23FloorNormalizedA16GraphNormH2ControlSource
  finiteRellich :
    G8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichSource
  missingClosedSubspace :
    ¬ G8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilityTarget

theorem
    G8BookIIICh23FloorNormalizedA16RellichRouteWithoutClosedSubspace.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA16RellichRouteWithoutClosedSubspace) :
    False :=
  gap.missingClosedSubspace
    g8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilityTarget_closed

/-- A claimed route that omits the compact-inclusion assembly theorem is still
    not the selected Rellich compact embedding. -/
structure
    G8BookIIICh23FloorNormalizedA16RellichStonesWithoutAssembly
    where
  graphNorm :
    G8BookIIICh23FloorNormalizedA16GraphNormH2ControlSource
  finiteRellich :
    G8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichSource
  closedSubspace :
    G8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilitySource
  noAssembly :
    ¬ G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteTarget

theorem
    G8BookIIICh23FloorNormalizedA16RellichStonesWithoutAssembly.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA16RellichStonesWithoutAssembly)
    (target :
      G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteTarget) :
    False :=
  gap.noAssembly target

end Tau.BookIII.Bridge
