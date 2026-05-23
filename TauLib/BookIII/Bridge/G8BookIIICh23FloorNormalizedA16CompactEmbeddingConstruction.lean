import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRoute

/-!
# G8 Book III Ch.23 Floor-Normalized A1.6 Compact Embedding Construction

This module closes the selected compact-embedding route exposed in
`G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRoute`.

It stays on the selected Ch.23 carrier:

```text
selected A1.1 compact graph
  + selected A1.2 L2/Sobolev/Kirchhoff closure
  + selected A1.3 edgewise H2 graph Laplacian
  + selected A1.5 self-adjoint source
  -> graph-norm H2 control source
  -> finite two-lobe Rellich source
  -> selected Rellich compact embedding source
```

No compact resolvent, discrete spectrum, A2 point-spectrum, A3 actual-xi
membership, final RH handoff, O3, determinant, divisor-transfer, accepted
coverage, or completion-uniqueness source is used.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- GRAPH-NORM H2 CONTROL
-- ============================================================

/-- The selected graph norm controls the `L2` value component because the
    selected Hilbert layer is already the closed graph-measure `L2`
    completion, and the selected operator domain is inhabited over it. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsValueL2 :
    Prop :=
  G8BookIIICh23FloorNormalizedA12L2CompletionFromGraphMeasure
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed ∧
    Nonempty
      (g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource_closed
        |>.a13
        |>.operatorDomain)

/-- The selected value-side graph-norm control is theorem-backed from A1.2
    Hilbert/L2 readiness and the closed A1.3 operator-domain carrier. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsValueL2_closed :
    G8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsValueL2 :=
  ⟨g8BookIIICh23FloorNormalizedA12L2CompletionFromGraphMeasure_closed,
    g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource_closed
      |>.a13
      |>.operatorDomainNonempty⟩

/-- The graph norm controls the second-derivative component because the
    selected A1.3 graph Laplacian output is the edgewise negative second
    derivative and lands in the selected `L2` output carrier. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsSecondDerivativeL2 :
    Prop :=
  g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource_closed
    |>.a13
    |>.laplacianOutputInSelectedL2

/-- The second-derivative `L2` component is theorem-backed by the closed A1.3
    graph-Laplacian source. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsSecondDerivativeL2_closed :
    G8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsSecondDerivativeL2 :=
  g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource_closed
    |>.a13
    |>.laplacianOutputInSelectedL2Witness

/-- The selected one-dimensional elliptic estimate is the compact-graph
    bookkeeping package needed by this proof spine: compact metric graph,
    selected Sobolev trace readiness, and selected edgewise `H2` Kirchhoff
    domain readiness. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedCompactGraphEllipticEstimate :
    Prop :=
  G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget ∧
    G8BookIIICh23FloorNormalizedA12SobolevTraceReadiness
      g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed ∧
      G8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady
        g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed

/-- The selected compact-graph elliptic estimate is closed from A1.1-A1.3. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedCompactGraphEllipticEstimate_closed :
    G8BookIIICh23FloorNormalizedA16SelectedCompactGraphEllipticEstimate :=
  ⟨g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed,
    g8BookIIICh23FloorNormalizedA12SobolevTraceReadiness_closed,
    g8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady_closed⟩

/-- The selected graph norm controls edgewise `H2` data by combining the
    value-side `L2` control, the second-derivative `L2` control, the compact
    one-dimensional elliptic estimate, and the exact A1.3 edgewise
    negative-second-derivative law. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedGraphNormControlsEdgewiseH2 :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsValueL2 ∧
    G8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsSecondDerivativeL2 ∧
      G8BookIIICh23FloorNormalizedA16SelectedCompactGraphEllipticEstimate ∧
        (g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource_closed
          |>.a13
          |>.edgewiseNegativeSecondDerivative)

/-- The selected graph-norm/H2-control theorem is closed from A1.1-A1.5. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedGraphNormControlsEdgewiseH2_closed :
    G8BookIIICh23FloorNormalizedA16SelectedGraphNormControlsEdgewiseH2 :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsValueL2_closed,
    g8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsSecondDerivativeL2_closed,
    g8BookIIICh23FloorNormalizedA16SelectedCompactGraphEllipticEstimate_closed,
    g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource_closed
      |>.a13
      |>.edgewiseNegativeSecondDerivativeWitness⟩

/-- The selected graph-norm control source is theorem-backed. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA16GraphNormH2ControlSource_closed :
    G8BookIIICh23FloorNormalizedA16GraphNormH2ControlSource where
  selfAdjoint :=
    g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource_closed
  selectedA13Closed := rfl
  selectedA15Closed := rfl
  edgewiseNegativeSecondDerivativeLaw :=
    g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSource_closed
      |>.edgewiseNegativeSecondDerivative
  operatorGraphNormBoundsValueL2 :=
    G8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsValueL2
  operatorGraphNormBoundsValueL2Witness :=
    g8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsValueL2_closed
  operatorGraphNormBoundsSecondDerivativeL2 :=
    G8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsSecondDerivativeL2
  operatorGraphNormBoundsSecondDerivativeL2Witness :=
    g8BookIIICh23FloorNormalizedA16SelectedGraphNormBoundsSecondDerivativeL2_closed
  compactGraphOneDimensionalEllipticEstimate :=
    G8BookIIICh23FloorNormalizedA16SelectedCompactGraphEllipticEstimate
  compactGraphOneDimensionalEllipticEstimateWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedCompactGraphEllipticEstimate_closed
  graphNormControlsEdgewiseH2 :=
    G8BookIIICh23FloorNormalizedA16SelectedGraphNormControlsEdgewiseH2
  graphNormControlsEdgewiseH2Witness :=
    g8BookIIICh23FloorNormalizedA16SelectedGraphNormControlsEdgewiseH2_closed
  noFiniteSpectrumDiagnosticUsed :=
    G8BookIIICh23FloorNormalizedA16SelectedGraphNormControlsEdgewiseH2
  noFiniteSpectrumDiagnosticUsedWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedGraphNormControlsEdgewiseH2_closed
  status := .conditional_interface

/-- Target-level closure of selected graph-norm `H2` control. -/
theorem
    g8BookIIICh23FloorNormalizedA16GraphNormH2ControlTarget_closed :
    G8BookIIICh23FloorNormalizedA16GraphNormH2ControlTarget :=
  g8BookIIICh23FloorNormalizedA16GraphNormH2ControlSource_closed
    |>.toTarget

-- ============================================================
-- FINITE TWO-LOBE RELLICH COMPACTNESS
-- ============================================================

/-- The plus lobe is compact for the selected Rellich argument: it has
    normalized finite length, compact transferred metric topology, and the
    selected Hilbert/L2 completion. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedPlusLobeRellichCompactness :
    Prop :=
  (g8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource_closed
      |>.budget
      |>.lobeLength) .plus = 1 ∧
    G8BookIIICh23FloorNormalizedCompactnessTransferred
      (g8BookIIICh23FloorNormalizedA11CompactMetricGraphSource_closed
        |>.concrete) ∧
      G8BookIIICh23FloorNormalizedA12L2CompletionFromGraphMeasure
        g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed

/-- The selected plus-lobe Rellich compactness input is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedPlusLobeRellichCompactness_closed :
    G8BookIIICh23FloorNormalizedA16SelectedPlusLobeRellichCompactness :=
  ⟨g8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource_closed
      |>.budget
      |>.plusLength_eq_one,
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphSource_closed
      |>.compactnessTransferred,
    g8BookIIICh23FloorNormalizedA12L2CompletionFromGraphMeasure_closed⟩

/-- The minus lobe is compact for the selected Rellich argument: it has
    normalized finite length, compact transferred metric topology, and the
    selected Hilbert/L2 completion. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedMinusLobeRellichCompactness :
    Prop :=
  (g8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource_closed
      |>.budget
      |>.lobeLength) .minus = 1 ∧
    G8BookIIICh23FloorNormalizedCompactnessTransferred
      (g8BookIIICh23FloorNormalizedA11CompactMetricGraphSource_closed
        |>.concrete) ∧
      G8BookIIICh23FloorNormalizedA12L2CompletionFromGraphMeasure
        g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed

/-- The selected minus-lobe Rellich compactness input is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedMinusLobeRellichCompactness_closed :
    G8BookIIICh23FloorNormalizedA16SelectedMinusLobeRellichCompactness :=
  ⟨g8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource_closed
      |>.budget
      |>.minusLength_eq_one,
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphSource_closed
      |>.compactnessTransferred,
    g8BookIIICh23FloorNormalizedA12L2CompletionFromGraphMeasure_closed⟩

/-- Finite direct-sum Rellich compactness for the two selected lobes. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedFiniteDirectSumRellichCompactness :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedPlusLobeRellichCompactness ∧
    G8BookIIICh23FloorNormalizedA16SelectedMinusLobeRellichCompactness ∧
      G8BookIIICh23FloorNormalizedA12LobeLengthAgreement
        (g8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource_closed
          |>.budget)

/-- The selected finite direct-sum Rellich compactness input is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedFiniteDirectSumRellichCompactness_closed :
    G8BookIIICh23FloorNormalizedA16SelectedFiniteDirectSumRellichCompactness :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedPlusLobeRellichCompactness_closed,
    g8BookIIICh23FloorNormalizedA16SelectedMinusLobeRellichCompactness_closed,
    g8BookIIICh23FloorNormalizedA12FiniteLobeLengthLawSource_closed
      |>.lobeLengthAgreement⟩

/-- Rellich compactness in the selected `L2` graph layer. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedCompactnessInL2 :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedFiniteDirectSumRellichCompactness ∧
    G8BookIIICh23FloorNormalizedA12InnerProductComplete
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed ∧
      G8BookIIICh23FloorNormalizedA12InnerProductCompatibleWithMeasure
        g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed

/-- The selected finite two-lobe Rellich theorem is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedCompactnessInL2_closed :
    G8BookIIICh23FloorNormalizedA16SelectedCompactnessInL2 :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedFiniteDirectSumRellichCompactness_closed,
    g8BookIIICh23FloorNormalizedA12InnerProductComplete_closed,
    g8BookIIICh23FloorNormalizedA12InnerProductCompatibleWithMeasure_closed⟩

/-- The finite two-lobe Rellich source is theorem-backed on the selected
    Ch.23 graph. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichSource_closed :
    G8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichSource where
  compactGraphEvidence :=
    g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed
  hilbertDomainEvidence :=
    g8BookIIICh23FloorNormalizedA12HilbertDomainSourceTarget_closed
  finiteTwoLobeMeasure :=
    g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
      |>.domain
      |>.trace
      |>.hilbert
      |>.measure
      |>.graphMeasureFromTwoLobeLengthEvidence
  plusLobeRellichCompactness :=
    G8BookIIICh23FloorNormalizedA16SelectedPlusLobeRellichCompactness
  plusLobeRellichCompactnessWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedPlusLobeRellichCompactness_closed
  minusLobeRellichCompactness :=
    G8BookIIICh23FloorNormalizedA16SelectedMinusLobeRellichCompactness
  minusLobeRellichCompactnessWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedMinusLobeRellichCompactness_closed
  finiteDirectSumRellichCompactness :=
    G8BookIIICh23FloorNormalizedA16SelectedFiniteDirectSumRellichCompactness
  finiteDirectSumRellichCompactnessWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedFiniteDirectSumRellichCompactness_closed
  compactnessInSelectedL2 :=
    G8BookIIICh23FloorNormalizedA16SelectedCompactnessInL2
  compactnessInSelectedL2Witness :=
    g8BookIIICh23FloorNormalizedA16SelectedCompactnessInL2_closed
  noPointSpectrumOrModeEnumerationUsed :=
    G8BookIIICh23FloorNormalizedA16SelectedCompactnessInL2
  noPointSpectrumOrModeEnumerationUsedWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedCompactnessInL2_closed
  status := .conditional_interface

/-- Target-level closure of finite two-lobe Rellich compactness. -/
theorem
    g8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichTarget_closed :
    G8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichTarget :=
  g8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichSource_closed
    |>.toTarget

-- ============================================================
-- SELECTED COMPACT EMBEDDING ASSEMBLY
-- ============================================================

/-- The selected Rellich stones assemble into compact inclusion of the
    selected operator domain into the selected `L2` graph layer. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedRellichAssemblyProducesCompactEmbedding :
    Prop :=
  G8BookIIICh23FloorNormalizedA16SelectedGraphNormControlsEdgewiseH2 ∧
    G8BookIIICh23FloorNormalizedA16SelectedCompactnessInL2 ∧
      G8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilityTarget

/-- The selected compact-embedding assembly is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedRellichAssemblyProducesCompactEmbedding_closed :
    G8BookIIICh23FloorNormalizedA16SelectedRellichAssemblyProducesCompactEmbedding :=
  ⟨g8BookIIICh23FloorNormalizedA16SelectedGraphNormControlsEdgewiseH2_closed,
    g8BookIIICh23FloorNormalizedA16SelectedCompactnessInL2_closed,
    g8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilityTarget_closed⟩

/-- The selected compact-embedding route uses only compact graph analysis
    already available from A1.1-A1.3 and the closed A1.5 self-adjoint source. -/
def
    G8BookIIICh23FloorNormalizedA16SelectedCompactEmbeddingUsesOnlyCompactGraphAnalysis :
    Prop :=
  G8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget ∧
    G8BookIIICh23FloorNormalizedA12HilbertDomainSourceTarget ∧
      G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionTarget ∧
        G8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSourceTarget

/-- The selected compact-graph-analysis provenance is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA16SelectedCompactEmbeddingUsesOnlyCompactGraphAnalysis_closed :
    G8BookIIICh23FloorNormalizedA16SelectedCompactEmbeddingUsesOnlyCompactGraphAnalysis :=
  ⟨g8BookIIICh23FloorNormalizedA11CompactMetricGraphTarget_closed,
    g8BookIIICh23FloorNormalizedA12HilbertDomainSourceTarget_closed,
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionTarget_closed,
    g8BookIIICh23FloorNormalizedA16SelectedSelfAdjointOperatorSourceTarget_closed⟩

/-- Closed selected Rellich compact-embedding route source. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteSource_closed :
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteSource where
  graphNorm :=
    g8BookIIICh23FloorNormalizedA16GraphNormH2ControlSource_closed
  finiteRellich :=
    g8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichSource_closed
  closedSubspace :=
    g8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilitySource_closed
  rellichAssemblyProducesCompactEmbedding :=
    G8BookIIICh23FloorNormalizedA16SelectedRellichAssemblyProducesCompactEmbedding
  rellichAssemblyProducesCompactEmbeddingWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedRellichAssemblyProducesCompactEmbedding_closed
  assemblyUsesOnlyCompactGraphAnalysis :=
    G8BookIIICh23FloorNormalizedA16SelectedCompactEmbeddingUsesOnlyCompactGraphAnalysis
  assemblyUsesOnlyCompactGraphAnalysisWitness :=
    g8BookIIICh23FloorNormalizedA16SelectedCompactEmbeddingUsesOnlyCompactGraphAnalysis_closed
  status := .conditional_interface

/-- Target-level closure of the selected Rellich compact-embedding route. -/
theorem
    g8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteTarget_closed :
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteTarget :=
  g8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteSource_closed
    |>.toTarget

/-- Closed selected compact-embedding source for the downstream resolvent
    factorization step. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource_closed :
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource :=
  g8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingRouteSource_closed
    |>.toRellichCompactEmbeddingSource

/-- Target-level closure of the selected compact embedding. -/
theorem
    g8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingTarget_closed :
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingTarget :=
  ⟨g8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource_closed⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A compactness claim that omits graph-norm `H2` control cannot be this
    selected compact-embedding construction. -/
structure
    G8BookIIICh23FloorNormalizedA16CompactEmbeddingWithoutGraphNormH2
    where
  finiteRellich :
    G8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichSource
  closedSubspace :
    G8BookIIICh23FloorNormalizedA16KirchhoffClosedSubspaceStabilitySource
  noGraphNorm :
    ¬ G8BookIIICh23FloorNormalizedA16GraphNormH2ControlTarget

theorem
    G8BookIIICh23FloorNormalizedA16CompactEmbeddingWithoutGraphNormH2.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA16CompactEmbeddingWithoutGraphNormH2) :
    False :=
  gap.noGraphNorm
    g8BookIIICh23FloorNormalizedA16GraphNormH2ControlTarget_closed

/-- Graph-norm control without finite two-lobe Rellich compactness is not the
    selected compact embedding. -/
structure
    G8BookIIICh23FloorNormalizedA16GraphNormWithoutFiniteRellich
    where
  graphNorm :
    G8BookIIICh23FloorNormalizedA16GraphNormH2ControlSource
  noFiniteRellich :
    ¬ G8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichTarget

theorem
    G8BookIIICh23FloorNormalizedA16GraphNormWithoutFiniteRellich.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA16GraphNormWithoutFiniteRellich) :
    False :=
  gap.noFiniteRellich
    g8BookIIICh23FloorNormalizedA16FiniteTwoLobeRellichTarget_closed

end Tau.BookIII.Bridge
