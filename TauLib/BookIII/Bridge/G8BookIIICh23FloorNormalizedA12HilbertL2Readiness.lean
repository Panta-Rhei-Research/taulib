import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA12GraphMeasureIdentification

/-!
# G8 Book III Ch.23 Floor-Normalized A1.2 Hilbert/L2 Readiness

This module closes the selected-carrier Hilbert/L2 readiness layer over the
closed floor-normalized graph measure.

It deliberately stops before the Sobolev trace theorem and Kirchhoff-domain
closure.  The trace fields required by the existing Hilbert readiness surface
are filled only at the Hilbert/L2 availability level: the graph has a selected
crossing and a compact metric/measure substrate on which later Sobolev trace
readiness can be stated.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CLOSED SELECTED GRAPH MEASURE
-- ============================================================

/-- The theorem-backed selected graph-measure source obtained from the closed
    crossing atom and two-lobe graph-length identification. -/
noncomputable def g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed :
    G8BookIIICh23FloorNormalizedA12GraphMeasureSource :=
  g8BookIIICh23FloorNormalizedA12GraphMeasureIdentificationSource_closed
    |>.toCrossingAndGraphMeasureLawSource
    |>.toGraphLengthMeasureLawSource
    |>.toGraphMeasureSource

/-- A graph-measure source is the closed selected Ch.23 graph measure. -/
def G8BookIIICh23FloorNormalizedA12ClosedSelectedGraphMeasure
    (measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource) :
    Prop :=
  measure = g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed

/-- The closed graph-measure source is, definitionally, the selected closed
    graph measure. -/
theorem
    g8BookIIICh23FloorNormalizedA12ClosedSelectedGraphMeasure_closed :
    G8BookIIICh23FloorNormalizedA12ClosedSelectedGraphMeasure
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed :=
  rfl

/-- The closed selected graph measure still discharges the existing
    graph-measure target. -/
theorem
    g8BookIIICh23FloorNormalizedA12GraphMeasureTarget_closed_fromSource :
    G8BookIIICh23FloorNormalizedA12GraphMeasureTarget :=
  g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed.toTarget

-- ============================================================
-- HILBERT/L2 LAW PREDICATES OVER THE CLOSED GRAPH MEASURE
-- ============================================================

/-- Symmetry is tied to the selected B/C lobe length agreement. -/
def G8BookIIICh23FloorNormalizedA12InnerProductSymmetric
    (measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12ClosedSelectedGraphMeasure measure ∧
    measure.lobeMeasureAgreement

/-- Positivity is the nonnegative selected graph-length density. -/
def G8BookIIICh23FloorNormalizedA12InnerProductPositive
    (measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource) :
    Prop :=
  ∀ x : G8BookIIICh23FloorNormalizedLemniscateCarrier,
    0 ≤ measure.weight x

/-- Completeness is recorded at the Hilbert/L2 package level from finite
    total graph length, compactness, and topology/metric agreement. -/
def G8BookIIICh23FloorNormalizedA12InnerProductComplete
    (measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12ClosedSelectedGraphMeasure measure ∧
    measure.totalFinite ∧
    G8BookIIICh23FloorNormalizedCompactnessTransferred
      measure.graph.concrete ∧
    G8BookIIICh23FloorNormalizedTopologyMetricAgreement
      measure.graph.concrete

/-- The inner product is compatible with the closed selected graph measure when
    it uses the two-lobe length law and the zero crossing-atom policy. -/
def
    G8BookIIICh23FloorNormalizedA12InnerProductCompatibleWithMeasure
    (measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12ClosedSelectedGraphMeasure measure ∧
    measure.graphMeasureFromTwoLobeLength ∧
    measure.crossingAtomPolicy

/-- Hilbert-level trace maps are available on the selected compact graph.  This
    is not the Sobolev trace theorem; it only records the selected crossing and
    quotient substrate used by the later trace-readiness layer. -/
def G8BookIIICh23FloorNormalizedA12HilbertTraceMapDefined
    (measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12ClosedSelectedGraphMeasure measure ∧
    G8BookIIICh23FloorNormalizedQuotientMatchesConcrete ∧
    measure.crossingAtomPolicy

/-- Hilbert-level trace continuity is recorded only as compact metric/finite
    measure availability for the later Sobolev trace theorem. -/
def G8BookIIICh23FloorNormalizedA12HilbertTraceMapContinuous
    (measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12ClosedSelectedGraphMeasure measure ∧
    G8BookIIICh23FloorNormalizedTopologyMetricAgreement
      measure.graph.concrete ∧
    measure.totalFinite

/-- Quotient completion is the selected compact finite-measure L2 completion
    substrate. -/
def G8BookIIICh23FloorNormalizedA12QuotientCompletionConstructed
    (measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12ClosedSelectedGraphMeasure measure ∧
    measure.totalFinite ∧
    G8BookIIICh23FloorNormalizedCompactnessTransferred
      measure.graph.concrete

/-- The L2 completion is built from the selected graph measure once the
    quotient completion, completeness, and measure compatibility laws are all
    present. -/
def G8BookIIICh23FloorNormalizedA12L2CompletionFromGraphMeasure
    (measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA12QuotientCompletionConstructed measure ∧
    G8BookIIICh23FloorNormalizedA12InnerProductComplete measure ∧
    G8BookIIICh23FloorNormalizedA12InnerProductCompatibleWithMeasure
      measure

-- ============================================================
-- CLOSED LAW WITNESSES
-- ============================================================

theorem
    g8BookIIICh23FloorNormalizedA12InnerProductSymmetric_closed :
    G8BookIIICh23FloorNormalizedA12InnerProductSymmetric
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
      |>.lobeMeasureAgreementWitness⟩

theorem
    g8BookIIICh23FloorNormalizedA12InnerProductPositive_closed :
    G8BookIIICh23FloorNormalizedA12InnerProductPositive
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed :=
  g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
    |>.nonnegative

theorem
    g8BookIIICh23FloorNormalizedA12InnerProductComplete_closed :
    G8BookIIICh23FloorNormalizedA12InnerProductComplete
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
      |>.totalFiniteWitness,
    g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
      |>.graph
      |>.compactnessTransferred,
    g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
      |>.graph
      |>.topologyMetricAgreement⟩

theorem
    g8BookIIICh23FloorNormalizedA12InnerProductCompatibleWithMeasure_closed :
    G8BookIIICh23FloorNormalizedA12InnerProductCompatibleWithMeasure
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
      |>.graphMeasureFromTwoLobeLengthEvidence,
    g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
      |>.crossingAtomPolicyWitness⟩

theorem
    g8BookIIICh23FloorNormalizedA12HilbertTraceMapDefined_closed :
    G8BookIIICh23FloorNormalizedA12HilbertTraceMapDefined
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
      |>.graph
      |>.quotientMatchesConcrete,
    g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
      |>.crossingAtomPolicyWitness⟩

theorem
    g8BookIIICh23FloorNormalizedA12HilbertTraceMapContinuous_closed :
    G8BookIIICh23FloorNormalizedA12HilbertTraceMapContinuous
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
      |>.graph
      |>.topologyMetricAgreement,
    g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
      |>.totalFiniteWitness⟩

theorem
    g8BookIIICh23FloorNormalizedA12QuotientCompletionConstructed_closed :
    G8BookIIICh23FloorNormalizedA12QuotientCompletionConstructed
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
      |>.totalFiniteWitness,
    g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
      |>.graph
      |>.compactnessTransferred⟩

theorem
    g8BookIIICh23FloorNormalizedA12L2CompletionFromGraphMeasure_closed :
    G8BookIIICh23FloorNormalizedA12L2CompletionFromGraphMeasure
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed :=
  ⟨g8BookIIICh23FloorNormalizedA12QuotientCompletionConstructed_closed,
    g8BookIIICh23FloorNormalizedA12InnerProductComplete_closed,
    g8BookIIICh23FloorNormalizedA12InnerProductCompatibleWithMeasure_closed⟩

-- ============================================================
-- CLOSED HILBERT/L2 SOURCES
-- ============================================================

/-- Closed inner-product readiness source over the selected graph measure. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA12InnerProductSource_closed :
    G8BookIIICh23FloorNormalizedA12InnerProductSource where
  measure := g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
  innerProductSymmetric :=
    G8BookIIICh23FloorNormalizedA12InnerProductSymmetric
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
  innerProductSymmetricWitness :=
    g8BookIIICh23FloorNormalizedA12InnerProductSymmetric_closed
  innerProductPositive :=
    G8BookIIICh23FloorNormalizedA12InnerProductPositive
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
  innerProductPositiveWitness :=
    g8BookIIICh23FloorNormalizedA12InnerProductPositive_closed
  innerProductComplete :=
    G8BookIIICh23FloorNormalizedA12InnerProductComplete
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
  innerProductCompleteWitness :=
    g8BookIIICh23FloorNormalizedA12InnerProductComplete_closed
  innerProductCompatibleWithMeasure :=
    G8BookIIICh23FloorNormalizedA12InnerProductCompatibleWithMeasure
      g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
  innerProductCompatibleWithMeasureWitness :=
    g8BookIIICh23FloorNormalizedA12InnerProductCompatibleWithMeasure_closed
  status := .conditional_interface

/-- Pure Hilbert/L2 readiness before the later Sobolev trace and Kirchhoff
    domain layers. -/
structure G8BookIIICh23FloorNormalizedA12HilbertL2ReadinessSource where
  measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource
  innerProduct : G8BookIIICh23FloorNormalizedA12InnerProductSource
  innerProductUsesMeasure : innerProduct.measure = measure
  quotientCompletionConstructed :
    G8BookIIICh23FloorNormalizedA12QuotientCompletionConstructed
      measure
  l2CompletionFromGraphMeasure :
    G8BookIIICh23FloorNormalizedA12L2CompletionFromGraphMeasure
      measure
  status : SpineStatus := .conditional_interface

/-- Target for the pure selected Hilbert/L2 readiness layer. -/
def G8BookIIICh23FloorNormalizedA12HilbertL2ReadinessTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA12HilbertL2ReadinessSource

/-- Closed pure Hilbert/L2 readiness over the selected graph measure. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA12HilbertL2ReadinessSource_closed :
    G8BookIIICh23FloorNormalizedA12HilbertL2ReadinessSource where
  measure := g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
  innerProduct :=
    g8BookIIICh23FloorNormalizedA12InnerProductSource_closed
  innerProductUsesMeasure := rfl
  quotientCompletionConstructed :=
    g8BookIIICh23FloorNormalizedA12QuotientCompletionConstructed_closed
  l2CompletionFromGraphMeasure :=
    g8BookIIICh23FloorNormalizedA12L2CompletionFromGraphMeasure_closed
  status := .conditional_interface

/-- The selected Hilbert/L2 readiness target is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA12HilbertL2ReadinessTarget_closed :
    G8BookIIICh23FloorNormalizedA12HilbertL2ReadinessTarget :=
  ⟨g8BookIIICh23FloorNormalizedA12HilbertL2ReadinessSource_closed⟩

/-- Hilbert-level trace availability needed to inhabit the existing Hilbert
    readiness surface.  Sobolev value/derivative trace readiness remains a
    separate A1.2 step. -/
structure G8BookIIICh23FloorNormalizedA12HilbertTraceAvailabilitySource where
  measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource
  traceMapDefined :
    G8BookIIICh23FloorNormalizedA12HilbertTraceMapDefined measure
  traceMapContinuous :
    G8BookIIICh23FloorNormalizedA12HilbertTraceMapContinuous measure
  status : SpineStatus := .conditional_interface

/-- Closed Hilbert-level trace availability over the selected graph measure. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA12HilbertTraceAvailabilitySource_closed :
    G8BookIIICh23FloorNormalizedA12HilbertTraceAvailabilitySource where
  measure := g8BookIIICh23FloorNormalizedA12GraphMeasureSource_closed
  traceMapDefined :=
    g8BookIIICh23FloorNormalizedA12HilbertTraceMapDefined_closed
  traceMapContinuous :=
    g8BookIIICh23FloorNormalizedA12HilbertTraceMapContinuous_closed
  status := .conditional_interface

/-- Pure Hilbert/L2 readiness plus Hilbert-level trace availability supplies
    the existing selected Hilbert-readiness source. -/
def
    G8BookIIICh23FloorNormalizedA12HilbertL2ReadinessSource.toHilbertReadinessSource
    (source :
      G8BookIIICh23FloorNormalizedA12HilbertL2ReadinessSource)
    (trace :
      G8BookIIICh23FloorNormalizedA12HilbertTraceAvailabilitySource)
    (traceUsesMeasure : trace.measure = source.measure) :
    G8BookIIICh23FloorNormalizedA12HilbertReadinessSource where
  measure := source.measure
  innerProduct := source.innerProduct
  innerProductUsesMeasure := source.innerProductUsesMeasure
  traceMapDefined :=
    G8BookIIICh23FloorNormalizedA12HilbertTraceMapDefined
      source.measure
  traceMapDefinedWitness := by
    exact traceUsesMeasure ▸ trace.traceMapDefined
  traceMapContinuous :=
    G8BookIIICh23FloorNormalizedA12HilbertTraceMapContinuous
      source.measure
  traceMapContinuousWitness := by
    exact traceUsesMeasure ▸ trace.traceMapContinuous
  quotientCompletionConstructed :=
    G8BookIIICh23FloorNormalizedA12QuotientCompletionConstructed
      source.measure
  quotientCompletionConstructedWitness :=
    source.quotientCompletionConstructed
  l2CompletionFromGraphMeasure :=
    G8BookIIICh23FloorNormalizedA12L2CompletionFromGraphMeasure
      source.measure
  l2CompletionFromGraphMeasureEvidence :=
    source.l2CompletionFromGraphMeasure
  status := source.status

/-- Closed selected Hilbert-readiness source over the theorem-backed graph
    measure. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed :
    G8BookIIICh23FloorNormalizedA12HilbertReadinessSource :=
  g8BookIIICh23FloorNormalizedA12HilbertL2ReadinessSource_closed
    |>.toHilbertReadinessSource
      g8BookIIICh23FloorNormalizedA12HilbertTraceAvailabilitySource_closed
      rfl

/-- The existing selected-carrier Hilbert/L2 readiness target is now closed. -/
theorem
    g8BookIIICh23FloorNormalizedA12HilbertReadinessTarget_closed :
    G8BookIIICh23FloorNormalizedA12HilbertReadinessTarget :=
  g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed.toTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A pure Hilbert/L2 source with the wrong inner-product measure is invalid. -/
structure G8BookIIICh23FloorNormalizedA12HilbertL2WrongMeasure
    (source :
      G8BookIIICh23FloorNormalizedA12HilbertL2ReadinessSource) where
  wrongMeasure :
    source.innerProduct.measure ≠ source.measure

theorem
    G8BookIIICh23FloorNormalizedA12HilbertL2WrongMeasure.refutes
    {source :
      G8BookIIICh23FloorNormalizedA12HilbertL2ReadinessSource}
    (gap :
      G8BookIIICh23FloorNormalizedA12HilbertL2WrongMeasure source) :
    False :=
  gap.wrongMeasure source.innerProductUsesMeasure

/-- Missing selected graph-measure closure refutes the closed Hilbert/L2 law
    predicates. -/
structure G8BookIIICh23FloorNormalizedA12HilbertL2WithoutClosedMeasure
    (measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource) where
  notClosed :
    ¬ G8BookIIICh23FloorNormalizedA12ClosedSelectedGraphMeasure measure

theorem
    G8BookIIICh23FloorNormalizedA12HilbertL2WithoutClosedMeasure.refutesSymmetry
    {measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource}
    (gap :
      G8BookIIICh23FloorNormalizedA12HilbertL2WithoutClosedMeasure
        measure) :
    ¬ G8BookIIICh23FloorNormalizedA12InnerProductSymmetric measure := by
  intro h
  exact gap.notClosed h.1

theorem
    G8BookIIICh23FloorNormalizedA12HilbertL2WithoutClosedMeasure.refutesCompatibility
    {measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource}
    (gap :
      G8BookIIICh23FloorNormalizedA12HilbertL2WithoutClosedMeasure
        measure) :
    ¬
      G8BookIIICh23FloorNormalizedA12InnerProductCompatibleWithMeasure
        measure := by
  intro h
  exact gap.notClosed h.1

/-- Hilbert/L2 readiness alone is not the Sobolev trace-readiness target. -/
structure G8BookIIICh23FloorNormalizedA12HilbertL2WithoutSobolevTrace where
  hilbert : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource
  noSobolevTrace :
    ¬ G8BookIIICh23FloorNormalizedA12TraceReadinessTarget

theorem
    G8BookIIICh23FloorNormalizedA12HilbertL2WithoutSobolevTrace.refutesTraceTarget
    (gap :
      G8BookIIICh23FloorNormalizedA12HilbertL2WithoutSobolevTrace) :
    ¬ G8BookIIICh23FloorNormalizedA12TraceReadinessTarget :=
  gap.noSobolevTrace

end Tau.BookIII.Bridge
