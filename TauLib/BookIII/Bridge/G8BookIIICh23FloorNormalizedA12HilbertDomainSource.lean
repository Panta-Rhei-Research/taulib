import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA11CompactGraphRoute
import TauLib.BookIII.Bridge.G8BookIIILemniscateCompactMetricGraphPackage

/-!
# G8 Book III Ch.23 Floor-Normalized A1.2 Hilbert Domain Source

This module starts A1.2 from the theorem-backed floor-normalized A1.1
compact graph route.

The key lesson from A1.1 is preserved here:

```text
selected Ch.23 carrier first;
old raw `LemniscateCarrier` only through an explicit exact bridge.
```

Accordingly, this file defines the selected-carrier graph-measure,
Hilbert/L2, trace, and Kirchhoff-domain proof surfaces, then proves adapters
into the existing raw `LemniscateCarrier` A1.2 interfaces when an exact
raw-carrier transfer is supplied.

It does not construct the graph measure, Sobolev trace theorem, or Kirchhoff
closure theorem from analysis.  Those remain proof-carrying fields.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- SELECTED-CARRIER A1.2 GRAPH MEASURE
-- ============================================================

/-- Graph-measure source over the floor-normalized selected Ch.23 carrier.

The weight is deliberately carrier-native.  The proof fields record the
analytic content needed for A1.2: finite total length, lobe-measure agreement,
crossing-node atom policy, and the fact that this measure is the intended
two-lobe graph length measure. -/
structure G8BookIIICh23FloorNormalizedA12GraphMeasureSource where
  graph : G8BookIIICh23FloorNormalizedA11CompactMetricGraphSource
  weight : G8BookIIICh23FloorNormalizedLemniscateCarrier → ℝ
  nonnegative : ∀ x, 0 ≤ weight x
  totalFinite : Prop
  totalFiniteWitness : totalFinite
  lobeMeasureAgreement : Prop
  lobeMeasureAgreementWitness : lobeMeasureAgreement
  crossingAtomPolicy : Prop
  crossingAtomPolicyWitness : crossingAtomPolicy
  graphMeasureFromTwoLobeLength : Prop
  graphMeasureFromTwoLobeLengthEvidence :
    graphMeasureFromTwoLobeLength
  status : SpineStatus := .conditional_interface

/-- Target for the selected-carrier graph-measure theorem. -/
def G8BookIIICh23FloorNormalizedA12GraphMeasureTarget : Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA12GraphMeasureSource

/-- A selected graph-measure source proves its target. -/
theorem
    G8BookIIICh23FloorNormalizedA12GraphMeasureSource.toTarget
    (source : G8BookIIICh23FloorNormalizedA12GraphMeasureSource) :
    G8BookIIICh23FloorNormalizedA12GraphMeasureTarget :=
  ⟨source⟩

-- ============================================================
-- SELECTED-CARRIER A1.2 HILBERT/L2 READINESS
-- ============================================================

/-- Inner-product readiness for the selected floor-normalized graph L2 layer. -/
structure G8BookIIICh23FloorNormalizedA12InnerProductSource where
  measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource
  innerProductSymmetric : Prop
  innerProductSymmetricWitness : innerProductSymmetric
  innerProductPositive : Prop
  innerProductPositiveWitness : innerProductPositive
  innerProductComplete : Prop
  innerProductCompleteWitness : innerProductComplete
  innerProductCompatibleWithMeasure : Prop
  innerProductCompatibleWithMeasureWitness :
    innerProductCompatibleWithMeasure
  status : SpineStatus := .conditional_interface

/-- Hilbert/L2 readiness over the selected floor-normalized graph. -/
structure G8BookIIICh23FloorNormalizedA12HilbertReadinessSource where
  measure : G8BookIIICh23FloorNormalizedA12GraphMeasureSource
  innerProduct : G8BookIIICh23FloorNormalizedA12InnerProductSource
  innerProductUsesMeasure : innerProduct.measure = measure
  traceMapDefined : Prop
  traceMapDefinedWitness : traceMapDefined
  traceMapContinuous : Prop
  traceMapContinuousWitness : traceMapContinuous
  quotientCompletionConstructed : Prop
  quotientCompletionConstructedWitness :
    quotientCompletionConstructed
  l2CompletionFromGraphMeasure : Prop
  l2CompletionFromGraphMeasureEvidence :
    l2CompletionFromGraphMeasure
  status : SpineStatus := .conditional_interface

/-- Target for the selected-carrier Hilbert/L2 readiness theorem. -/
def G8BookIIICh23FloorNormalizedA12HilbertReadinessTarget : Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA12HilbertReadinessSource

/-- Hilbert readiness source proves its selected target. -/
theorem
    G8BookIIICh23FloorNormalizedA12HilbertReadinessSource.toTarget
    (source : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource) :
    G8BookIIICh23FloorNormalizedA12HilbertReadinessTarget :=
  ⟨source⟩

-- ============================================================
-- SELECTED-CARRIER A1.2 TRACE AND KIRCHHOFF DOMAIN
-- ============================================================

/-- Trace-readiness source over the selected graph.

This isolates the Sobolev trace theorem from the later Kirchhoff closure
fields. -/
structure G8BookIIICh23FloorNormalizedA12TraceReadinessSource where
  hilbert : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource
  valueTraceDefined : Prop
  valueTraceDefinedWitness : valueTraceDefined
  valueTraceContinuous : Prop
  valueTraceContinuousWitness : valueTraceContinuous
  derivativeTraceDefined : Prop
  derivativeTraceDefinedWitness : derivativeTraceDefined
  derivativeTraceContinuous : Prop
  derivativeTraceContinuousWitness : derivativeTraceContinuous
  sobolevTraceTheorem : Prop
  sobolevTraceTheoremWitness : sobolevTraceTheorem
  status : SpineStatus := .conditional_interface

/-- Target for selected-carrier Sobolev trace readiness. -/
def G8BookIIICh23FloorNormalizedA12TraceReadinessTarget : Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA12TraceReadinessSource

/-- Trace readiness source proves its selected target. -/
theorem
    G8BookIIICh23FloorNormalizedA12TraceReadinessSource.toTarget
    (source : G8BookIIICh23FloorNormalizedA12TraceReadinessSource) :
    G8BookIIICh23FloorNormalizedA12TraceReadinessTarget :=
  ⟨source⟩

/-- Kirchhoff-domain readiness source over the selected floor-normalized graph.

This is the selected-carrier A1.2 payload: trace continuity plus closed
crossing agreement and closed Kirchhoff balance. -/
structure G8BookIIICh23FloorNormalizedA12KirchhoffDomainSource where
  trace : G8BookIIICh23FloorNormalizedA12TraceReadinessSource
  crossingAgreementClosed : Prop
  crossingAgreementClosedWitness : crossingAgreementClosed
  kirchhoffConditionClosed : Prop
  kirchhoffConditionClosedWitness : kirchhoffConditionClosed
  crossingClosureFromBasepointTrace : Prop
  crossingClosureFromBasepointTraceWitness :
    crossingClosureFromBasepointTrace
  kirchhoffClosureFromOutgoingDerivativeBalance : Prop
  kirchhoffClosureFromOutgoingDerivativeBalanceWitness :
    kirchhoffClosureFromOutgoingDerivativeBalance
  status : SpineStatus := .conditional_interface

/-- Target for the selected-carrier Kirchhoff-domain theorem. -/
def G8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget : Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA12KirchhoffDomainSource

/-- Kirchhoff-domain source proves its selected target. -/
theorem
    G8BookIIICh23FloorNormalizedA12KirchhoffDomainSource.toTarget
    (source : G8BookIIICh23FloorNormalizedA12KirchhoffDomainSource) :
    G8BookIIICh23FloorNormalizedA12KirchhoffDomainTarget :=
  ⟨source⟩

/-- Combined selected-carrier A1.2 source. -/
structure G8BookIIICh23FloorNormalizedA12HilbertDomainSource where
  domain : G8BookIIICh23FloorNormalizedA12KirchhoffDomainSource
  graphMeasureIsSelectedLength :
    domain.trace.hilbert.measure.graphMeasureFromTwoLobeLength
  hilbertBuiltFromSelectedGraph :
    domain.trace.hilbert.l2CompletionFromGraphMeasure
  traceBuiltFromSelectedSobolevTheory :
    domain.trace.sobolevTraceTheorem
  kirchhoffBuiltFromSelectedTrace :
    domain.crossingClosureFromBasepointTrace ∧
      domain.kirchhoffClosureFromOutgoingDerivativeBalance
  status : SpineStatus := .conditional_interface

/-- Target for the selected-carrier A1.2 Hilbert/domain source. -/
def G8BookIIICh23FloorNormalizedA12HilbertDomainSourceTarget : Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA12HilbertDomainSource

/-- Combined selected source proves its target. -/
theorem
    G8BookIIICh23FloorNormalizedA12HilbertDomainSource.toTarget
    (source : G8BookIIICh23FloorNormalizedA12HilbertDomainSource) :
    G8BookIIICh23FloorNormalizedA12HilbertDomainSourceTarget :=
  ⟨source⟩

-- ============================================================
-- RAW-CARRIER TRANSFER INTO THE EXISTING A1.2 SURFACES
-- ============================================================

/-- The optional floor-normalized-to-raw carrier bridge supplies the existing
    compact-metric-graph package for the old `LemniscateCarrier` surface. -/
def
    G8BookIIICh23FloorNormalizedToRawLemniscateCarrierBridge.toCompactMetricGraphPackage
    (bridge : G8BookIIICh23FloorNormalizedToRawLemniscateCarrierBridge) :
    G8BookIIILemniscateCompactMetricGraphPackage where
  carrierCtx := bridge.carrierCtx
  topologyIsWedgeQuotient := bridge.topologyTransferred
  metricIsGraphMetric := bridge.metricTransferred
  compactnessFromWedge := bridge.compactnessTransferred
  topologyMetricAgreement := bridge.topologyMetricAgreement
  graphDistanceRealizesMetric := bridge.graphDistanceRealizesMetric
  theoremBackedStatus := bridge.theoremBackedStatus
  compactMetricGraphFromRawWedge :=
    bridge.exactCarrierAlignment
  compactMetricGraphFromRawWedgeEvidence :=
    bridge.exactCarrierAlignmentEvidence
  status := bridge.status

/-- Exact transfer from selected-carrier A1.2 data into the old raw-carrier
    Hilbert/Kirchhoff interface.

This is intentionally proof-carrying: it requires both the selected A1.2
source and an exact floor-normalized-to-raw carrier bridge, plus exact measure,
Hilbert, trace, and Kirchhoff agreement fields on the raw surface. -/
structure G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource where
  selected : G8BookIIICh23FloorNormalizedA12HilbertDomainSource
  rawBridge :
    G8BookIIICh23FloorNormalizedToRawLemniscateCarrierBridge
  hilbertCtx : LemniscateHilbertContext
  hilbertUsesGraph :
    hilbertCtx.measure.carrierContext = rawBridge.carrierCtx
  selectedGraphMeasureTransferredToRaw : Prop
  selectedGraphMeasureTransferredToRawEvidence :
    selectedGraphMeasureTransferredToRaw
  measureTotalFinite : hilbertCtx.measure.totalFinite
  lobeMeasureAgreement : hilbertCtx.measure.lobeMeasureAgreement
  innerProductSymmetric : hilbertCtx.innerProduct.symmetric
  innerProductPositive : hilbertCtx.innerProduct.positive
  innerProductComplete : hilbertCtx.innerProduct.complete
  innerProductCompatibleWithMeasure :
    hilbertCtx.innerProduct.compatibleWithMeasure
  traceMapDefined : hilbertCtx.traceMapDefined
  traceMapContinuous : hilbertCtx.traceMapContinuous
  quotientCompletionConstructed :
    hilbertCtx.quotientCompletionConstructed
  domainCtx : LemniscateDomainContext
  domainUsesHilbert : domainCtx.hilbert = hilbertCtx
  valueTraceDefined : domainCtx.valueTraceDefined
  valueTraceContinuous : domainCtx.valueTraceContinuous
  derivativeTraceDefined : domainCtx.derivativeTraceDefined
  derivativeTraceContinuous : domainCtx.derivativeTraceContinuous
  crossingAgreementClosed : domainCtx.crossingAgreementClosed
  kirchhoffConditionClosed : domainCtx.kirchhoffConditionClosed
  traceContinuityEvidence : Prop
  traceContinuityWitness : traceContinuityEvidence
  derivativeTraceEvidence : Prop
  derivativeTraceWitness : derivativeTraceEvidence
  crossingClosureEvidence : Prop
  crossingClosureWitness : crossingClosureEvidence
  kirchhoffClosureEvidence : Prop
  kirchhoffClosureWitness : kirchhoffClosureEvidence
  rawHilbertDomainMatchesSelectedSource : Prop
  rawHilbertDomainMatchesSelectedSourceEvidence :
    rawHilbertDomainMatchesSelectedSource
  status : SpineStatus := .conditional_interface

/-- Target for exact selected-to-raw A1.2 Hilbert/domain transfer. -/
def G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferTarget : Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource

/-- Convert the exact raw-transfer package to the existing compact-graph-keyed
    A1.2 package. -/
def
    G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource.toCompactMetricGraphKirchhoffDomainPackage
    (source :
      G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource) :
    G8BookIIILemniscateCompactMetricGraphKirchhoffDomainPackage where
  graph := source.rawBridge.toCompactMetricGraphPackage
  hilbertCtx := source.hilbertCtx
  hilbertUsesGraph := source.hilbertUsesGraph
  measureTotalFinite := source.measureTotalFinite
  lobeMeasureAgreement := source.lobeMeasureAgreement
  innerProductSymmetric := source.innerProductSymmetric
  innerProductPositive := source.innerProductPositive
  innerProductComplete := source.innerProductComplete
  innerProductCompatibleWithMeasure :=
    source.innerProductCompatibleWithMeasure
  traceMapDefined := source.traceMapDefined
  traceMapContinuous := source.traceMapContinuous
  quotientCompletionConstructed :=
    source.quotientCompletionConstructed
  domainCtx := source.domainCtx
  domainUsesHilbert := source.domainUsesHilbert
  valueTraceDefined := source.valueTraceDefined
  valueTraceContinuous := source.valueTraceContinuous
  derivativeTraceDefined := source.derivativeTraceDefined
  derivativeTraceContinuous := source.derivativeTraceContinuous
  crossingAgreementClosed := source.crossingAgreementClosed
  kirchhoffConditionClosed := source.kirchhoffConditionClosed
  traceContinuityEvidence := source.traceContinuityEvidence
  traceContinuityWitness := source.traceContinuityWitness
  derivativeTraceEvidence := source.derivativeTraceEvidence
  derivativeTraceWitness := source.derivativeTraceWitness
  crossingClosureEvidence := source.crossingClosureEvidence
  crossingClosureWitness := source.crossingClosureWitness
  kirchhoffClosureEvidence := source.kirchhoffClosureEvidence
  kirchhoffClosureWitness := source.kirchhoffClosureWitness
  status := source.status

/-- Raw-transfer source supplies the existing low-level Kirchhoff-domain
    readiness data. -/
def
    G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource.toKirchhoffDomainReadinessData
    (source :
      G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource) :
    G8BookIIILemniscateKirchhoffDomainReadinessData :=
  source.toCompactMetricGraphKirchhoffDomainPackage
    |>.toKirchhoffDomainReadinessData

/-- Raw-transfer source supplies the existing proof-map Hilbert/domain
    source. -/
def
    G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource.toHilbertDomainSource
    (source :
      G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource) :
    G8BookIIILemniscateHilbertDomainSource :=
  source.toKirchhoffDomainReadinessData.toHilbertDomainSource

/-- Raw-transfer source discharges the existing Kirchhoff-domain readiness
    target. -/
theorem
    G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource.toKirchhoffDomainReadinessTarget
    (source :
      G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource) :
    G8BookIIILemniscateKirchhoffDomainReadinessTarget :=
  ⟨source.toKirchhoffDomainReadinessData⟩

/-- Raw-transfer source discharges the proof-map Hilbert/domain source target. -/
theorem
    G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource.toHilbertDomainSourceTarget
    (source :
      G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource) :
    Nonempty G8BookIIILemniscateHilbertDomainSource :=
  ⟨source.toHilbertDomainSource⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A selected graph without graph-measure construction cannot claim A1.2
    graph-measure readiness. -/
structure G8BookIIICh23FloorNormalizedGraphWithoutMeasure where
  graph : G8BookIIICh23FloorNormalizedA11CompactMetricGraphSource
  noGraphMeasure :
    ¬ G8BookIIICh23FloorNormalizedA12GraphMeasureTarget

theorem G8BookIIICh23FloorNormalizedGraphWithoutMeasure.refutes
    (gap : G8BookIIICh23FloorNormalizedGraphWithoutMeasure) :
    ¬ G8BookIIICh23FloorNormalizedA12GraphMeasureTarget :=
  gap.noGraphMeasure

/-- A selected Hilbert source must use the selected graph measure. -/
structure G8BookIIICh23FloorNormalizedHilbertWrongMeasure
    (source : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource) where
  wrongMeasure :
    source.innerProduct.measure ≠ source.measure

theorem G8BookIIICh23FloorNormalizedHilbertWrongMeasure.refutes
    {source : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource}
    (gap : G8BookIIICh23FloorNormalizedHilbertWrongMeasure source) :
    False :=
  gap.wrongMeasure source.innerProductUsesMeasure

/-- Raw A1.2 transfer requires the exact selected-to-raw carrier bridge. -/
structure G8BookIIICh23FloorNormalizedA12WithoutRawCarrierBridge where
  selected : G8BookIIICh23FloorNormalizedA12HilbertDomainSource
  noRawBridge :
    ¬ G8BookIIICh23FloorNormalizedToRawCarrierBridgeTarget

theorem
    G8BookIIICh23FloorNormalizedA12WithoutRawCarrierBridge.refutesRawTransfer
    (gap : G8BookIIICh23FloorNormalizedA12WithoutRawCarrierBridge) :
    ¬ G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferTarget := by
  intro hTransfer
  rcases hTransfer with ⟨source⟩
  exact gap.noRawBridge ⟨source.rawBridge⟩

/-- Raw transfer also requires exact measure/Hilbert/domain agreement with
    the selected source, not merely a raw-carrier equivalence. -/
structure G8BookIIICh23FloorNormalizedA12RawAgreementGap
    (source :
      G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource) where
  missingAgreement :
    ¬ source.rawHilbertDomainMatchesSelectedSource

theorem G8BookIIICh23FloorNormalizedA12RawAgreementGap.refutes
    {source :
      G8BookIIICh23FloorNormalizedA12RawHilbertDomainTransferSource}
    (gap : G8BookIIICh23FloorNormalizedA12RawAgreementGap source) :
    False :=
  gap.missingAgreement
    source.rawHilbertDomainMatchesSelectedSourceEvidence

end Tau.BookIII.Bridge
