import TauLib.BookIII.Bridge.G8BookIIILaneAOperatorSelfAdjointProofSource
import TauLib.BookIII.Bridge.G8BookIIILemniscateTauProfiniteCompactMetricSource

/-!
# TauLib.BookIII.Bridge.G8BookIIILemniscateTauProfiniteHilbertDomainTransfer

Pure A1.1/A1.2 transfer layer for the Lane-A operator route.

`G8BookIIILemniscateTauProfiniteCompactMetricSource` closes the reusable
`TauProfinite` compact metric substrate and isolates the transfer corridor from
that substrate to the current two-lobe lemniscate carrier.  This module keeps
following the A1 proof map one small step at a time:

```text
TauProfinite compact metric substrate
  + tau-circle/profinite lobe identification
  + wedge quotient and graph-metric transfer
  + graph measure / L2 transfer
  + Sobolev trace and Kirchhoff-domain transfer
  -> A1.1 metric graph source and A1.2 Hilbert/domain source
```

The new objects are proof-carrying transfer surfaces only.  They do not
construct the τ-circle lobe equivalence, graph measure, trace continuity, or
Kirchhoff closure from finite diagnostics, and they stay upstream of actual-`xi`
membership and all RH-facing handoffs.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.Boundary

-- ============================================================
-- A1.1 TAU-CIRCLE / PROFINITE LOBE IDENTIFICATION
-- ============================================================

/-- Exact source package for identifying the current `TauCirclePoint` lobe
    model with the theorem-backed `TauProfinite` compact metric substrate.

This is the first missing transfer theorem after the closed profinite
substrate.  The maps and pullback fields are intentionally exact data: circle
trigonometric facts or finite checks do not inhabit this source. -/
structure G8BookIIILemniscateTauProfiniteLobeIdentificationSource where
  substrate : G8TauProfiniteCompactMetricSubstrate :=
    g8TauProfiniteCompactMetricSubstrate
  circleToProfinite : TauCirclePoint → TauProfinite
  profiniteToCircle : TauProfinite → TauCirclePoint
  leftInverse :
    ∀ p : TauCirclePoint, profiniteToCircle (circleToProfinite p) = p
  rightInverse :
    ∀ x : TauProfinite, circleToProfinite (profiniteToCircle x) = x
  basepointPreserved : Prop
  basepointPreservedEvidence : basepointPreserved
  topologyPulledBackFromProfinite : Prop
  topologyPulledBackFromProfiniteEvidence :
    topologyPulledBackFromProfinite
  metricPulledBackFromProfinite : Prop
  metricPulledBackFromProfiniteEvidence :
    metricPulledBackFromProfinite
  compactnessPulledBackFromProfinite : Prop
  compactnessPulledBackFromProfiniteEvidence :
    compactnessPulledBackFromProfinite
  status : SpineStatus := .conditional_interface

/-- Target for the tau-circle/profinite lobe identification theorem. -/
def G8BookIIILemniscateTauProfiniteLobeIdentificationTarget : Prop :=
  Nonempty G8BookIIILemniscateTauProfiniteLobeIdentificationSource

-- ============================================================
-- A1.1 WEDGE AND GRAPH-METRIC TRANSFER
-- ============================================================

/-- Proof-carrying transfer from profinite circle lobes to the two-lobe
    lemniscate compact metric graph.

The selected `carrierCtx` is the one consumed by downstream operator readiness.
All compactness, topology/metric agreement, and shortest-path graph-metric
fields are exact proof fields. -/
structure G8BookIIILemniscateTauProfiniteWedgeTransferSource where
  lobeIdentification :
    G8BookIIILemniscateTauProfiniteLobeIdentificationSource
  rawWedge : G8BookIIILemniscateTwoLobeWedgeCore :=
    g8BookIIILemniscateTwoLobeWedgeCore
  rawWedgeClosed : G8BookIIILemniscateTwoLobeWedgeCoreTarget :=
    g8BookIIILemniscateTwoLobeWedgeCore_closed
  rawWedge_isCanonical :
    rawWedge = g8BookIIILemniscateTwoLobeWedgeCore := by
      rfl
  carrierCtx : LemniscateCarrierContext
  twoLobeWedgeQuotientMatchesCarrier : Prop
  twoLobeWedgeQuotientMatchesCarrierEvidence :
    twoLobeWedgeQuotientMatchesCarrier
  compactnessTransfersFromProfiniteWedge : Prop
  compactnessTransfersFromProfiniteWedgeEvidence :
    compactnessTransfersFromProfiniteWedge
  graphMetricTransfersFromProfiniteLobes : Prop
  graphMetricTransfersFromProfiniteLobesEvidence :
    graphMetricTransfersFromProfiniteLobes
  topologyIsWedgeQuotient : carrierCtx.topologyIsWedgeQuotient
  metricIsGraphMetric : carrierCtx.metricIsGraphMetric
  compactnessFromWedge : carrierCtx.compactnessFromWedge
  topologyMetricAgreement : LemniscateTopologyMetricAgreement carrierCtx
  graphDistanceRealizesMetric : carrierCtx.graphDistanceRealizesMetric
  theoremBackedStatus : carrierCtx.status = .theoremBacked
  compactMetricGraphFromTauProfiniteWedge : Prop
  compactMetricGraphFromTauProfiniteWedgeEvidence :
    compactMetricGraphFromTauProfiniteWedge
  status : SpineStatus := .conditional_interface

/-- Target for the profinite lobe/wedge/graph-metric transfer theorem. -/
def G8BookIIILemniscateTauProfiniteWedgeTransferTarget : Prop :=
  Nonempty G8BookIIILemniscateTauProfiniteWedgeTransferSource

/-- The refined lobe/wedge transfer source supplies the existing compact metric
    corridor. -/
def G8BookIIILemniscateTauProfiniteWedgeTransferSource.toCompactMetricCorridor
    (source : G8BookIIILemniscateTauProfiniteWedgeTransferSource) :
    G8BookIIILemniscateTauProfiniteCompactMetricCorridor where
  substrate := source.lobeIdentification.substrate
  rawWedge := source.rawWedge
  rawWedgeClosed := source.rawWedgeClosed
  rawWedge_isCanonical := source.rawWedge_isCanonical
  carrierCtx := source.carrierCtx
  tauCircleLobesModeledByTauProfinite :=
    source.lobeIdentification.topologyPulledBackFromProfinite ∧
      source.lobeIdentification.metricPulledBackFromProfinite ∧
      source.lobeIdentification.compactnessPulledBackFromProfinite
  tauCircleLobesModeledByTauProfiniteEvidence :=
    ⟨source.lobeIdentification.topologyPulledBackFromProfiniteEvidence,
      source.lobeIdentification.metricPulledBackFromProfiniteEvidence,
      source.lobeIdentification.compactnessPulledBackFromProfiniteEvidence⟩
  twoLobeWedgeQuotientMatchesCarrier :=
    source.twoLobeWedgeQuotientMatchesCarrier
  twoLobeWedgeQuotientMatchesCarrierEvidence :=
    source.twoLobeWedgeQuotientMatchesCarrierEvidence
  compactnessTransfersFromProfiniteWedge :=
    source.compactnessTransfersFromProfiniteWedge
  compactnessTransfersFromProfiniteWedgeEvidence :=
    source.compactnessTransfersFromProfiniteWedgeEvidence
  graphMetricTransfersFromProfiniteLobes :=
    source.graphMetricTransfersFromProfiniteLobes
  graphMetricTransfersFromProfiniteLobesEvidence :=
    source.graphMetricTransfersFromProfiniteLobesEvidence
  topologyIsWedgeQuotient := source.topologyIsWedgeQuotient
  metricIsGraphMetric := source.metricIsGraphMetric
  compactnessFromWedge := source.compactnessFromWedge
  topologyMetricAgreement := source.topologyMetricAgreement
  graphDistanceRealizesMetric := source.graphDistanceRealizesMetric
  theoremBackedStatus := source.theoremBackedStatus
  compactMetricGraphFromTauProfiniteWedge :=
    source.compactMetricGraphFromTauProfiniteWedge
  compactMetricGraphFromTauProfiniteWedgeEvidence :=
    source.compactMetricGraphFromTauProfiniteWedgeEvidence
  status := source.status

/-- The refined wedge transfer source supplies the τ-native compact metric graph
    realization source. -/
def
    G8BookIIILemniscateTauProfiniteWedgeTransferSource.toTauNativeRealizationSource
    (source : G8BookIIILemniscateTauProfiniteWedgeTransferSource) :
    G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource :=
  source.toCompactMetricCorridor.toTauNativeRealizationSource

/-- The refined wedge transfer source supplies the A1.1 compact metric graph
    package. -/
def G8BookIIILemniscateTauProfiniteWedgeTransferSource.toCompactMetricGraphPackage
    (source : G8BookIIILemniscateTauProfiniteWedgeTransferSource) :
    G8BookIIILemniscateCompactMetricGraphPackage :=
  source.toTauNativeRealizationSource.toCompactMetricGraphPackage

/-- The refined wedge transfer source supplies the A1.1 metric-graph source
    consumed by the operator proof map. -/
def G8BookIIILemniscateTauProfiniteWedgeTransferSource.toMetricGraphSource
    (source : G8BookIIILemniscateTauProfiniteWedgeTransferSource) :
    G8BookIIILemniscateMetricGraphSource :=
  source.toCompactMetricGraphPackage.toMetricGraphSource

/-- The refined wedge transfer source discharges the existing compact metric
    corridor target. -/
theorem
    G8BookIIILemniscateTauProfiniteWedgeTransferSource.toCompactMetricCorridorTarget
    (source : G8BookIIILemniscateTauProfiniteWedgeTransferSource) :
    G8BookIIILemniscateTauProfiniteCompactMetricCorridorTarget :=
  ⟨source.toCompactMetricCorridor⟩

-- ============================================================
-- A1.2 GRAPH MEASURE AND KIRCHHOFF DOMAIN TRANSFER
-- ============================================================

/-- Proof-carrying transfer from the profinite compact metric graph corridor to
    the graph measure, Hilbert/L2 space, and Sobolev/Kirchhoff domain.

This is the A1.2 analogue of the compact graph corridor.  It records exactly
what still has to be proved from graph analysis: total finite graph measure,
lobe measure agreement, inner-product readiness, trace continuity, and the
closed crossing/Kirchhoff domain conditions. -/
structure G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource where
  graphTransfer : G8BookIIILemniscateTauProfiniteWedgeTransferSource
  hilbertCtx : LemniscateHilbertContext
  hilbertUsesGraph :
    hilbertCtx.measure.carrierContext = graphTransfer.carrierCtx
  graphMeasurePulledBackFromProfiniteLobes : Prop
  graphMeasurePulledBackFromProfiniteLobesEvidence :
    graphMeasurePulledBackFromProfiniteLobes
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
  sobolevDomainPulledBackFromGraphMetric : Prop
  sobolevDomainPulledBackFromGraphMetricEvidence :
    sobolevDomainPulledBackFromGraphMetric
  status : SpineStatus := .conditional_interface

/-- Target for the profinite-to-Hilbert/Kirchhoff domain transfer theorem. -/
def G8BookIIILemniscateTauProfiniteHilbertDomainTransferTarget : Prop :=
  Nonempty G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource

/-- Package the A1.2 transfer source into the compact-graph-keyed
    Hilbert/Kirchhoff package. -/
def
    G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource.toCompactMetricGraphKirchhoffDomainPackage
    (source : G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource) :
    G8BookIIILemniscateCompactMetricGraphKirchhoffDomainPackage where
  graph := source.graphTransfer.toCompactMetricGraphPackage
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

/-- The A1.2 transfer source supplies the low-level Kirchhoff-domain readiness
    data. -/
def
    G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource.toKirchhoffDomainReadinessData
    (source : G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource) :
    G8BookIIILemniscateKirchhoffDomainReadinessData :=
  source.toCompactMetricGraphKirchhoffDomainPackage.toKirchhoffDomainReadinessData

/-- The A1.2 transfer source supplies the proof-map Hilbert/domain source. -/
def G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource.toHilbertDomainSource
    (source : G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource) :
    G8BookIIILemniscateHilbertDomainSource :=
  source.toKirchhoffDomainReadinessData.toHilbertDomainSource

/-- The A1.2 transfer source discharges the existing Kirchhoff-domain readiness
    target. -/
theorem
    G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource.toKirchhoffDomainReadinessTarget
    (source : G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource) :
    G8BookIIILemniscateKirchhoffDomainReadinessTarget :=
  ⟨source.toKirchhoffDomainReadinessData⟩

/-- The A1.2 transfer source discharges the proof-map Hilbert/domain source
    target. -/
theorem
    G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource.toHilbertDomainSourceTarget
    (source : G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource) :
    Nonempty G8BookIIILemniscateHilbertDomainSource :=
  ⟨source.toHilbertDomainSource⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A lobe identification that fails to preserve the profinite pullback
    topology refutes the lobe-identification source. -/
structure G8BookIIIMissingTauProfiniteLobeTopologyPullback
    (source : G8BookIIILemniscateTauProfiniteLobeIdentificationSource) where
  missingTopologyPullback :
    ¬ source.topologyPulledBackFromProfinite

/-- Exact topology pullback is required by the lobe-identification source. -/
theorem G8BookIIIMissingTauProfiniteLobeTopologyPullback.refutes
    {source : G8BookIIILemniscateTauProfiniteLobeIdentificationSource}
    (gap : G8BookIIIMissingTauProfiniteLobeTopologyPullback source) :
    False :=
  gap.missingTopologyPullback
    source.topologyPulledBackFromProfiniteEvidence

/-- A profinite compact metric graph transfer without graph-measure transfer
    still does not construct the A1.2 Hilbert/Kirchhoff domain package. -/
structure G8BookIIITauProfiniteGraphWithoutHilbertDomainTransfer where
  graphTransfer : G8BookIIILemniscateTauProfiniteWedgeTransferSource
  noHilbertDomainTransfer :
    ¬ G8BookIIILemniscateTauProfiniteHilbertDomainTransferTarget

/-- The graph-only transfer gap refutes the A1.2 transfer target. -/
theorem
    G8BookIIITauProfiniteGraphWithoutHilbertDomainTransfer.refutesDomainTransfer
    (gap : G8BookIIITauProfiniteGraphWithoutHilbertDomainTransfer) :
    ¬ G8BookIIILemniscateTauProfiniteHilbertDomainTransferTarget :=
  gap.noHilbertDomainTransfer

/-- Missing graph-measure transfer refutes any A1.2 transfer source claiming
    that same transfer field. -/
structure G8BookIIIMissingTauProfiniteGraphMeasureTransfer
    (source :
      G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource) where
  missingGraphMeasureTransfer :
    ¬ source.graphMeasurePulledBackFromProfiniteLobes

/-- A1.2 requires exact graph-measure transfer from the profinite lobes. -/
theorem G8BookIIIMissingTauProfiniteGraphMeasureTransfer.refutes
    {source :
      G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource}
    (gap : G8BookIIIMissingTauProfiniteGraphMeasureTransfer source) :
    False :=
  gap.missingGraphMeasureTransfer
    source.graphMeasurePulledBackFromProfiniteLobesEvidence

/-- Missing Sobolev-domain transfer refutes any A1.2 transfer source claiming
    that same transfer field. -/
structure G8BookIIIMissingTauProfiniteSobolevDomainTransfer
    (source :
      G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource) where
  missingSobolevDomainTransfer :
    ¬ source.sobolevDomainPulledBackFromGraphMetric

/-- A1.2 requires exact Sobolev/Kirchhoff-domain transfer from the graph
    metric. -/
theorem G8BookIIIMissingTauProfiniteSobolevDomainTransfer.refutes
    {source :
      G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource}
    (gap : G8BookIIIMissingTauProfiniteSobolevDomainTransfer source) :
    False :=
  gap.missingSobolevDomainTransfer
    source.sobolevDomainPulledBackFromGraphMetricEvidence

/-- Finite or trigonometric diagnostics are not a substitute for the exact
    Hilbert/domain transfer theorem. -/
structure G8BookIIITauCircleDiagnosticsWithoutHilbertDomainTransfer where
  tauCircleTrigDiagnostic : Prop
  tauCircleTrigEvidence : tauCircleTrigDiagnostic
  finiteGraphDiagnostic : Prop
  finiteGraphEvidence : finiteGraphDiagnostic
  noHilbertDomainTransfer :
    ¬ G8BookIIILemniscateTauProfiniteHilbertDomainTransferTarget

/-- Diagnostic-only evidence refutes the A1.2 transfer target precisely when
    it records that the exact transfer theorem is absent. -/
theorem
    G8BookIIITauCircleDiagnosticsWithoutHilbertDomainTransfer.refutesDomainTransfer
    (gap : G8BookIIITauCircleDiagnosticsWithoutHilbertDomainTransfer) :
    ¬ G8BookIIILemniscateTauProfiniteHilbertDomainTransferTarget :=
  gap.noHilbertDomainTransfer

end Tau.BookIII.Bridge
