import TauLib.BookIII.Bridge.G8BookIIILemniscateGraphDomainCore

/-!
# TauLib.BookIII.Bridge.G8BookIIILemniscateCompactMetricGraphPackage

Pure A1.1 package for the Lane-A operator route.

This module records the exact compact metric graph data needed to turn the
theorem-backed raw two-lobe wedge into `LemniscateCarrierReady`.  It stays below
Hilbert/domain analysis, operator self-adjointness, actual-`xi` membership, and
all downstream RH-facing handoffs.

The package is proof-carrying: it does not construct the compact graph topology
or metric from the current τ-circle scaffold.  Those fields remain the live
A1.1 theorem target.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- A1.1 COMPACT METRIC GRAPH PACKAGE
-- ============================================================

/-- The exact compact metric graph data needed for the lemniscate carrier.

The selected `carrierCtx` carries the topology, metric, and compact-space
instances.  The proposition fields prove that this context is the intended
compact graph quotient/metric and not merely a scaffold carrier. -/
structure G8BookIIILemniscateCompactMetricGraphPackage where
  rawWedge : G8BookIIILemniscateTwoLobeWedgeCore :=
    g8BookIIILemniscateTwoLobeWedgeCore
  rawWedgeClosed : G8BookIIILemniscateTwoLobeWedgeCoreTarget :=
    g8BookIIILemniscateTwoLobeWedgeCore_closed
  rawWedge_isCanonical :
    rawWedge = g8BookIIILemniscateTwoLobeWedgeCore := by
      rfl
  carrierCtx : LemniscateCarrierContext
  topologyIsWedgeQuotient : carrierCtx.topologyIsWedgeQuotient
  metricIsGraphMetric : carrierCtx.metricIsGraphMetric
  compactnessFromWedge : carrierCtx.compactnessFromWedge
  topologyMetricAgreement : LemniscateTopologyMetricAgreement carrierCtx
  graphDistanceRealizesMetric : carrierCtx.graphDistanceRealizesMetric
  theoremBackedStatus : carrierCtx.status = .theoremBacked
  compactMetricGraphFromRawWedge : Prop
  compactMetricGraphFromRawWedgeEvidence :
    compactMetricGraphFromRawWedge
  status : SpineStatus := .conditional_interface

/-- Proposition target for the A1.1 compact metric graph package. -/
def G8BookIIILemniscateCompactMetricGraphPackageTarget : Prop :=
  Nonempty G8BookIIILemniscateCompactMetricGraphPackage

/-- The topology selected by a compact metric graph package. -/
def G8BookIIILemniscateCompactMetricGraphPackage.topology
    (pkg : G8BookIIILemniscateCompactMetricGraphPackage) :
    TopologicalSpace LemniscateCarrier :=
  pkg.carrierCtx.topology

/-- The metric selected by a compact metric graph package. -/
def G8BookIIILemniscateCompactMetricGraphPackage.metric
    (pkg : G8BookIIILemniscateCompactMetricGraphPackage) :
    MetricSpace LemniscateCarrier :=
  pkg.carrierCtx.metric

/-- The compact-space witness selected by a compact metric graph package. -/
def G8BookIIILemniscateCompactMetricGraphPackage.compact
    (pkg : G8BookIIILemniscateCompactMetricGraphPackage) :
    @CompactSpace LemniscateCarrier pkg.carrierCtx.topology :=
  pkg.carrierCtx.compact

/-- A compact metric graph package supplies the low-level metric graph
    readiness data. -/
def G8BookIIILemniscateCompactMetricGraphPackage.toReadinessData
    (pkg : G8BookIIILemniscateCompactMetricGraphPackage) :
    G8BookIIILemniscateMetricGraphReadinessData where
  carrierCtx := pkg.carrierCtx
  topologyIsWedgeQuotient := pkg.topologyIsWedgeQuotient
  metricIsGraphMetric := pkg.metricIsGraphMetric
  compactnessFromWedge := pkg.compactnessFromWedge
  topologyMetricAgreement := pkg.topologyMetricAgreement
  graphDistanceRealizesMetric := pkg.graphDistanceRealizesMetric
  theoremBackedStatus := pkg.theoremBackedStatus

/-- A compact metric graph package immediately yields carrier readiness. -/
def G8BookIIILemniscateCompactMetricGraphPackage.toCarrierReady
    (pkg : G8BookIIILemniscateCompactMetricGraphPackage) :
    LemniscateCarrierReady pkg.carrierCtx :=
  pkg.toReadinessData.toCarrierReady

/-- A compact metric graph package supplies the existing A1.1 constructor
    surface. -/
def G8BookIIILemniscateCompactMetricGraphPackage.toMetricGraphConstructor
    (pkg : G8BookIIILemniscateCompactMetricGraphPackage) :
    G8BookIIILemniscateMetricGraphConstructor where
  rawWedge := pkg.rawWedge
  readiness := pkg.toReadinessData
  compactMetricGraphFromRawWedge :=
    pkg.compactMetricGraphFromRawWedge
  compactMetricGraphFromRawWedgeEvidence :=
    pkg.compactMetricGraphFromRawWedgeEvidence
  status := pkg.status

-- ============================================================
-- A1.2 COMPATIBILITY SURFACE
-- ============================================================

/-- Optional A1.2 compatibility package: future Hilbert/domain readiness data
    keyed to a compact metric graph package.

This does not prove Hilbert or Kirchhoff readiness.  It simply makes the
dependency on the A1.1 compact graph package explicit before forwarding to the
existing `G8BookIIILemniscateKirchhoffDomainReadinessData` surface. -/
structure G8BookIIILemniscateCompactMetricGraphKirchhoffDomainPackage where
  graph : G8BookIIILemniscateCompactMetricGraphPackage
  hilbertCtx : LemniscateHilbertContext
  hilbertUsesGraph :
    hilbertCtx.measure.carrierContext = graph.carrierCtx
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
  status : SpineStatus := .conditional_interface

/-- Forward a compact-graph-keyed A1.2 package to the existing
    Hilbert/Kirchhoff readiness surface. -/
def G8BookIIILemniscateCompactMetricGraphKirchhoffDomainPackage.toKirchhoffDomainReadinessData
    (pkg : G8BookIIILemniscateCompactMetricGraphKirchhoffDomainPackage) :
    G8BookIIILemniscateKirchhoffDomainReadinessData where
  hilbert :=
    { metricGraph := pkg.graph.toMetricGraphConstructor
      hilbertCtx := pkg.hilbertCtx
      hilbertUsesGraph := pkg.hilbertUsesGraph
      measureTotalFinite := pkg.measureTotalFinite
      lobeMeasureAgreement := pkg.lobeMeasureAgreement
      innerProductSymmetric := pkg.innerProductSymmetric
      innerProductPositive := pkg.innerProductPositive
      innerProductComplete := pkg.innerProductComplete
      innerProductCompatibleWithMeasure :=
        pkg.innerProductCompatibleWithMeasure
      traceMapDefined := pkg.traceMapDefined
      traceMapContinuous := pkg.traceMapContinuous
      quotientCompletionConstructed :=
        pkg.quotientCompletionConstructed }
  domainCtx := pkg.domainCtx
  domainUsesHilbert := pkg.domainUsesHilbert
  valueTraceDefined := pkg.valueTraceDefined
  valueTraceContinuous := pkg.valueTraceContinuous
  derivativeTraceDefined := pkg.derivativeTraceDefined
  derivativeTraceContinuous := pkg.derivativeTraceContinuous
  crossingAgreementClosed := pkg.crossingAgreementClosed
  kirchhoffConditionClosed := pkg.kirchhoffConditionClosed
  traceContinuityEvidence := pkg.traceContinuityEvidence
  traceContinuityWitness := pkg.traceContinuityWitness
  derivativeTraceEvidence := pkg.derivativeTraceEvidence
  derivativeTraceWitness := pkg.derivativeTraceWitness
  crossingClosureEvidence := pkg.crossingClosureEvidence
  crossingClosureWitness := pkg.crossingClosureWitness
  kirchhoffClosureEvidence := pkg.kirchhoffClosureEvidence
  kirchhoffClosureWitness := pkg.kirchhoffClosureWitness
  status := pkg.status

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Raw wedge facts alone may coexist with absence of a compact metric graph
    package; this records the non-constructor gap explicitly. -/
structure G8BookIIIRawWedgeWithoutCompactMetricGraphPackage where
  rawWedge : G8BookIIILemniscateTwoLobeWedgeCore :=
    g8BookIIILemniscateTwoLobeWedgeCore
  rawWedgeClosed : G8BookIIILemniscateTwoLobeWedgeCoreTarget :=
    g8BookIIILemniscateTwoLobeWedgeCore_closed
  noCompactMetricGraphPackage :
    ¬ G8BookIIILemniscateCompactMetricGraphPackageTarget

/-- A raw wedge gap refutes the compact metric graph package target. -/
theorem G8BookIIIRawWedgeWithoutCompactMetricGraphPackage.refutesTarget
    (gap : G8BookIIIRawWedgeWithoutCompactMetricGraphPackage) :
    ¬ G8BookIIILemniscateCompactMetricGraphPackageTarget :=
  gap.noCompactMetricGraphPackage

/-- A scaffold or zero-distance lane without a graph-metric proof refutes a
    compact metric graph package over the same carrier context. -/
structure G8BookIIIZeroDistanceScaffoldMetricGap
    (ctx : LemniscateCarrierContext) where
  scaffoldDistanceUsed : Prop
  scaffoldDistanceEvidence : scaffoldDistanceUsed
  noGraphMetricProof : ¬ ctx.metricIsGraphMetric

/-- Metric graph packages require the exact `metricIsGraphMetric` proof. -/
theorem G8BookIIIZeroDistanceScaffoldMetricGap.refutesPackage
    {pkg : G8BookIIILemniscateCompactMetricGraphPackage}
    (gap : G8BookIIIZeroDistanceScaffoldMetricGap pkg.carrierCtx) :
    False :=
  gap.noGraphMetricProof pkg.metricIsGraphMetric

/-- Missing any exact carrier-readiness proof refutes the compact metric graph
    package for that carrier context. -/
structure G8BookIIICompactMetricGraphExactProofGap
    (ctx : LemniscateCarrierContext) where
  missingExactReadiness :
    ¬ (ctx.topologyIsWedgeQuotient ∧
       ctx.metricIsGraphMetric ∧
       ctx.compactnessFromWedge ∧
       LemniscateTopologyMetricAgreement ctx ∧
       ctx.graphDistanceRealizesMetric ∧
       ctx.status = .theoremBacked)

/-- Compact metric graph packages require every exact readiness field, not a
    diagnostic substitute. -/
theorem G8BookIIICompactMetricGraphExactProofGap.refutesPackage
    {pkg : G8BookIIILemniscateCompactMetricGraphPackage}
    (gap : G8BookIIICompactMetricGraphExactProofGap pkg.carrierCtx) :
    False :=
  gap.missingExactReadiness
    ⟨pkg.topologyIsWedgeQuotient,
      pkg.metricIsGraphMetric,
      pkg.compactnessFromWedge,
      pkg.topologyMetricAgreement,
      pkg.graphDistanceRealizesMetric,
      pkg.theoremBackedStatus⟩

end Tau.BookIII.Bridge
