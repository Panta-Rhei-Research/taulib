import TauLib.BookIII.Bridge.G8BookIIILemniscateTauProfiniteA1A2TargetCompression

/-!
# TauLib.BookIII.Bridge.G8BookIIILemniscateCh23CompactMetricGraphSource

Ch.23-native A1.1 compact metric graph source.

The TauProfinite corridor remains useful compatibility infrastructure, but the
Book III proof map starts from the compact metric graph

```text
L = S1_B wedge S1_C
```

with a distinguished crossing point and the graph shortest-path metric.  This
module names that Ch.23 source directly and proves the no-sorry adapters into
the existing A1.1 package surface.

It does not construct the compact metric graph from the current tau-circle
trigonometric scaffold, nor from finite diagnostics, nor from the TauProfinite
ultrametric substrate alone.  The live theorem is the Ch.23 metric graph
realization for the current `LemniscateCarrier`.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CH.23 LOBE AND WEDGE SOURCE
-- ============================================================

/-- A Ch.23 circle-lobe model used to build the lemniscate graph.

This keeps the source theorem close to the manuscript: each lobe is a compact
metric circle with a distinguished basepoint.  The fields are proof-carrying
data, not inferred from the current `TauCirclePoint` scaffold. -/
structure G8BookIIICh23CircleLobeModel where
  lobeCarrier : Type 1
  topology : TopologicalSpace lobeCarrier
  metric : MetricSpace lobeCarrier
  compact : @CompactSpace lobeCarrier topology
  basepoint : lobeCarrier
  isCircleLobe : Prop
  isCircleLobeEvidence : isCircleLobe
  compactMetricCircle : Prop
  compactMetricCircleEvidence : compactMetricCircle
  basepointIsCrossingEndpoint : Prop
  basepointIsCrossingEndpointEvidence : basepointIsCrossingEndpoint
  status : SpineStatus := .conditional_interface

/-- The exact Ch.23 compact metric graph source for
    `S1_B wedge S1_C`.

The selected `carrierCtx` is the same context consumed by the downstream
operator-readiness spine.  The exact readiness fields are carried explicitly so
that this source can adapt directly into the existing A1.1 compact graph
package. -/
structure G8BookIIILemniscateCh23CompactMetricGraphSource where
  plusLobe : G8BookIIICh23CircleLobeModel
  minusLobe : G8BookIIICh23CircleLobeModel
  rawWedge : G8BookIIILemniscateTwoLobeWedgeCore :=
    g8BookIIILemniscateTwoLobeWedgeCore
  rawWedgeClosed : G8BookIIILemniscateTwoLobeWedgeCoreTarget :=
    g8BookIIILemniscateTwoLobeWedgeCore_closed
  rawWedge_isCanonical :
    rawWedge = g8BookIIILemniscateTwoLobeWedgeCore := by
      rfl
  crossingIdentifiesBasepoints : Prop
  crossingIdentifiesBasepointsEvidence : crossingIdentifiesBasepoints
  twoCircleWedgeQuotientConstructed : Prop
  twoCircleWedgeQuotientConstructedEvidence :
    twoCircleWedgeQuotientConstructed
  quotientMatchesLemniscateCarrier : Prop
  quotientMatchesLemniscateCarrierEvidence :
    quotientMatchesLemniscateCarrier
  carrierCtx : LemniscateCarrierContext
  topologyIsWedgeQuotient : carrierCtx.topologyIsWedgeQuotient
  metricIsGraphMetric : carrierCtx.metricIsGraphMetric
  compactnessFromWedge : carrierCtx.compactnessFromWedge
  topologyMetricAgreement : LemniscateTopologyMetricAgreement carrierCtx
  graphDistanceRealizesMetric : carrierCtx.graphDistanceRealizesMetric
  theoremBackedStatus : carrierCtx.status = .theoremBacked
  compactMetricGraphFromCh23 : Prop
  compactMetricGraphFromCh23Evidence : compactMetricGraphFromCh23
  shortestPathMetricFromCircleLobes : Prop
  shortestPathMetricFromCircleLobesEvidence :
    shortestPathMetricFromCircleLobes
  tauProfiniteCompatibilityDeferred : Prop
  tauProfiniteCompatibilityDeferredEvidence :
    tauProfiniteCompatibilityDeferred
  status : SpineStatus := .conditional_interface

/-- Target for the Ch.23-native compact metric graph theorem. -/
def G8BookIIILemniscateCh23CompactMetricGraphTarget : Prop :=
  Nonempty G8BookIIILemniscateCh23CompactMetricGraphSource

-- ============================================================
-- ADAPTERS INTO EXISTING A1.1 SURFACES
-- ============================================================

/-- A Ch.23 compact metric graph source supplies the existing A1.1 compact
    metric graph package. -/
def G8BookIIILemniscateCh23CompactMetricGraphSource.toCompactMetricGraphPackage
    (source : G8BookIIILemniscateCh23CompactMetricGraphSource) :
    G8BookIIILemniscateCompactMetricGraphPackage where
  rawWedge := source.rawWedge
  rawWedgeClosed := source.rawWedgeClosed
  rawWedge_isCanonical := source.rawWedge_isCanonical
  carrierCtx := source.carrierCtx
  topologyIsWedgeQuotient := source.topologyIsWedgeQuotient
  metricIsGraphMetric := source.metricIsGraphMetric
  compactnessFromWedge := source.compactnessFromWedge
  topologyMetricAgreement := source.topologyMetricAgreement
  graphDistanceRealizesMetric := source.graphDistanceRealizesMetric
  theoremBackedStatus := source.theoremBackedStatus
  compactMetricGraphFromRawWedge :=
    source.compactMetricGraphFromCh23
  compactMetricGraphFromRawWedgeEvidence :=
    source.compactMetricGraphFromCh23Evidence
  status := source.status

/-- A Ch.23 compact metric graph source supplies the existing metric-graph
    source consumed by the A1/A2 proof map. -/
def G8BookIIILemniscateCh23CompactMetricGraphSource.toMetricGraphSource
    (source : G8BookIIILemniscateCh23CompactMetricGraphSource) :
    G8BookIIILemniscateMetricGraphSource :=
  source.toCompactMetricGraphPackage.toMetricGraphSource

/-- A Ch.23 compact metric graph source supplies the low-level A1.1 constructor
    target. -/
theorem
    G8BookIIILemniscateCh23CompactMetricGraphSource.toMetricGraphConstructorTarget
    (source : G8BookIIILemniscateCh23CompactMetricGraphSource) :
    G8BookIIILemniscateMetricGraphConstructorTarget :=
  ⟨source.toCompactMetricGraphPackage.toMetricGraphConstructor⟩

/-- A Ch.23 compact metric graph source discharges the compact metric graph
    package target. -/
theorem
    G8BookIIILemniscateCh23CompactMetricGraphSource.toCompactMetricGraphPackageTarget
    (source : G8BookIIILemniscateCh23CompactMetricGraphSource) :
    G8BookIIILemniscateCompactMetricGraphPackageTarget :=
  ⟨source.toCompactMetricGraphPackage⟩

/-- A Ch.23 compact metric graph source discharges the metric-graph source
    target from the proof-step wrapper. -/
theorem
    G8BookIIILemniscateCh23CompactMetricGraphSource.toMetricGraphReadinessTarget
    (source : G8BookIIILemniscateCh23CompactMetricGraphSource) :
    Nonempty G8BookIIILemniscateMetricGraphSource :=
  ⟨source.toMetricGraphSource⟩

/-- Target-level adapter from the Ch.23 source theorem into the existing A1.1
    package target. -/
theorem
    g8BookIIILemniscateCh23CompactMetricGraphTarget_toPackageTarget
    (target : G8BookIIILemniscateCh23CompactMetricGraphTarget) :
    G8BookIIILemniscateCompactMetricGraphPackageTarget := by
  rcases target with ⟨source⟩
  exact source.toCompactMetricGraphPackageTarget

/-- Target-level adapter from the Ch.23 source theorem into the metric graph
    source target. -/
theorem
    g8BookIIILemniscateCh23CompactMetricGraphTarget_toMetricGraphSourceTarget
    (target : G8BookIIILemniscateCh23CompactMetricGraphTarget) :
    Nonempty G8BookIIILemniscateMetricGraphSource := by
  rcases target with ⟨source⟩
  exact source.toMetricGraphReadinessTarget

-- ============================================================
-- RELATION TO TAUPROFINITE COMPATIBILITY
-- ============================================================

/-- Compatibility object: a Ch.23 compact metric graph source may later be
    paired with the TauProfinite corridor, but the Ch.23 source does not depend
    on that corridor. -/
structure G8BookIIILemniscateCh23TauProfiniteCompatibilitySource where
  ch23Graph : G8BookIIILemniscateCh23CompactMetricGraphSource
  tauProfiniteWedge :
    G8BookIIILemniscateTauProfiniteWedgeTransferSource
  sameCarrierContext :
    tauProfiniteWedge.carrierCtx = ch23Graph.carrierCtx
  sameTopologyMetricAgreement : Prop
  sameTopologyMetricAgreementEvidence :
    sameTopologyMetricAgreement
  sameShortestPathMetric : Prop
  sameShortestPathMetricEvidence : sameShortestPathMetric
  status : SpineStatus := .conditional_interface

/-- A compatibility source supplies both the Ch.23 and TauProfinite A1.1
    package targets, without making TauProfinite the source truth for Ch.23. -/
theorem
    G8BookIIILemniscateCh23TauProfiniteCompatibilitySource.toBothA1Targets
    (source : G8BookIIILemniscateCh23TauProfiniteCompatibilitySource) :
    G8BookIIILemniscateCompactMetricGraphPackageTarget ∧
      G8BookIIILemniscateTauProfiniteWedgeTransferTarget :=
  ⟨source.ch23Graph.toCompactMetricGraphPackageTarget,
    ⟨source.tauProfiniteWedge⟩⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Two compact circle lobes without the wedge quotient and shortest-path
    graph metric still do not construct the Ch.23 metric graph. -/
structure G8BookIIICh23CircleLobesWithoutWedgeMetric where
  plusLobe : G8BookIIICh23CircleLobeModel
  minusLobe : G8BookIIICh23CircleLobeModel
  noCh23CompactMetricGraph :
    ¬ G8BookIIILemniscateCh23CompactMetricGraphTarget

/-- Circle-lobe data alone refutes the Ch.23 target precisely when it records
    absence of the wedge metric theorem. -/
theorem G8BookIIICh23CircleLobesWithoutWedgeMetric.refutesTarget
    (gap : G8BookIIICh23CircleLobesWithoutWedgeMetric) :
    ¬ G8BookIIILemniscateCh23CompactMetricGraphTarget :=
  gap.noCh23CompactMetricGraph

/-- TauProfinite compactness alone is not the Ch.23 connected metric graph
    theorem. -/
structure G8BookIIITauProfiniteSubstrateWithoutCh23MetricGraph where
  substrateClosed : G8TauProfiniteCompactMetricSubstrateTarget :=
    g8TauProfiniteCompactMetricSubstrate_closed
  noCh23CompactMetricGraph :
    ¬ G8BookIIILemniscateCh23CompactMetricGraphTarget

/-- The TauProfinite substrate-only gap refutes the Ch.23 target. -/
theorem
    G8BookIIITauProfiniteSubstrateWithoutCh23MetricGraph.refutesTarget
    (gap : G8BookIIITauProfiniteSubstrateWithoutCh23MetricGraph) :
    ¬ G8BookIIILemniscateCh23CompactMetricGraphTarget :=
  gap.noCh23CompactMetricGraph

/-- Missing shortest-path graph metric realization refutes any Ch.23 source
    over the same carrier context. -/
structure G8BookIIICh23MissingShortestPathMetric
    (source : G8BookIIILemniscateCh23CompactMetricGraphSource) where
  noShortestPathMetric :
    ¬ source.carrierCtx.graphDistanceRealizesMetric

/-- The Ch.23 source requires the exact shortest-path realization field. -/
theorem G8BookIIICh23MissingShortestPathMetric.refutesSource
    {source : G8BookIIILemniscateCh23CompactMetricGraphSource}
    (gap : G8BookIIICh23MissingShortestPathMetric source) :
    False :=
  gap.noShortestPathMetric source.graphDistanceRealizesMetric

/-- A Ch.23 source with a non-theorem-backed carrier context is impossible. -/
structure G8BookIIICh23NonTheoremBackedCarrier
    (source : G8BookIIILemniscateCh23CompactMetricGraphSource) where
  notTheoremBacked :
    source.carrierCtx.status ≠ .theoremBacked

/-- The Ch.23 source requires theorem-backed carrier status. -/
theorem G8BookIIICh23NonTheoremBackedCarrier.refutesSource
    {source : G8BookIIILemniscateCh23CompactMetricGraphSource}
    (gap : G8BookIIICh23NonTheoremBackedCarrier source) :
    False :=
  gap.notTheoremBacked source.theoremBackedStatus

end Tau.BookIII.Bridge
