import TauLib.BookIII.Bridge.G8BookIIILemniscateCompactMetricGraphPackage

/-!
# TauLib.BookIII.Bridge.G8BookIIILemniscateCompactMetricGraphRealization

Pure A1.1 realization surface for the Lane-A operator route.

The previous package names the exact compact metric graph data needed by the
downstream operator spine.  This module isolates the corresponding τ-native
realization theorem as a source object and proves the no-sorry constructors and
equivalences around it.

It deliberately does not inhabit the source from the current zero-distance
scaffold in `LemniscateGraph`.  The live mathematical payload is still the
actual compact graph topology, graph metric, compactness theorem,
topology/metric agreement, and shortest-path realization for the two-lobe
τ-native wedge carrier.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- A1.1 TAU-NATIVE COMPACT METRIC GRAPH REALIZATION SOURCE
-- ============================================================

/-- Exact τ-native source theorem for the compact metric graph realization of
    the two-lobe lemniscate carrier.

This is the proof object we ultimately need to construct from compact metric
graph topology.  It is intentionally isomorphic to
`G8BookIIILemniscateCompactMetricGraphPackage`, but named from the
mathematical side: topology, metric, compactness, agreement, and graph-distance
realization for the τ-native wedge. -/
structure G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource where
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
  compactTopologyConstructed : Prop
  compactTopologyWitness : compactTopologyConstructed
  graphMetricConstructed : Prop
  graphMetricWitness : graphMetricConstructed
  shortestPathRealizationConstructed : Prop
  shortestPathRealizationWitness :
    shortestPathRealizationConstructed

/-- Proposition target for the τ-native compact metric graph realization
    theorem. -/
def G8BookIIILemniscateTauNativeCompactMetricGraphRealizationTarget : Prop :=
  Nonempty G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource

/-- A τ-native compact metric graph realization source gives the A1.1 package. -/
def
    G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource.toCompactMetricGraphPackage
    (source :
      G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource) :
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
    source.compactMetricGraphFromRawWedge
  compactMetricGraphFromRawWedgeEvidence :=
    source.compactMetricGraphFromRawWedgeEvidence
  status := .conditional_interface

/-- The A1.1 package can be viewed as the exact τ-native realization source,
    with the already-carried package evidence reused as the construction
    provenance.

This is a bookkeeping equivalence, not a new compactness theorem. -/
def
    G8BookIIILemniscateCompactMetricGraphPackage.toTauNativeRealizationSource
    (pkg : G8BookIIILemniscateCompactMetricGraphPackage) :
    G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource where
  rawWedge := pkg.rawWedge
  rawWedgeClosed := pkg.rawWedgeClosed
  rawWedge_isCanonical := pkg.rawWedge_isCanonical
  carrierCtx := pkg.carrierCtx
  topologyIsWedgeQuotient := pkg.topologyIsWedgeQuotient
  metricIsGraphMetric := pkg.metricIsGraphMetric
  compactnessFromWedge := pkg.compactnessFromWedge
  topologyMetricAgreement := pkg.topologyMetricAgreement
  graphDistanceRealizesMetric := pkg.graphDistanceRealizesMetric
  theoremBackedStatus := pkg.theoremBackedStatus
  compactMetricGraphFromRawWedge :=
    pkg.compactMetricGraphFromRawWedge
  compactMetricGraphFromRawWedgeEvidence :=
    pkg.compactMetricGraphFromRawWedgeEvidence
  compactTopologyConstructed :=
    pkg.carrierCtx.topologyIsWedgeQuotient ∧
      pkg.carrierCtx.compactnessFromWedge
  compactTopologyWitness :=
    ⟨pkg.topologyIsWedgeQuotient, pkg.compactnessFromWedge⟩
  graphMetricConstructed :=
    pkg.carrierCtx.metricIsGraphMetric ∧
      LemniscateTopologyMetricAgreement pkg.carrierCtx
  graphMetricWitness :=
    ⟨pkg.metricIsGraphMetric, pkg.topologyMetricAgreement⟩
  shortestPathRealizationConstructed :=
    pkg.carrierCtx.graphDistanceRealizesMetric
  shortestPathRealizationWitness :=
    pkg.graphDistanceRealizesMetric

/-- The τ-native realization target is exactly the A1.1 package target. -/
theorem
    g8BookIIILemniscateTauNativeCompactMetricGraphRealizationTarget_iff_packageTarget :
    G8BookIIILemniscateTauNativeCompactMetricGraphRealizationTarget ↔
      G8BookIIILemniscateCompactMetricGraphPackageTarget := by
  constructor
  · rintro ⟨source⟩
    exact ⟨source.toCompactMetricGraphPackage⟩
  · rintro ⟨pkg⟩
    exact ⟨pkg.toTauNativeRealizationSource⟩

/-- A τ-native realization source discharges the existing A1.1 constructor
    target. -/
theorem
    G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource.toMetricGraphConstructorTarget
    (source :
      G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource) :
    G8BookIIILemniscateMetricGraphConstructorTarget :=
  ⟨source.toCompactMetricGraphPackage.toMetricGraphConstructor⟩

/-- A τ-native realization source gives carrier readiness for its selected
    carrier context. -/
def
    G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource.toCarrierReady
    (source :
      G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource) :
    LemniscateCarrierReady source.carrierCtx :=
  source.toCompactMetricGraphPackage.toCarrierReady

-- ============================================================
-- A1.2 COMPATIBILITY
-- ============================================================

/-- A1.2 package keyed to the τ-native compact metric graph realization source.

The Hilbert/domain fields remain proof-carrying inputs.  This wrapper simply
keeps the dependency on the A1.1 realization theorem explicit before entering
the existing Kirchhoff-domain readiness surface. -/
structure G8BookIIILemniscateTauNativeCompactMetricGraphDomainRealizationSource where
  graph :
    G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource
  hilbertDomain :
    G8BookIIILemniscateCompactMetricGraphKirchhoffDomainPackage
  hilbertDomainUsesGraph :
    hilbertDomain.graph =
      graph.toCompactMetricGraphPackage

/-- Forget the τ-native realization wrapper and recover the existing A1.2
    Kirchhoff-domain readiness data. -/
def
    G8BookIIILemniscateTauNativeCompactMetricGraphDomainRealizationSource.toKirchhoffDomainReadinessData
    (source :
      G8BookIIILemniscateTauNativeCompactMetricGraphDomainRealizationSource) :
    G8BookIIILemniscateKirchhoffDomainReadinessData :=
  source.hilbertDomain.toKirchhoffDomainReadinessData

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- The current zero-distance carrier scaffold is not, by itself, a compact
    metric graph realization source. -/
structure G8BookIIILemniscateZeroDistanceScaffoldOnly where
  zeroDistanceSelf :
    ∀ x : LemniscateCarrier, lemniscateGraphDist x x = 0
  noTauNativeCompactMetricGraphRealization :
    ¬ G8BookIIILemniscateTauNativeCompactMetricGraphRealizationTarget

/-- Zero-distance self-sanity alone refutes the realization target whenever the
    actual compact graph source is absent. -/
theorem G8BookIIILemniscateZeroDistanceScaffoldOnly.refutesRealizationTarget
    (gap : G8BookIIILemniscateZeroDistanceScaffoldOnly) :
    ¬ G8BookIIILemniscateTauNativeCompactMetricGraphRealizationTarget :=
  gap.noTauNativeCompactMetricGraphRealization

/-- Missing shortest-path realization refutes any τ-native compact metric graph
    realization source over the same carrier context. -/
structure G8BookIIILemniscateMissingShortestPathRealization
    (ctx : LemniscateCarrierContext) where
  noShortestPathRealization : ¬ ctx.graphDistanceRealizesMetric

/-- The τ-native realization source requires the exact graph-distance
    realization field. -/
theorem G8BookIIILemniscateMissingShortestPathRealization.refutesSource
    {source :
      G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource}
    (gap :
      G8BookIIILemniscateMissingShortestPathRealization source.carrierCtx) :
    False :=
  gap.noShortestPathRealization source.graphDistanceRealizesMetric

/-- Missing topology/metric agreement refutes any τ-native compact metric graph
    realization source over the same carrier context. -/
structure G8BookIIILemniscateMissingTopologyMetricAgreement
    (ctx : LemniscateCarrierContext) where
  noTopologyMetricAgreement :
    ¬ LemniscateTopologyMetricAgreement ctx

/-- The τ-native realization source requires exact topology/metric agreement. -/
theorem G8BookIIILemniscateMissingTopologyMetricAgreement.refutesSource
    {source :
      G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource}
    (gap :
      G8BookIIILemniscateMissingTopologyMetricAgreement source.carrierCtx) :
    False :=
  gap.noTopologyMetricAgreement source.topologyMetricAgreement

end Tau.BookIII.Bridge
