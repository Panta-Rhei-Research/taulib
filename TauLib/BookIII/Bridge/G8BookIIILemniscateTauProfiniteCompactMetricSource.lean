import TauLib.BookIII.Bridge.G8BookIIILemniscateCompactMetricGraphRealization
import TauLib.BookI.Boundary.Bridge.TauProfiniteMetricSpaceCanonical
import TauLib.BookI.Boundary.Bridge.TauProfiniteCompactSpace

/-!
# TauLib.BookIII.Bridge.G8BookIIILemniscateTauProfiniteCompactMetricSource

Pure A1.1 source scan for the Lane-A operator route.

TauLib already contains a theorem-backed compact metric substrate for
`TauProfinite`: the canonical ultrametric, topology agreement, and compactness
instance.  The current lemniscate carrier, however, is built from
`TauCirclePoint` lobes glued by a wedge quotient, and does not yet expose a
theorem-backed identification with two profinite circles carrying the graph
shortest-path metric.

This module records exactly what can be reused from the existing infrastructure
and names the remaining transfer theorem:

```text
TauProfinite compact metric circle substrate
  + tau-circle/profinite lobe identification
  + two-lobe wedge quotient transfer
  + graph shortest-path metric transfer
  -> tau-native compact metric graph realization
```

No downstream RH-facing machinery, actual-`xi` membership, accepted coverage,
operator spectrum, or finite spectral diagnostics enter this source layer.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.Boundary

-- ============================================================
-- THEOREM-BACKED TAUPROFINITE COMPACT METRIC SUBSTRATE
-- ============================================================

/-- Reusable theorem-backed compact metric substrate already present in
    TauLib for `TauProfinite`.

This is not yet the lemniscate compact metric graph.  It is the strongest
available τ-native circle-like topology/metric/compactness source we can reuse:
canonical ultrametric distance, cylinder/metric topology agreement, and
compactness. -/
structure G8TauProfiniteCompactMetricSubstrate where
  topology : TopologicalSpace TauProfinite :=
    TauProfinite.instTopologicalSpace
  metric : MetricSpace TauProfinite :=
    TauProfinite.instMetricSpaceCanonical
  compact : @CompactSpace TauProfinite topology := by
    infer_instance
  topology_eq_metric :
    (TauProfinite.instTopologicalSpace : TopologicalSpace TauProfinite) =
      TauProfinite.instMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  canonical_dist_eq_ultrametric :
    ∀ x y : TauProfinite,
      TauProfinite.instMetricSpaceCanonical.dist x y =
        TauProfinite.ultrametricDistanceReal x y
  status : SpineStatus := .conditional_interface

/-- The existing `TauProfinite` topology/metric/compactness substrate is
    theorem-backed. -/
noncomputable def g8TauProfiniteCompactMetricSubstrate :
    G8TauProfiniteCompactMetricSubstrate where
  topology_eq_metric := TauProfinite.cylinder_topology_eq_metric_topology
  canonical_dist_eq_ultrametric :=
    TauProfinite.instMetricSpaceCanonical_dist

/-- Proposition target for the reusable `TauProfinite` compact metric
    substrate. -/
def G8TauProfiniteCompactMetricSubstrateTarget : Prop :=
  Nonempty G8TauProfiniteCompactMetricSubstrate

/-- The reusable `TauProfinite` compact metric substrate is closed by existing
    TauLib infrastructure. -/
theorem g8TauProfiniteCompactMetricSubstrate_closed :
    G8TauProfiniteCompactMetricSubstrateTarget :=
  ⟨g8TauProfiniteCompactMetricSubstrate⟩

-- ============================================================
-- TAU-CIRCLE / PROFINITE WEDGE TRANSFER CORRIDOR
-- ============================================================

/-- Proof-carrying corridor from the theorem-backed `TauProfinite` compact
    metric substrate to the τ-native two-lobe lemniscate carrier.

The first field is already theorem-backed.  The lobe-identification,
wedge-transfer, compactness-transfer, topology/metric agreement, and
shortest-path metric fields are exactly the remaining A1.1 transfer theorem.
-/
structure G8BookIIILemniscateTauProfiniteCompactMetricCorridor where
  substrate : G8TauProfiniteCompactMetricSubstrate :=
    g8TauProfiniteCompactMetricSubstrate
  rawWedge : G8BookIIILemniscateTwoLobeWedgeCore :=
    g8BookIIILemniscateTwoLobeWedgeCore
  rawWedgeClosed : G8BookIIILemniscateTwoLobeWedgeCoreTarget :=
    g8BookIIILemniscateTwoLobeWedgeCore_closed
  rawWedge_isCanonical :
    rawWedge = g8BookIIILemniscateTwoLobeWedgeCore := by
      rfl
  carrierCtx : LemniscateCarrierContext
  tauCircleLobesModeledByTauProfinite : Prop
  tauCircleLobesModeledByTauProfiniteEvidence :
    tauCircleLobesModeledByTauProfinite
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

/-- Proposition target for the profinite-to-lemniscate compact metric graph
    transfer corridor. -/
def G8BookIIILemniscateTauProfiniteCompactMetricCorridorTarget : Prop :=
  Nonempty G8BookIIILemniscateTauProfiniteCompactMetricCorridor

/-- The profinite compact metric corridor supplies the current τ-native
    compact metric graph realization source. -/
def G8BookIIILemniscateTauProfiniteCompactMetricCorridor.toTauNativeRealizationSource
    (source : G8BookIIILemniscateTauProfiniteCompactMetricCorridor) :
    G8BookIIILemniscateTauNativeCompactMetricGraphRealizationSource where
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
    source.compactMetricGraphFromTauProfiniteWedge
  compactMetricGraphFromRawWedgeEvidence :=
    source.compactMetricGraphFromTauProfiniteWedgeEvidence
  compactTopologyConstructed :=
    source.tauCircleLobesModeledByTauProfinite ∧
      source.twoLobeWedgeQuotientMatchesCarrier ∧
      source.compactnessTransfersFromProfiniteWedge
  compactTopologyWitness :=
    ⟨source.tauCircleLobesModeledByTauProfiniteEvidence,
      source.twoLobeWedgeQuotientMatchesCarrierEvidence,
      source.compactnessTransfersFromProfiniteWedgeEvidence⟩
  graphMetricConstructed :=
    source.graphMetricTransfersFromProfiniteLobes ∧
      LemniscateTopologyMetricAgreement source.carrierCtx
  graphMetricWitness :=
    ⟨source.graphMetricTransfersFromProfiniteLobesEvidence,
      source.topologyMetricAgreement⟩
  shortestPathRealizationConstructed :=
    source.carrierCtx.graphDistanceRealizesMetric
  shortestPathRealizationWitness :=
    source.graphDistanceRealizesMetric

/-- A profinite compact metric corridor discharges the τ-native compact metric
    graph realization target. -/
theorem
    G8BookIIILemniscateTauProfiniteCompactMetricCorridor.toTauNativeRealizationTarget
    (source : G8BookIIILemniscateTauProfiniteCompactMetricCorridor) :
    G8BookIIILemniscateTauNativeCompactMetricGraphRealizationTarget :=
  ⟨source.toTauNativeRealizationSource⟩

/-- A profinite compact metric corridor discharges the A1.1 compact metric graph
    package target. -/
theorem
    G8BookIIILemniscateTauProfiniteCompactMetricCorridor.toCompactMetricGraphPackageTarget
    (source : G8BookIIILemniscateTauProfiniteCompactMetricCorridor) :
    G8BookIIILemniscateCompactMetricGraphPackageTarget :=
  (g8BookIIILemniscateTauNativeCompactMetricGraphRealizationTarget_iff_packageTarget).mp
    source.toTauNativeRealizationTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- The theorem-backed `TauProfinite` substrate alone does not construct the
    lemniscate compact metric graph unless the tau-circle/wedge transfer
    corridor is supplied. -/
structure G8TauProfiniteSubstrateWithoutLemniscateCorridor where
  substrateClosed : G8TauProfiniteCompactMetricSubstrateTarget :=
    g8TauProfiniteCompactMetricSubstrate_closed
  noLemniscateCorridor :
    ¬ G8BookIIILemniscateTauProfiniteCompactMetricCorridorTarget

/-- The profinite substrate-only gap refutes the corridor target. -/
theorem G8TauProfiniteSubstrateWithoutLemniscateCorridor.refutesCorridorTarget
    (gap : G8TauProfiniteSubstrateWithoutLemniscateCorridor) :
    ¬ G8BookIIILemniscateTauProfiniteCompactMetricCorridorTarget :=
  gap.noLemniscateCorridor

/-- Tau-circle trigonometric/unit-magnitude facts alone do not supply the
    compact graph topology, graph metric, compactness, topology/metric
    agreement, or shortest-path realization fields. -/
structure G8TauCircleTrigWithoutCompactMetricGraphTransfer where
  tauCircleTrigEvidence : Prop
  tauCircleTrigWitness : tauCircleTrigEvidence
  noTauNativeCompactMetricGraphRealization :
    ¬ G8BookIIILemniscateTauNativeCompactMetricGraphRealizationTarget

/-- Trigonometric circle evidence refutes the realization target whenever the
    compact metric graph transfer theorem is absent. -/
theorem
    G8TauCircleTrigWithoutCompactMetricGraphTransfer.refutesRealizationTarget
    (gap : G8TauCircleTrigWithoutCompactMetricGraphTransfer) :
    ¬ G8BookIIILemniscateTauNativeCompactMetricGraphRealizationTarget :=
  gap.noTauNativeCompactMetricGraphRealization

/-- A missing lobe/profinite identification refutes any corridor that claims
    the same identification field. -/
structure G8MissingTauCircleProfiniteLobeIdentification
    (source : G8BookIIILemniscateTauProfiniteCompactMetricCorridor) where
  missingLobeIdentification :
    ¬ source.tauCircleLobesModeledByTauProfinite

/-- The corridor requires exact tau-circle/profinite lobe identification. -/
theorem G8MissingTauCircleProfiniteLobeIdentification.refutesCorridor
    {source : G8BookIIILemniscateTauProfiniteCompactMetricCorridor}
    (gap : G8MissingTauCircleProfiniteLobeIdentification source) :
    False :=
  gap.missingLobeIdentification
    source.tauCircleLobesModeledByTauProfiniteEvidence

/-- A missing graph-metric transfer refutes any corridor that claims the same
    transfer field. -/
structure G8MissingTauProfiniteGraphMetricTransfer
    (source : G8BookIIILemniscateTauProfiniteCompactMetricCorridor) where
  missingGraphMetricTransfer :
    ¬ source.graphMetricTransfersFromProfiniteLobes

/-- The corridor requires exact graph-metric transfer from the profinite lobe
    substrate. -/
theorem G8MissingTauProfiniteGraphMetricTransfer.refutesCorridor
    {source : G8BookIIILemniscateTauProfiniteCompactMetricCorridor}
    (gap : G8MissingTauProfiniteGraphMetricTransfer source) :
    False :=
  gap.missingGraphMetricTransfer
    source.graphMetricTransfersFromProfiniteLobesEvidence

end Tau.BookIII.Bridge
