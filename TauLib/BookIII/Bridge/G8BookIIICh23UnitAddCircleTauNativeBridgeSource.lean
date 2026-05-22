import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleWedgeGraphConstructor

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleTauNativeBridgeSource

Proof-step split for the Ch.23 concrete wedge to tau-native carrier bridge.

`G8BookIIICh23UnitAddCircleWedgeGraphConstructor` already isolates the full
bridge from the concrete `UnitAddCircle` wedge graph to the current
`LemniscateCarrier`.  This module opens the next load-bearing field in that
bridge: a basepoint-preserving lobe equivalence induces an exact quotient
equivalence

```text
G8Ch23UnitAddCircleWedgeCarrier ≃ LemniscateCarrier.
```

The topology, metric, compactness, and shortest-path transfer remain explicit
proof-carrying fields.  In particular, this module does not identify
`TauCirclePoint` with `UnitAddCircle` unconditionally, and it does not promote
the zero-distance scaffold to a graph metric.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- LOBE-LEVEL BASEPOINT-PRESERVING EQUIVALENCE
-- ============================================================

/-- Exact lobe-level identification needed to compare the concrete Ch.23
    `UnitAddCircle` wedge with the current tau-native lobe carrier.

The basepoint field is load-bearing: without it, the quotient crossing classes
need not match. -/
structure G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence where
  lobeEquiv : UnitAddCircle ≃ TauCirclePoint
  basepoint_preserving :
    lobeEquiv G8Ch23UnitAddCircleWedgePoint.basepoint =
      TauCirclePoint.base
  lobeTopologyAgreement : Prop
  lobeTopologyAgreementEvidence : lobeTopologyAgreement
  lobeMetricAgreement : Prop
  lobeMetricAgreementEvidence : lobeMetricAgreement
  lobeCompactnessAgreement : Prop
  lobeCompactnessAgreementEvidence : lobeCompactnessAgreement
  status : SpineStatus := .conditional_interface

namespace G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence

/-- The inverse lobe map also preserves the distinguished basepoint. -/
theorem symm_basepoint_preserving
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    source.lobeEquiv.symm TauCirclePoint.base =
      G8Ch23UnitAddCircleWedgePoint.basepoint := by
  apply source.lobeEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact source.basepoint_preserving.symm

/-- Raw concrete wedge points transported to the tau-native raw wedge. -/
def toTauNativeRaw
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    G8Ch23UnitAddCircleWedgePoint → LemniscatePoint
  | .crossing => .crossing
  | .lobe s p => .lobe s (source.lobeEquiv p)

/-- Raw tau-native wedge points transported back to the concrete wedge. -/
def fromTauNativeRaw
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    LemniscatePoint → G8Ch23UnitAddCircleWedgePoint
  | .crossing => .crossing
  | .lobe s p => .lobe s (source.lobeEquiv.symm p)

/-- Concrete crossing-class membership maps into tau-native crossing-class
    membership. -/
theorem toTauNativeRaw_inCrossingClass
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence)
    {x : G8Ch23UnitAddCircleWedgePoint}
    (h : G8Ch23UnitAddCircleWedgePoint.InCrossingClass x) :
    LemniscatePoint.InCrossingClass (source.toTauNativeRaw x) := by
  cases x with
  | crossing =>
      trivial
  | lobe s p =>
      dsimp [G8Ch23UnitAddCircleWedgePoint.InCrossingClass] at h
      dsimp [toTauNativeRaw, LemniscatePoint.InCrossingClass]
      rw [h]
      exact source.basepoint_preserving

/-- Tau-native crossing-class membership maps back into concrete
    crossing-class membership. -/
theorem fromTauNativeRaw_inCrossingClass
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence)
    {x : LemniscatePoint}
    (h : LemniscatePoint.InCrossingClass x) :
    G8Ch23UnitAddCircleWedgePoint.InCrossingClass
      (source.fromTauNativeRaw x) := by
  cases x with
  | crossing =>
      trivial
  | lobe s p =>
      dsimp [LemniscatePoint.InCrossingClass] at h
      dsimp [fromTauNativeRaw,
        G8Ch23UnitAddCircleWedgePoint.InCrossingClass]
      rw [h]
      exact source.symm_basepoint_preserving

/-- The raw forward map respects the concrete wedge equivalence relation. -/
theorem toTauNativeRaw_respects
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence)
    {x y : G8Ch23UnitAddCircleWedgePoint}
    (h : G8Ch23UnitAddCircleWedgePoint.WedgeEquivalent x y) :
    LemniscatePoint.WedgeEquivalent
      (source.toTauNativeRaw x) (source.toTauNativeRaw y) := by
  cases h with
  | inl hxy =>
      exact Or.inl (by rw [hxy])
  | inr hxy =>
      exact Or.inr
        ⟨source.toTauNativeRaw_inCrossingClass hxy.left,
          source.toTauNativeRaw_inCrossingClass hxy.right⟩

/-- The raw inverse map respects the tau-native wedge equivalence relation. -/
theorem fromTauNativeRaw_respects
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence)
    {x y : LemniscatePoint}
    (h : LemniscatePoint.WedgeEquivalent x y) :
    G8Ch23UnitAddCircleWedgePoint.WedgeEquivalent
      (source.fromTauNativeRaw x) (source.fromTauNativeRaw y) := by
  cases h with
  | inl hxy =>
      exact Or.inl (by rw [hxy])
  | inr hxy =>
      exact Or.inr
        ⟨source.fromTauNativeRaw_inCrossingClass hxy.left,
          source.fromTauNativeRaw_inCrossingClass hxy.right⟩

/-- Quotient-level map from the concrete Ch.23 wedge carrier to the
    tau-native `LemniscateCarrier`. -/
def toTauNativeCarrier
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    G8Ch23UnitAddCircleWedgeCarrier → LemniscateCarrier :=
  Quotient.map source.toTauNativeRaw (by
    intro x y h
    exact source.toTauNativeRaw_respects h)

/-- Quotient-level inverse map from `LemniscateCarrier` to the concrete Ch.23
    wedge carrier. -/
def fromTauNativeCarrier
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    LemniscateCarrier → G8Ch23UnitAddCircleWedgeCarrier :=
  Quotient.map source.fromTauNativeRaw (by
    intro x y h
    exact source.fromTauNativeRaw_respects h)

/-- The forward quotient map followed by the inverse is identity. -/
theorem from_to_carrier
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence)
    (x : G8Ch23UnitAddCircleWedgeCarrier) :
    source.fromTauNativeCarrier (source.toTauNativeCarrier x) = x := by
  refine Quotient.inductionOn x ?_
  intro raw
  apply Quotient.sound
  cases raw with
  | crossing =>
      exact Or.inl rfl
  | lobe s p =>
      exact Or.inl (by simp [toTauNativeRaw, fromTauNativeRaw])

/-- The inverse quotient map followed by the forward map is identity. -/
theorem to_from_carrier
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence)
    (x : LemniscateCarrier) :
    source.toTauNativeCarrier (source.fromTauNativeCarrier x) = x := by
  refine Quotient.inductionOn x ?_
  intro raw
  apply Quotient.sound
  cases raw with
  | crossing =>
      exact Or.inl rfl
  | lobe s p =>
      exact Or.inl (by simp [toTauNativeRaw, fromTauNativeRaw])

/-- A basepoint-preserving lobe equivalence induces the exact quotient
    equivalence between the concrete Ch.23 wedge and `LemniscateCarrier`. -/
noncomputable def toCarrierEquiv
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    G8Ch23UnitAddCircleWedgeCarrier ≃ LemniscateCarrier where
  toFun := source.toTauNativeCarrier
  invFun := source.fromTauNativeCarrier
  left_inv := source.from_to_carrier
  right_inv := source.to_from_carrier

/-- The induced quotient equivalence sends the concrete crossing to the
    tau-native crossing. -/
theorem toCarrierEquiv_crossing
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    source.toCarrierEquiv G8Ch23UnitAddCircleWedgeCarrier.crossing =
      LemniscateCarrier.crossing :=
  rfl

/-- The induced quotient equivalence sends concrete lobe points to their
    tau-native lobe image. -/
theorem toCarrierEquiv_lobe
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence)
    (s : LemniscateSector) (p : UnitAddCircle) :
    source.toCarrierEquiv (G8Ch23UnitAddCircleWedgeCarrier.lobe s p) =
      LemniscateCarrier.lobe s (source.lobeEquiv p) :=
  rfl

end G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence

-- ============================================================
-- QUOTIENT BRIDGE AND METRIC-TRANSFER SOURCE
-- ============================================================

/-- Proof-carrying quotient bridge obtained from a basepoint-preserving
    lobe equivalence. -/
structure G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeSource where
  lobeEquivalence :
    G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence
  carrierEquiv :
    G8Ch23UnitAddCircleWedgeCarrier ≃ LemniscateCarrier :=
      lobeEquivalence.toCarrierEquiv
  carrierEquiv_isInduced :
    carrierEquiv = lobeEquivalence.toCarrierEquiv := by
      rfl
  crossing_preserved :
    carrierEquiv G8Ch23UnitAddCircleWedgeCarrier.crossing =
      LemniscateCarrier.crossing
  lobe_preserved :
    ∀ (s : LemniscateSector) (p : UnitAddCircle),
      carrierEquiv (G8Ch23UnitAddCircleWedgeCarrier.lobe s p) =
        LemniscateCarrier.lobe s (lobeEquivalence.lobeEquiv p)
  quotientEquivalenceTheoremBacked : Prop
  quotientEquivalenceTheoremBackedEvidence :
    quotientEquivalenceTheoremBacked
  status : SpineStatus := .conditional_interface

namespace G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeSource

/-- Canonical quotient bridge induced by the lobe equivalence. -/
noncomputable def ofLobeEquivalence
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) :
    G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeSource where
  lobeEquivalence := source
  crossing_preserved := source.toCarrierEquiv_crossing
  lobe_preserved := source.toCarrierEquiv_lobe
  quotientEquivalenceTheoremBacked :=
    Nonempty (G8Ch23UnitAddCircleWedgeCarrier ≃ LemniscateCarrier)
  quotientEquivalenceTheoremBackedEvidence :=
    ⟨source.toCarrierEquiv⟩
  status := source.status

end G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeSource

/-- Target for the exact quotient-equivalence bridge. -/
def G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeTarget : Prop :=
  Nonempty G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeSource

/-- Full transfer source: quotient equivalence plus the topology/metric
    transfer fields needed by the existing tau-native Ch.23 bridge. -/
structure G8BookIIICh23UnitAddCircleTauNativeMetricTransferSource where
  concrete :
    G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource
  quotientBridge :
    G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeSource
  carrierCtx : LemniscateCarrierContext
  topologyTransferred : carrierCtx.topologyIsWedgeQuotient
  metricTransferred : carrierCtx.metricIsGraphMetric
  compactnessTransferred : carrierCtx.compactnessFromWedge
  topologyMetricAgreement : LemniscateTopologyMetricAgreement carrierCtx
  graphDistanceRealizesMetric : carrierCtx.graphDistanceRealizesMetric
  theoremBackedStatus : carrierCtx.status = .theoremBacked
  quotientMatchesLemniscateCarrier : Prop
  quotientMatchesLemniscateCarrierEvidence :
    quotientMatchesLemniscateCarrier
  metricTransferFromConcreteWedge : Prop
  metricTransferFromConcreteWedgeEvidence :
    metricTransferFromConcreteWedge
  status : SpineStatus := .conditional_interface

/-- The split transfer source supplies the existing monolithic tau-native
    bridge. -/
def G8BookIIICh23UnitAddCircleTauNativeMetricTransferSource.toTauNativeBridge
    (source : G8BookIIICh23UnitAddCircleTauNativeMetricTransferSource) :
    G8BookIIICh23UnitAddCircleWedgeTauNativeBridge where
  concrete := source.concrete
  carrierCtx := source.carrierCtx
  carrierEquiv := source.quotientBridge.carrierEquiv
  topologyTransferred := source.topologyTransferred
  metricTransferred := source.metricTransferred
  compactnessTransferred := source.compactnessTransferred
  topologyMetricAgreement := source.topologyMetricAgreement
  graphDistanceRealizesMetric := source.graphDistanceRealizesMetric
  theoremBackedStatus := source.theoremBackedStatus
  quotientMatchesLemniscateCarrier :=
    source.quotientMatchesLemniscateCarrier
  quotientMatchesLemniscateCarrierEvidence :=
    source.quotientMatchesLemniscateCarrierEvidence
  status := source.status

/-- Target for the split metric-transfer bridge. -/
def G8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget : Prop :=
  Nonempty G8BookIIICh23UnitAddCircleTauNativeMetricTransferSource

/-- The split transfer target implies the existing tau-native bridge target. -/
theorem
    g8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget_toBridgeTarget
    (target : G8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget) :
    G8BookIIICh23UnitAddCircleWedgeTauNativeBridgeTarget := by
  rcases target with ⟨source⟩
  exact ⟨source.toTauNativeBridge⟩

/-- The split transfer target implies the existing Ch.23 compact metric graph
    target. -/
theorem
    g8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget_toCh23Target
    (target : G8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget) :
    G8BookIIILemniscateCh23CompactMetricGraphTarget :=
  g8BookIIICh23UnitAddCircleWedgeTauNativeBridgeTarget_toCh23Target
    (g8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget_toBridgeTarget
      target)

/-- The split transfer target implies the existing compact metric graph
    package target. -/
theorem
    g8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget_toPackageTarget
    (target : G8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget) :
    G8BookIIILemniscateCompactMetricGraphPackageTarget :=
  g8BookIIILemniscateCh23CompactMetricGraphTarget_toPackageTarget
    (g8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget_toCh23Target
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A lobe equivalence that misses the basepoint cannot be used for the
    quotient bridge. -/
structure G8BookIIICh23UnitAddCircleTauCircleBasepointMismatch
    (source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence) where
  notBasepointPreserving :
    source.lobeEquiv G8Ch23UnitAddCircleWedgePoint.basepoint ≠
      TauCirclePoint.base

/-- The lobe-equivalence source requires exact basepoint preservation. -/
theorem
    G8BookIIICh23UnitAddCircleTauCircleBasepointMismatch.refutesSource
    {source : G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence}
    (gap : G8BookIIICh23UnitAddCircleTauCircleBasepointMismatch source) :
    False :=
  gap.notBasepointPreserving source.basepoint_preserving

/-- A quotient bridge alone does not transfer topology, graph metric,
    compactness, or shortest-path realization. -/
structure G8BookIIICh23QuotientBridgeWithoutMetricTransfer where
  quotientBridge :
    G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeSource
  noMetricTransfer :
    ¬ G8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget

/-- The quotient bridge without metric transfer refutes only the transfer
    target, not the quotient equivalence itself. -/
theorem
    G8BookIIICh23QuotientBridgeWithoutMetricTransfer.refutesTransferTarget
    (gap : G8BookIIICh23QuotientBridgeWithoutMetricTransfer) :
    ¬ G8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget :=
  gap.noMetricTransfer

/-- Metric transfer cannot be weakened to quotient equivalence alone. -/
structure G8BookIIICh23MetricTransferMissingGraphMetric
    (source :
      G8BookIIICh23UnitAddCircleTauNativeMetricTransferSource) where
  noGraphMetric : ¬ source.carrierCtx.metricIsGraphMetric

/-- The split transfer source requires exact graph-metric evidence. -/
theorem
    G8BookIIICh23MetricTransferMissingGraphMetric.refutesTransferSource
    {source :
      G8BookIIICh23UnitAddCircleTauNativeMetricTransferSource}
    (gap : G8BookIIICh23MetricTransferMissingGraphMetric source) :
    False :=
  gap.noGraphMetric source.metricTransferred

end Tau.BookIII.Bridge
