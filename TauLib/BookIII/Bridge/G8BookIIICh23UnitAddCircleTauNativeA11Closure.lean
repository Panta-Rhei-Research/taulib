import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleTauNativeBridgeSource

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleTauNativeA11Closure

Final A1.1 assembly surface for the Ch.23 `UnitAddCircle` wedge route.

The previous bridge module proves that a basepoint-preserving lobe equivalence
induces the exact quotient equivalence

```text
G8Ch23UnitAddCircleWedgeCarrier ≃ LemniscateCarrier.
```

This module packages the remaining A1.1 transfer theorem in one place:

```text
concrete UnitAddCircle compact graph
  + tau-circle lobe equivalence
  + exact topology/metric/compactness transfer
  -> tau-native compact metric graph package.
```

It deliberately does not manufacture the lobe equivalence, graph metric, or
compactness transfer from the current scaffold.  Those remain the load-bearing
mathematical fields.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- TAU-CIRCLE PARAMETRIZATION COMPLETENESS
-- ============================================================

/-- Exact source for identifying the current tau-native circle lobe with the
    Ch.23 `UnitAddCircle` lobe.

The inverse fields are load-bearing: without a genuine equivalence, the
quotient bridge is not available.  The topology/metric/compactness fields are
kept explicit so that this is not merely a set-level bijection. -/
structure G8BookIIICh23TauCircleParametrizationCompletenessSource where
  toTauCircle : UnitAddCircle → TauCirclePoint
  fromTauCircle : TauCirclePoint → UnitAddCircle
  left_inv :
    ∀ p : UnitAddCircle, fromTauCircle (toTauCircle p) = p
  right_inv :
    ∀ p : TauCirclePoint, toTauCircle (fromTauCircle p) = p
  basepoint_preserving :
    toTauCircle G8Ch23UnitAddCircleWedgePoint.basepoint =
      TauCirclePoint.base
  lobeTopologyAgreement : Prop
  lobeTopologyAgreementEvidence : lobeTopologyAgreement
  lobeMetricAgreement : Prop
  lobeMetricAgreementEvidence : lobeMetricAgreement
  lobeCompactnessAgreement : Prop
  lobeCompactnessAgreementEvidence : lobeCompactnessAgreement
  parametrizationComplete : Prop
  parametrizationCompleteEvidence : parametrizationComplete
  status : SpineStatus := .conditional_interface

namespace G8BookIIICh23TauCircleParametrizationCompletenessSource

/-- A complete tau-circle parametrization supplies the lobe equivalence source
    used by the quotient bridge. -/
def toLobeEquivalence
    (source : G8BookIIICh23TauCircleParametrizationCompletenessSource) :
    G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence where
  lobeEquiv :=
    { toFun := source.toTauCircle
      invFun := source.fromTauCircle
      left_inv := source.left_inv
      right_inv := source.right_inv }
  basepoint_preserving := source.basepoint_preserving
  lobeTopologyAgreement := source.lobeTopologyAgreement
  lobeTopologyAgreementEvidence := source.lobeTopologyAgreementEvidence
  lobeMetricAgreement := source.lobeMetricAgreement
  lobeMetricAgreementEvidence := source.lobeMetricAgreementEvidence
  lobeCompactnessAgreement := source.lobeCompactnessAgreement
  lobeCompactnessAgreementEvidence :=
    source.lobeCompactnessAgreementEvidence
  status := source.status

/-- A complete tau-circle parametrization induces the concrete-to-tau-native
    quotient bridge. -/
noncomputable def toQuotientBridge
    (source : G8BookIIICh23TauCircleParametrizationCompletenessSource) :
    G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeSource :=
  G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeSource.ofLobeEquivalence
    source.toLobeEquivalence

end G8BookIIICh23TauCircleParametrizationCompletenessSource

/-- Target for the tau-circle parametrization completeness theorem. -/
def G8BookIIICh23TauCircleParametrizationCompletenessTarget : Prop :=
  Nonempty G8BookIIICh23TauCircleParametrizationCompletenessSource

/-- Parametrization completeness is sufficient for the quotient bridge target. -/
theorem
    g8BookIIICh23TauCircleParametrizationCompletenessTarget_toQuotientBridgeTarget
    (target : G8BookIIICh23TauCircleParametrizationCompletenessTarget) :
    G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeTarget := by
  rcases target with ⟨source⟩
  exact ⟨source.toQuotientBridge⟩

-- ============================================================
-- A1.1 CLOSURE SOURCE
-- ============================================================

/-- Exact A1.1 closure source for transferring the concrete Ch.23
    `UnitAddCircle` wedge graph to the tau-native lemniscate carrier.

The lobe equivalence field is intentionally prior to the quotient bridge:
the quotient bridge is theorem-backed from it by
`G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeSource.ofLobeEquivalence`.
The topology, graph metric, compactness, topology/metric agreement, and
shortest-path fields are still exact transfer data, not inferred from the
quotient equivalence alone. -/
structure G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource where
  concrete :
    G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource
  lobeEquivalence :
    G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence
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

namespace G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource

/-- The lobe equivalence canonically supplies the quotient bridge. -/
noncomputable def toQuotientBridge
    (source : G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource) :
    G8BookIIICh23UnitAddCircleTauNativeQuotientBridgeSource where
  lobeEquivalence := source.lobeEquivalence
  crossing_preserved := source.lobeEquivalence.toCarrierEquiv_crossing
  lobe_preserved := source.lobeEquivalence.toCarrierEquiv_lobe
  quotientEquivalenceTheoremBacked :=
    Nonempty (G8Ch23UnitAddCircleWedgeCarrier ≃ LemniscateCarrier)
  quotientEquivalenceTheoremBackedEvidence :=
    ⟨source.lobeEquivalence.toCarrierEquiv⟩
  status := source.status

/-- The full A1.1 closure source supplies the split metric-transfer source. -/
noncomputable def toMetricTransferSource
    (source : G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource) :
    G8BookIIICh23UnitAddCircleTauNativeMetricTransferSource where
  concrete := source.concrete
  quotientBridge := source.toQuotientBridge
  carrierCtx := source.carrierCtx
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
  metricTransferFromConcreteWedge :=
    source.metricTransferFromConcreteWedge
  metricTransferFromConcreteWedgeEvidence :=
    source.metricTransferFromConcreteWedgeEvidence
  status := source.status

/-- The full A1.1 closure source discharges the split metric-transfer target. -/
theorem toMetricTransferTarget
    (source : G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource) :
    G8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget :=
  ⟨source.toMetricTransferSource⟩

/-- The full A1.1 closure source discharges the tau-native compact metric graph
    package target. -/
theorem toCompactMetricGraphPackageTarget
    (source : G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource) :
    G8BookIIILemniscateCompactMetricGraphPackageTarget :=
  g8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget_toPackageTarget
    source.toMetricTransferTarget

/-- The full A1.1 closure source also supplies the tau-native realization
    target, using the existing package/realization equivalence. -/
theorem toTauNativeRealizationTarget
    (source : G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource) :
    G8BookIIILemniscateTauNativeCompactMetricGraphRealizationTarget :=
  (g8BookIIILemniscateTauNativeCompactMetricGraphRealizationTarget_iff_packageTarget).mpr
    source.toCompactMetricGraphPackageTarget

end G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource

/-- Parametrization-complete variant of the A1.1 closure source.

This is the same A1.1 closure theorem, but with the lobe equivalence generated
from the stricter tau-circle parametrization completeness source. -/
structure G8BookIIICh23TauCircleParametrizedA11ClosureSource where
  concrete :
    G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource
  tauCircleParam :
    G8BookIIICh23TauCircleParametrizationCompletenessSource
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

namespace G8BookIIICh23TauCircleParametrizedA11ClosureSource

/-- The parametrization-complete variant supplies the existing assembled A1.1
    closure source by constructing the lobe equivalence first. -/
def toA11ClosureSource
    (source : G8BookIIICh23TauCircleParametrizedA11ClosureSource) :
    G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource where
  concrete := source.concrete
  lobeEquivalence := source.tauCircleParam.toLobeEquivalence
  carrierCtx := source.carrierCtx
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
  metricTransferFromConcreteWedge :=
    source.metricTransferFromConcreteWedge
  metricTransferFromConcreteWedgeEvidence :=
    source.metricTransferFromConcreteWedgeEvidence
  status := source.status

end G8BookIIICh23TauCircleParametrizedA11ClosureSource

/-- Target for the assembled A1.1 concrete-to-tau-native closure theorem. -/
def G8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget : Prop :=
  Nonempty G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource

/-- Target for the parametrization-complete A1.1 closure theorem. -/
def G8BookIIICh23TauCircleParametrizedA11ClosureTarget : Prop :=
  Nonempty G8BookIIICh23TauCircleParametrizedA11ClosureSource

/-- The parametrization-complete closure target supplies the assembled A1.1
    closure target. -/
theorem
    g8BookIIICh23TauCircleParametrizedA11ClosureTarget_toA11ClosureTarget
    (target : G8BookIIICh23TauCircleParametrizedA11ClosureTarget) :
    G8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget := by
  rcases target with ⟨source⟩
  exact ⟨source.toA11ClosureSource⟩

/-- Target-level adapter from the assembled A1.1 source to the metric-transfer
    target. -/
theorem
    g8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget_toMetricTransferTarget
    (target : G8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget) :
    G8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget := by
  rcases target with ⟨source⟩
  exact source.toMetricTransferTarget

/-- Target-level adapter from the assembled A1.1 source to the tau-native
    compact metric graph package target. -/
theorem
    g8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget_toPackageTarget
    (target : G8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget) :
    G8BookIIILemniscateCompactMetricGraphPackageTarget :=
  g8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget_toPackageTarget
    (g8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget_toMetricTransferTarget
      target)

/-- Target-level adapter from the assembled A1.1 source to the tau-native
    compact metric graph realization target. -/
theorem
    g8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget_toRealizationTarget
    (target : G8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget) :
    G8BookIIILemniscateTauNativeCompactMetricGraphRealizationTarget :=
  (g8BookIIILemniscateTauNativeCompactMetricGraphRealizationTarget_iff_packageTarget).mpr
    (g8BookIIICh23UnitAddCircleTauNativeA11ClosureTarget_toPackageTarget
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Without the concrete compact metric graph source, the assembled closure
    source cannot be obtained. -/
structure G8BookIIICh23A11ClosureWithoutConcreteGraph where
  noConcreteGraph :
    ¬ G8BookIIICh23ConcreteCompactMetricGraphTarget

/-- Any assembled closure source includes a concrete compact metric graph
    source. -/
theorem G8BookIIICh23A11ClosureWithoutConcreteGraph.refutesSource
    {source : G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource}
    (gap : G8BookIIICh23A11ClosureWithoutConcreteGraph) :
    False :=
  gap.noConcreteGraph source.concrete.toTarget

/-- Without a basepoint-preserving tau-circle lobe equivalence, the assembled
    closure source cannot be obtained. -/
structure G8BookIIICh23A11ClosureWithoutLobeEquivalence where
  noLobeEquivalence :
    ¬ Nonempty G8BookIIICh23UnitAddCircleTauCircleLobeEquivalence

/-- Any assembled closure source includes the exact lobe equivalence. -/
theorem G8BookIIICh23A11ClosureWithoutLobeEquivalence.refutesSource
    {source : G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource}
    (gap : G8BookIIICh23A11ClosureWithoutLobeEquivalence) :
    False :=
  gap.noLobeEquivalence ⟨source.lobeEquivalence⟩

/-- A quotient bridge without exact topology/metric transfer is not an A1.1
    closure. -/
structure G8BookIIICh23A11ClosureWithoutMetricTransfer where
  noMetricTransfer :
    ¬ G8BookIIICh23UnitAddCircleTauNativeMetricTransferTarget

/-- Any assembled closure source supplies the split metric-transfer target. -/
theorem G8BookIIICh23A11ClosureWithoutMetricTransfer.refutesSource
    {source : G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource}
    (gap : G8BookIIICh23A11ClosureWithoutMetricTransfer) :
    False :=
  gap.noMetricTransfer source.toMetricTransferTarget

/-- Weakening the metric transfer to a non-graph-metric context refutes the
    assembled closure source. -/
structure G8BookIIICh23A11ClosureMissingGraphMetric
    (source : G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource) where
  noGraphMetric : ¬ source.carrierCtx.metricIsGraphMetric

/-- The assembled A1.1 source carries exact graph-metric evidence. -/
theorem G8BookIIICh23A11ClosureMissingGraphMetric.refutesSource
    {source : G8BookIIICh23UnitAddCircleTauNativeA11ClosureSource}
    (gap : G8BookIIICh23A11ClosureMissingGraphMetric source) :
    False :=
  gap.noGraphMetric source.metricTransferred

/-- A tau-circle parametrization that misses the basepoint cannot be promoted
    to the lobe equivalence used by the quotient bridge. -/
structure G8BookIIICh23TauCircleParametrizationBasepointGap
    (source : G8BookIIICh23TauCircleParametrizationCompletenessSource) where
  notBasepointPreserving :
    source.toTauCircle G8Ch23UnitAddCircleWedgePoint.basepoint ≠
      TauCirclePoint.base

/-- Parametrization completeness requires exact basepoint preservation. -/
theorem
    G8BookIIICh23TauCircleParametrizationBasepointGap.refutesSource
    {source : G8BookIIICh23TauCircleParametrizationCompletenessSource}
    (gap : G8BookIIICh23TauCircleParametrizationBasepointGap source) :
    False :=
  gap.notBasepointPreserving source.basepoint_preserving

/-- Parametrization completeness alone does not close the tau-native compact
    graph package without concrete graph and transfer fields. -/
structure G8BookIIICh23TauCircleParametrizationWithoutA11Transfer where
  tauCircleParam :
    G8BookIIICh23TauCircleParametrizationCompletenessSource
  noParametrizedClosure :
    ¬ G8BookIIICh23TauCircleParametrizedA11ClosureTarget

/-- The parametrization-only gap refutes exactly the parametrized closure
    target, not the quotient equivalence supplied by the parametrization. -/
theorem
    G8BookIIICh23TauCircleParametrizationWithoutA11Transfer.refutesClosure
    (gap : G8BookIIICh23TauCircleParametrizationWithoutA11Transfer) :
    ¬ G8BookIIICh23TauCircleParametrizedA11ClosureTarget :=
  gap.noParametrizedClosure

end Tau.BookIII.Bridge
