import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleLoopConstructor

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleWedgeGraphConstructor

Concrete Ch.23 two-lobe wedge graph constructor from theorem-backed
`UnitAddCircle` loops.

The previous module proved the one-loop and two-loop Ch.23 targets using the
standard compact additive circle.  This module builds the corresponding raw
two-lobe wedge quotient carrier and closes the purely quotient-level
basepoint/crossing facts.

It deliberately does not identify the concrete `UnitAddCircle` wedge with the
current tau-native `LemniscateCarrier`.  That identification is a separate
bridge theorem.  It also keeps the full quotient topology, shortest-path graph
metric, compactness, and topology/metric agreement as exact proof-carrying
fields unless and until they are theorem-backed by the metric-graph API.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CONCRETE UNITADDCIRCLE WEDGE CARRIER
-- ============================================================

/-- Raw points of the concrete Ch.23 wedge: one crossing point plus one
    `UnitAddCircle` copy for each lobe. -/
inductive G8Ch23UnitAddCircleWedgePoint where
  | crossing : G8Ch23UnitAddCircleWedgePoint
  | lobe : LemniscateSector → UnitAddCircle →
      G8Ch23UnitAddCircleWedgePoint

namespace G8Ch23UnitAddCircleWedgePoint

/-- The raw crossing point. -/
def omega : G8Ch23UnitAddCircleWedgePoint :=
  .crossing

/-- The additive-circle basepoint used for the lobe gluing. -/
def basepoint : UnitAddCircle :=
  0

/-- The raw basepoint on a selected lobe. -/
def lobeBase (s : LemniscateSector) :
    G8Ch23UnitAddCircleWedgePoint :=
  .lobe s basepoint

/-- Predicate for the crossing equivalence class: the explicit crossing plus
    the two lobe basepoints. -/
def InCrossingClass : G8Ch23UnitAddCircleWedgePoint → Prop
  | .crossing => True
  | .lobe _ p => p = basepoint

/-- Raw wedge equivalence for the concrete two-circle wedge. -/
def WedgeEquivalent
    (x y : G8Ch23UnitAddCircleWedgePoint) : Prop :=
  x = y ∨ (InCrossingClass x ∧ InCrossingClass y)

/-- Wedge equivalence is reflexive. -/
theorem WedgeEquivalent.refl
    (x : G8Ch23UnitAddCircleWedgePoint) :
    WedgeEquivalent x x :=
  Or.inl rfl

/-- Wedge equivalence is symmetric. -/
theorem WedgeEquivalent.symm
    {x y : G8Ch23UnitAddCircleWedgePoint}
    (h : WedgeEquivalent x y) :
    WedgeEquivalent y x := by
  cases h with
  | inl hxy =>
      exact Or.inl hxy.symm
  | inr hxy =>
      exact Or.inr ⟨hxy.right, hxy.left⟩

/-- Wedge equivalence is transitive. -/
theorem WedgeEquivalent.trans
    {x y z : G8Ch23UnitAddCircleWedgePoint}
    (hxy : WedgeEquivalent x y)
    (hyz : WedgeEquivalent y z) :
    WedgeEquivalent x z := by
  cases hxy with
  | inl hxy =>
      subst y
      exact hyz
  | inr hxyc =>
      cases hyz with
      | inl hyz =>
          subst z
          exact Or.inr hxyc
      | inr hyzc =>
          exact Or.inr ⟨hxyc.left, hyzc.right⟩

/-- Setoid implementing the concrete two-circle wedge quotient. -/
def wedgeSetoid : Setoid G8Ch23UnitAddCircleWedgePoint where
  r := WedgeEquivalent
  iseqv :=
    ⟨WedgeEquivalent.refl,
      WedgeEquivalent.symm,
      WedgeEquivalent.trans⟩

/-- Primitive raw relations whose soundness is used by the quotient carrier. -/
inductive WedgeRelated :
    G8Ch23UnitAddCircleWedgePoint →
      G8Ch23UnitAddCircleWedgePoint → Prop where
  | refl (x : G8Ch23UnitAddCircleWedgePoint) : WedgeRelated x x
  | plus_base_to_crossing :
      WedgeRelated (lobeBase .plus) omega
  | minus_base_to_crossing :
      WedgeRelated (lobeBase .minus) omega
  | crossing_to_plus_base :
      WedgeRelated omega (lobeBase .plus)
  | crossing_to_minus_base :
      WedgeRelated omega (lobeBase .minus)
  | base_glue :
      WedgeRelated (lobeBase .plus) (lobeBase .minus)

/-- The primitive raw wedge relation is contained in wedge equivalence. -/
theorem WedgeRelated.toEquivalent {x y : G8Ch23UnitAddCircleWedgePoint}
    (h : WedgeRelated x y) :
    WedgeEquivalent x y := by
  cases h with
  | refl x =>
      exact WedgeEquivalent.refl x
  | plus_base_to_crossing =>
      exact Or.inr ⟨rfl, trivial⟩
  | minus_base_to_crossing =>
      exact Or.inr ⟨rfl, trivial⟩
  | crossing_to_plus_base =>
      exact Or.inr ⟨trivial, rfl⟩
  | crossing_to_minus_base =>
      exact Or.inr ⟨trivial, rfl⟩
  | base_glue =>
      exact Or.inr ⟨rfl, rfl⟩

end G8Ch23UnitAddCircleWedgePoint

/-- Concrete quotient carrier for `S1_B ∨ S1_C` built from two copies of
    `UnitAddCircle`. -/
abbrev G8Ch23UnitAddCircleWedgeCarrier : Type :=
  Quotient G8Ch23UnitAddCircleWedgePoint.wedgeSetoid

namespace G8Ch23UnitAddCircleWedgeCarrier

/-- Concrete crossing class. -/
def crossing : G8Ch23UnitAddCircleWedgeCarrier :=
  Quotient.mk G8Ch23UnitAddCircleWedgePoint.wedgeSetoid
    G8Ch23UnitAddCircleWedgePoint.omega

/-- Concrete lobe point. -/
def lobe (s : LemniscateSector) (p : UnitAddCircle) :
    G8Ch23UnitAddCircleWedgeCarrier :=
  Quotient.mk G8Ch23UnitAddCircleWedgePoint.wedgeSetoid
    (G8Ch23UnitAddCircleWedgePoint.lobe s p)

/-- The basepoint on each concrete lobe is the crossing class. -/
theorem lobe_base_eq_crossing (s : LemniscateSector) :
    lobe s G8Ch23UnitAddCircleWedgePoint.basepoint =
      crossing := by
  apply Quotient.sound
  exact Or.inr ⟨rfl, trivial⟩

/-- The two concrete lobe basepoints are glued together. -/
theorem plus_base_eq_minus_base :
    lobe .plus G8Ch23UnitAddCircleWedgePoint.basepoint =
      lobe .minus G8Ch23UnitAddCircleWedgePoint.basepoint := by
  apply Quotient.sound
  exact Or.inr ⟨rfl, rfl⟩

/-- Primitive wedge-related raw points become equal in the quotient carrier. -/
theorem sound_wedge_related
    {x y : G8Ch23UnitAddCircleWedgePoint}
    (h : G8Ch23UnitAddCircleWedgePoint.WedgeRelated x y) :
    Quotient.mk G8Ch23UnitAddCircleWedgePoint.wedgeSetoid x =
      Quotient.mk G8Ch23UnitAddCircleWedgePoint.wedgeSetoid y := by
  exact Quotient.sound h.toEquivalent

end G8Ch23UnitAddCircleWedgeCarrier

-- ============================================================
-- CLOSED QUOTIENT-CORE PACKAGE
-- ============================================================

/-- The theorem-backed quotient-core facts for the concrete Ch.23 wedge. -/
structure G8BookIIICh23UnitAddCircleWedgeCore where
  loops : G8BookIIICh23TwoLobeLoopConstructor
  loopTarget :
    G8BookIIICh23TwoLobeLoopConstructorTarget
  plusBase_eq_crossing :
    G8Ch23UnitAddCircleWedgeCarrier.lobe .plus
      G8Ch23UnitAddCircleWedgePoint.basepoint =
        G8Ch23UnitAddCircleWedgeCarrier.crossing
  minusBase_eq_crossing :
    G8Ch23UnitAddCircleWedgeCarrier.lobe .minus
      G8Ch23UnitAddCircleWedgePoint.basepoint =
        G8Ch23UnitAddCircleWedgeCarrier.crossing
  plusBase_eq_minusBase :
    G8Ch23UnitAddCircleWedgeCarrier.lobe .plus
      G8Ch23UnitAddCircleWedgePoint.basepoint =
        G8Ch23UnitAddCircleWedgeCarrier.lobe .minus
          G8Ch23UnitAddCircleWedgePoint.basepoint
  wedgeRelated_sound :
    ∀ {x y : G8Ch23UnitAddCircleWedgePoint},
      G8Ch23UnitAddCircleWedgePoint.WedgeRelated x y →
        Quotient.mk G8Ch23UnitAddCircleWedgePoint.wedgeSetoid x =
          Quotient.mk G8Ch23UnitAddCircleWedgePoint.wedgeSetoid y
  concreteQuotientCarrierDefined : Prop
  concreteQuotientCarrierDefinedEvidence :
    concreteQuotientCarrierDefined
  basepointCrossingQuotientClosed : Prop
  basepointCrossingQuotientClosedEvidence :
    basepointCrossingQuotientClosed
  status : SpineStatus := .conditional_interface

/-- The concrete `UnitAddCircle` wedge quotient core is theorem-backed. -/
noncomputable def g8BookIIICh23UnitAddCircleWedgeCore :
    G8BookIIICh23UnitAddCircleWedgeCore where
  loops :=
    g8BookIIICh23TwoLobeLoopConstructor_unitAddCircle
  loopTarget :=
    g8BookIIICh23TwoLobeLoopConstructorTarget_unitAddCircle
  plusBase_eq_crossing :=
    G8Ch23UnitAddCircleWedgeCarrier.lobe_base_eq_crossing .plus
  minusBase_eq_crossing :=
    G8Ch23UnitAddCircleWedgeCarrier.lobe_base_eq_crossing .minus
  plusBase_eq_minusBase :=
    G8Ch23UnitAddCircleWedgeCarrier.plus_base_eq_minus_base
  wedgeRelated_sound := by
    intro x y h
    exact G8Ch23UnitAddCircleWedgeCarrier.sound_wedge_related h
  concreteQuotientCarrierDefined :=
    Nonempty G8Ch23UnitAddCircleWedgeCarrier
  concreteQuotientCarrierDefinedEvidence :=
    ⟨G8Ch23UnitAddCircleWedgeCarrier.crossing⟩
  basepointCrossingQuotientClosed :=
    G8Ch23UnitAddCircleWedgeCarrier.lobe .plus
      G8Ch23UnitAddCircleWedgePoint.basepoint =
        G8Ch23UnitAddCircleWedgeCarrier.crossing ∧
      G8Ch23UnitAddCircleWedgeCarrier.lobe .minus
        G8Ch23UnitAddCircleWedgePoint.basepoint =
          G8Ch23UnitAddCircleWedgeCarrier.crossing
  basepointCrossingQuotientClosedEvidence :=
    ⟨G8Ch23UnitAddCircleWedgeCarrier.lobe_base_eq_crossing .plus,
      G8Ch23UnitAddCircleWedgeCarrier.lobe_base_eq_crossing .minus⟩

/-- Closed target for the concrete quotient-core construction. -/
def G8BookIIICh23UnitAddCircleWedgeCoreTarget : Prop :=
  Nonempty G8BookIIICh23UnitAddCircleWedgeCore

/-- The concrete quotient-core target is closed. -/
theorem g8BookIIICh23UnitAddCircleWedgeCore_closed :
    G8BookIIICh23UnitAddCircleWedgeCoreTarget :=
  ⟨g8BookIIICh23UnitAddCircleWedgeCore⟩

-- ============================================================
-- FULL CONCRETE COMPACT METRIC GRAPH SOURCE
-- ============================================================

/-- Full concrete compact metric graph source for the `UnitAddCircle` wedge.

The quotient-core fields are closed above.  The topology, metric, compactness,
topology/metric agreement, and shortest-path graph realization remain exact
proof fields so that this source cannot be filled by the zero-distance
scaffold or by finite diagnostics. -/
structure G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource where
  core : G8BookIIICh23UnitAddCircleWedgeCore
  topology : TopologicalSpace G8Ch23UnitAddCircleWedgeCarrier
  metric : MetricSpace G8Ch23UnitAddCircleWedgeCarrier
  compact : @CompactSpace G8Ch23UnitAddCircleWedgeCarrier topology
  quotientTopologyIsTwoCircleWedge : Prop
  quotientTopologyIsTwoCircleWedgeEvidence :
    quotientTopologyIsTwoCircleWedge
  compactnessFromCircleWedge : Prop
  compactnessFromCircleWedgeEvidence : compactnessFromCircleWedge
  shortestPathGraphMetric : Prop
  shortestPathGraphMetricEvidence : shortestPathGraphMetric
  topologyMetricAgreement : Prop
  topologyMetricAgreementEvidence : topologyMetricAgreement
  graphDistanceRealizesMetric : Prop
  graphDistanceRealizesMetricEvidence : graphDistanceRealizesMetric
  status : SpineStatus := .conditional_interface

/-- Target for the full concrete compact metric graph theorem. -/
def G8BookIIICh23ConcreteCompactMetricGraphTarget : Prop :=
  Nonempty G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource

/-- A concrete compact metric graph source trivially inhabits its target. -/
theorem
    G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource.toTarget
    (source : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource) :
    G8BookIIICh23ConcreteCompactMetricGraphTarget :=
  ⟨source⟩

-- ============================================================
-- BRIDGE TO THE TAU-NATIVE LEMNISCATE CARRIER
-- ============================================================

/-- Exact bridge from the concrete `UnitAddCircle` wedge graph to the current
    tau-native `LemniscateCarrier`.

This is deliberately separate from the concrete source.  Supplying it is the
remaining A1.1 carrier-realization theorem: the concrete Ch.23 quotient graph
and the tau-native carrier have the same topology, metric, compactness, and
shortest-path realization. -/
structure G8BookIIICh23UnitAddCircleWedgeTauNativeBridge where
  concrete :
    G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource
  carrierCtx : LemniscateCarrierContext
  carrierEquiv :
    G8Ch23UnitAddCircleWedgeCarrier ≃ LemniscateCarrier
  topologyTransferred : carrierCtx.topologyIsWedgeQuotient
  metricTransferred : carrierCtx.metricIsGraphMetric
  compactnessTransferred : carrierCtx.compactnessFromWedge
  topologyMetricAgreement : LemniscateTopologyMetricAgreement carrierCtx
  graphDistanceRealizesMetric : carrierCtx.graphDistanceRealizesMetric
  theoremBackedStatus : carrierCtx.status = .theoremBacked
  quotientMatchesLemniscateCarrier : Prop
  quotientMatchesLemniscateCarrierEvidence :
    quotientMatchesLemniscateCarrier
  status : SpineStatus := .conditional_interface

/-- A concrete-to-tau-native bridge supplies the existing Ch.23 compact metric
    graph source. -/
def G8BookIIICh23UnitAddCircleWedgeTauNativeBridge.toCh23CompactMetricGraphSource
    (bridge : G8BookIIICh23UnitAddCircleWedgeTauNativeBridge) :
    G8BookIIILemniscateCh23CompactMetricGraphSource where
  plusLobe := bridge.concrete.core.loops.plusLobeModel
  minusLobe := bridge.concrete.core.loops.minusLobeModel
  crossingIdentifiesBasepoints :=
    bridge.concrete.core.basepointCrossingQuotientClosed
  crossingIdentifiesBasepointsEvidence :=
    bridge.concrete.core.basepointCrossingQuotientClosedEvidence
  twoCircleWedgeQuotientConstructed :=
    bridge.concrete.core.concreteQuotientCarrierDefined ∧
      bridge.concrete.quotientTopologyIsTwoCircleWedge
  twoCircleWedgeQuotientConstructedEvidence :=
    ⟨bridge.concrete.core.concreteQuotientCarrierDefinedEvidence,
      bridge.concrete.quotientTopologyIsTwoCircleWedgeEvidence⟩
  quotientMatchesLemniscateCarrier :=
    bridge.quotientMatchesLemniscateCarrier
  quotientMatchesLemniscateCarrierEvidence :=
    bridge.quotientMatchesLemniscateCarrierEvidence
  carrierCtx := bridge.carrierCtx
  topologyIsWedgeQuotient := bridge.topologyTransferred
  metricIsGraphMetric := bridge.metricTransferred
  compactnessFromWedge := bridge.compactnessTransferred
  topologyMetricAgreement := bridge.topologyMetricAgreement
  graphDistanceRealizesMetric := bridge.graphDistanceRealizesMetric
  theoremBackedStatus := bridge.theoremBackedStatus
  compactMetricGraphFromCh23 :=
    bridge.concrete.compactnessFromCircleWedge ∧
      bridge.concrete.shortestPathGraphMetric ∧
      bridge.concrete.topologyMetricAgreement ∧
      bridge.concrete.graphDistanceRealizesMetric ∧
      bridge.quotientMatchesLemniscateCarrier
  compactMetricGraphFromCh23Evidence :=
    ⟨bridge.concrete.compactnessFromCircleWedgeEvidence,
      bridge.concrete.shortestPathGraphMetricEvidence,
      bridge.concrete.topologyMetricAgreementEvidence,
      bridge.concrete.graphDistanceRealizesMetricEvidence,
      bridge.quotientMatchesLemniscateCarrierEvidence⟩
  shortestPathMetricFromCircleLobes :=
    bridge.concrete.shortestPathGraphMetric
  shortestPathMetricFromCircleLobesEvidence :=
    bridge.concrete.shortestPathGraphMetricEvidence
  tauProfiniteCompatibilityDeferred :=
    True
  tauProfiniteCompatibilityDeferredEvidence :=
    trivial
  status := bridge.status

/-- Exact concrete-to-tau-native bridge target. -/
def G8BookIIICh23UnitAddCircleWedgeTauNativeBridgeTarget : Prop :=
  Nonempty G8BookIIICh23UnitAddCircleWedgeTauNativeBridge

/-- A concrete-to-tau-native bridge discharges the existing Ch.23 compact
    metric graph target. -/
theorem
    G8BookIIICh23UnitAddCircleWedgeTauNativeBridge.toCh23CompactMetricGraphTarget
    (bridge : G8BookIIICh23UnitAddCircleWedgeTauNativeBridge) :
    G8BookIIILemniscateCh23CompactMetricGraphTarget :=
  ⟨bridge.toCh23CompactMetricGraphSource⟩

/-- Target-level adapter from the concrete-to-tau-native bridge to the
    existing Ch.23 target. -/
theorem
    g8BookIIICh23UnitAddCircleWedgeTauNativeBridgeTarget_toCh23Target
    (target : G8BookIIICh23UnitAddCircleWedgeTauNativeBridgeTarget) :
    G8BookIIILemniscateCh23CompactMetricGraphTarget := by
  rcases target with ⟨bridge⟩
  exact bridge.toCh23CompactMetricGraphTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- The closed quotient core alone is not a full compact metric graph source. -/
structure G8BookIIICh23UnitAddCircleWedgeCoreWithoutMetricGraph where
  core : G8BookIIICh23UnitAddCircleWedgeCore
  noConcreteCompactMetricGraph :
    ¬ G8BookIIICh23ConcreteCompactMetricGraphTarget

/-- The quotient core refutes the full target exactly when topology/metric
    evidence is absent. -/
theorem
    G8BookIIICh23UnitAddCircleWedgeCoreWithoutMetricGraph.refutesConcreteTarget
    (gap : G8BookIIICh23UnitAddCircleWedgeCoreWithoutMetricGraph) :
    ¬ G8BookIIICh23ConcreteCompactMetricGraphTarget :=
  gap.noConcreteCompactMetricGraph

/-- A concrete graph source without tau-native equivalence does not identify
    the concrete carrier with `LemniscateCarrier`. -/
structure G8BookIIICh23ConcreteGraphWithoutTauNativeBridge where
  concrete :
    G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource
  noTauNativeBridge :
    ¬ G8BookIIICh23UnitAddCircleWedgeTauNativeBridgeTarget

/-- The absence of an exact tau-native bridge refutes only the bridge target,
    not the concrete graph source itself. -/
theorem
    G8BookIIICh23ConcreteGraphWithoutTauNativeBridge.refutesBridgeTarget
    (gap : G8BookIIICh23ConcreteGraphWithoutTauNativeBridge) :
    ¬ G8BookIIICh23UnitAddCircleWedgeTauNativeBridgeTarget :=
  gap.noTauNativeBridge

/-- A candidate bridge with the wrong tau-native quotient match refutes the
    bridge source. -/
structure G8BookIIICh23UnitAddCircleWrongTauNativeMatch
    (bridge : G8BookIIICh23UnitAddCircleWedgeTauNativeBridge) where
  noQuotientMatch : ¬ bridge.quotientMatchesLemniscateCarrier

/-- The bridge requires exact quotient-to-carrier matching. -/
theorem G8BookIIICh23UnitAddCircleWrongTauNativeMatch.refutesBridge
    {bridge : G8BookIIICh23UnitAddCircleWedgeTauNativeBridge}
    (gap : G8BookIIICh23UnitAddCircleWrongTauNativeMatch bridge) :
    False :=
  gap.noQuotientMatch bridge.quotientMatchesLemniscateCarrierEvidence

/-- A candidate concrete graph with a non-shortest-path metric cannot be used
    as the full concrete compact metric graph source. -/
structure G8BookIIICh23UnitAddCircleNonShortestPathMetric
    (source : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource)
    where
  noShortestPathMetric : ¬ source.shortestPathGraphMetric

/-- The concrete graph source requires exact shortest-path metric evidence. -/
theorem
    G8BookIIICh23UnitAddCircleNonShortestPathMetric.refutesConcreteSource
    {source : G8BookIIICh23ConcreteUnitAddCircleCompactMetricGraphSource}
    (gap : G8BookIIICh23UnitAddCircleNonShortestPathMetric source) :
    False :=
  gap.noShortestPathMetric source.shortestPathGraphMetricEvidence

end Tau.BookIII.Bridge
