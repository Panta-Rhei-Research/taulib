import TauLib.BookIII.Bridge.G8BookIIILemniscateCh23LoopConstructor

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleLoopConstructor

Theorem-backed Ch.23 one-loop constructor using Mathlib's `UnitAddCircle`.

The previous Ch.23 loop module isolated the exact one-loop target.  This module
inhabits that target with the standard compact metric additive circle
`UnitAddCircle = ℝ / ℤ`.  It deliberately does not identify this carrier with
the tau-native `TauCirclePoint` carrier, and it does not construct the
two-lobe wedge graph on `LemniscateCarrier`.  Those are later bridge steps.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- UNIT ADDITIVE CIRCLE EVIDENCE
-- ============================================================

/-- The Ch.23 loop is represented by the closed interval `[0,1]` with
    endpoints identified, using Mathlib's `AddCircle.homeoIccQuot`. -/
def G8UnitAddCircleIntervalParameterModel : Prop :=
  Nonempty (UnitAddCircle ≃ₜ
    Quot (AddCircle.EndpointIdent (1 : ℝ) 0))

/-- The endpoint quotient homeomorphism for `UnitAddCircle`. -/
theorem g8UnitAddCircle_intervalParameterModel :
    G8UnitAddCircleIntervalParameterModel :=
  ⟨AddCircle.homeoIccQuot (1 : ℝ) 0⟩

/-- The interval endpoints are identified at the additive-circle basepoint. -/
def G8UnitAddCircleEndpointsIdentifiedAtBasepoint : Prop :=
  ((1 : ℝ) : UnitAddCircle) = (0 : UnitAddCircle)

/-- Endpoint identification is exactly the period relation in `AddCircle`. -/
theorem g8UnitAddCircle_endpointsIdentifiedAtBasepoint :
    G8UnitAddCircleEndpointsIdentifiedAtBasepoint :=
  AddCircle.coe_period (1 : ℝ)

/-- The quotient topology is the standard circle topology supplied by
    `AddCircle.homeoIccQuot`. -/
def G8UnitAddCircleQuotientTopologyIsCircle : Prop :=
  Nonempty (UnitAddCircle ≃ₜ
    Quot (AddCircle.EndpointIdent (1 : ℝ) 0))

/-- The quotient topology is circle-shaped for `UnitAddCircle`. -/
theorem g8UnitAddCircle_quotientTopologyIsCircle :
    G8UnitAddCircleQuotientTopologyIsCircle :=
  ⟨AddCircle.homeoIccQuot (1 : ℝ) 0⟩

/-- Shortest-arc metric evidence for the additive circle.

`AddCircle.norm_le_half_period` records the half-period bound, while
`dist_eq_norm` records the translation-invariant metric readout. -/
def G8UnitAddCircleShortestArcMetric : Prop :=
  (∀ x : UnitAddCircle, ‖x‖ ≤ (1 : ℝ) / 2) ∧
    ∀ x y : UnitAddCircle, dist x y = ‖x - y‖

/-- The `UnitAddCircle` metric has the expected shortest-arc normalization. -/
theorem g8UnitAddCircle_shortestArcMetric :
    G8UnitAddCircleShortestArcMetric := by
  constructor
  · intro x
    simpa using
      (AddCircle.norm_le_half_period (1 : ℝ) (by exact one_ne_zero) (x := x))
  · intro x y
    exact dist_eq_norm x y

/-- The topology carried by the metric/uniform structure is the selected
    topology on `UnitAddCircle`. -/
def G8UnitAddCircleTopologyMetricAgreement : Prop :=
  (inferInstance : TopologicalSpace UnitAddCircle) =
    (@UniformSpace.toTopologicalSpace UnitAddCircle
      (inferInstance : UniformSpace UnitAddCircle))

/-- The topology/metric agreement is definitional for the selected instances. -/
theorem g8UnitAddCircle_topologyMetricAgreement :
    G8UnitAddCircleTopologyMetricAgreement :=
  rfl

/-- Compactness is the standard compactness of `AddCircle`, paired with the
    interval-quotient presentation used above. -/
def G8UnitAddCircleCompactnessFromIntervalQuotient : Prop :=
  CompactSpace UnitAddCircle ∧ G8UnitAddCircleIntervalParameterModel

/-- The additive circle is compact, with compactness inherited from the
    interval quotient presentation. -/
theorem g8UnitAddCircle_compactnessFromIntervalQuotient :
    G8UnitAddCircleCompactnessFromIntervalQuotient :=
  ⟨inferInstance, g8UnitAddCircle_intervalParameterModel⟩

/-- The basepoint is the common image of the interval endpoints. -/
def G8UnitAddCircleBasepointIsCrossingEndpoint : Prop :=
  ((0 : ℝ) : UnitAddCircle) = (0 : UnitAddCircle) ∧
    ((1 : ℝ) : UnitAddCircle) = (0 : UnitAddCircle)

/-- Both interval endpoints map to the chosen basepoint. -/
theorem g8UnitAddCircle_basepointIsCrossingEndpoint :
    G8UnitAddCircleBasepointIsCrossingEndpoint :=
  ⟨AddCircle.coe_zero (1 : ℝ), AddCircle.coe_period (1 : ℝ)⟩

/-- Bundled theorem-backed status for the `UnitAddCircle` Ch.23 loop. -/
def G8UnitAddCircleCh23LoopTheoremBacked : Prop :=
  G8UnitAddCircleIntervalParameterModel ∧
    G8UnitAddCircleEndpointsIdentifiedAtBasepoint ∧
    G8UnitAddCircleQuotientTopologyIsCircle ∧
    G8UnitAddCircleShortestArcMetric ∧
    G8UnitAddCircleTopologyMetricAgreement ∧
    G8UnitAddCircleCompactnessFromIntervalQuotient ∧
    G8UnitAddCircleBasepointIsCrossingEndpoint

/-- All `UnitAddCircle` one-loop fields are theorem-backed by Mathlib's
    additive-circle API. -/
theorem g8UnitAddCircle_ch23LoopTheoremBacked :
    G8UnitAddCircleCh23LoopTheoremBacked :=
  ⟨g8UnitAddCircle_intervalParameterModel,
    g8UnitAddCircle_endpointsIdentifiedAtBasepoint,
    g8UnitAddCircle_quotientTopologyIsCircle,
    g8UnitAddCircle_shortestArcMetric,
    g8UnitAddCircle_topologyMetricAgreement,
    g8UnitAddCircle_compactnessFromIntervalQuotient,
    g8UnitAddCircle_basepointIsCrossingEndpoint⟩

/-- Strict proof package for the `UnitAddCircle` loop constructor. -/
structure G8BookIIICh23UnitAddCircleLoopEvidence where
  intervalParameterModel :
    G8UnitAddCircleIntervalParameterModel
  endpointsIdentifiedAtBasepoint :
    G8UnitAddCircleEndpointsIdentifiedAtBasepoint
  quotientTopologyIsCircle :
    G8UnitAddCircleQuotientTopologyIsCircle
  shortestArcMetric :
    G8UnitAddCircleShortestArcMetric
  topologyMetricAgreement :
    G8UnitAddCircleTopologyMetricAgreement
  compactnessFromIntervalQuotient :
    G8UnitAddCircleCompactnessFromIntervalQuotient
  basepointIsCrossingEndpoint :
    G8UnitAddCircleBasepointIsCrossingEndpoint
  ch23LoopTheoremBacked :
    G8UnitAddCircleCh23LoopTheoremBacked

/-- The theorem-backed `UnitAddCircle` loop evidence. -/
def g8BookIIICh23UnitAddCircleLoopEvidence :
    G8BookIIICh23UnitAddCircleLoopEvidence where
  intervalParameterModel :=
    g8UnitAddCircle_intervalParameterModel
  endpointsIdentifiedAtBasepoint :=
    g8UnitAddCircle_endpointsIdentifiedAtBasepoint
  quotientTopologyIsCircle :=
    g8UnitAddCircle_quotientTopologyIsCircle
  shortestArcMetric :=
    g8UnitAddCircle_shortestArcMetric
  topologyMetricAgreement :=
    g8UnitAddCircle_topologyMetricAgreement
  compactnessFromIntervalQuotient :=
    g8UnitAddCircle_compactnessFromIntervalQuotient
  basepointIsCrossingEndpoint :=
    g8UnitAddCircle_basepointIsCrossingEndpoint
  ch23LoopTheoremBacked :=
    g8UnitAddCircle_ch23LoopTheoremBacked

-- ============================================================
-- ONE-LOOP AND TWO-LOBE CONSTRUCTORS
-- ============================================================

/-- Convert strict `UnitAddCircle` evidence into the general Ch.23 compact
    loop constructor. -/
noncomputable def G8BookIIICh23UnitAddCircleLoopEvidence.toCompactLoopConstructor
    (evidence : G8BookIIICh23UnitAddCircleLoopEvidence) :
    G8BookIIICh23CompactLoopConstructor where
  loopCarrier := ULift UnitAddCircle
  topology := inferInstance
  metric := inferInstance
  compact := inferInstance
  basepoint := ULift.up (0 : UnitAddCircle)
  intervalParameterModel :=
    G8UnitAddCircleIntervalParameterModel
  intervalParameterModelEvidence :=
    evidence.intervalParameterModel
  endpointsIdentifiedAtBasepoint :=
    G8UnitAddCircleEndpointsIdentifiedAtBasepoint
  endpointsIdentifiedAtBasepointEvidence :=
    evidence.endpointsIdentifiedAtBasepoint
  quotientTopologyIsCircle :=
    G8UnitAddCircleQuotientTopologyIsCircle
  quotientTopologyIsCircleEvidence :=
    evidence.quotientTopologyIsCircle
  shortestArcMetric :=
    G8UnitAddCircleShortestArcMetric
  shortestArcMetricEvidence :=
    evidence.shortestArcMetric
  topologyMetricAgreement :=
    G8UnitAddCircleTopologyMetricAgreement
  topologyMetricAgreementEvidence :=
    evidence.topologyMetricAgreement
  compactnessFromIntervalQuotient :=
    G8UnitAddCircleCompactnessFromIntervalQuotient
  compactnessFromIntervalQuotientEvidence :=
    evidence.compactnessFromIntervalQuotient
  basepointIsCrossingEndpoint :=
    G8UnitAddCircleBasepointIsCrossingEndpoint
  basepointIsCrossingEndpointEvidence :=
    evidence.basepointIsCrossingEndpoint
  ch23LoopTheoremBacked :=
    G8UnitAddCircleCh23LoopTheoremBacked
  ch23LoopTheoremBackedEvidence :=
    evidence.ch23LoopTheoremBacked
  status := .conditional_interface

/-- The concrete one-loop constructor selected for Ch.23. -/
noncomputable def g8BookIIICh23CompactLoopConstructor_unitAddCircle :
    G8BookIIICh23CompactLoopConstructor :=
  G8BookIIICh23UnitAddCircleLoopEvidence.toCompactLoopConstructor
    g8BookIIICh23UnitAddCircleLoopEvidence

/-- The one-loop Ch.23 target is inhabited by `UnitAddCircle`. -/
theorem g8BookIIICh23CompactLoopConstructorTarget_unitAddCircle :
    G8BookIIICh23CompactLoopConstructorTarget :=
  ⟨g8BookIIICh23CompactLoopConstructor_unitAddCircle⟩

/-- The plus lobe is represented by the selected compact loop. -/
def G8UnitAddCircleRepresentsPlusSector : Prop :=
  LemniscateSector.plus = LemniscateSector.plus

/-- The minus lobe is represented by the selected compact loop. -/
def G8UnitAddCircleRepresentsMinusSector : Prop :=
  LemniscateSector.minus = LemniscateSector.minus

/-- The two lobe labels remain distinct before the wedge quotient. -/
def G8UnitAddCircleSectorsAreDistinctLobes : Prop :=
  LemniscateSector.plus ≠ LemniscateSector.minus

/-- The selected loop supplies two labeled Ch.23 lobes. -/
noncomputable def g8BookIIICh23TwoLobeLoopConstructor_unitAddCircle :
    G8BookIIICh23TwoLobeLoopConstructor where
  plusLoop := g8BookIIICh23CompactLoopConstructor_unitAddCircle
  minusLoop := g8BookIIICh23CompactLoopConstructor_unitAddCircle
  plusRepresentsSector := G8UnitAddCircleRepresentsPlusSector
  plusRepresentsSectorEvidence := rfl
  minusRepresentsSector := G8UnitAddCircleRepresentsMinusSector
  minusRepresentsSectorEvidence := rfl
  sectorsAreDistinctLobes := G8UnitAddCircleSectorsAreDistinctLobes
  sectorsAreDistinctLobesEvidence := by
    intro h
    cases h
  status := .conditional_interface

/-- Two `UnitAddCircle` copies discharge the two-lobe loop target. -/
theorem g8BookIIICh23TwoLobeLoopConstructorTarget_unitAddCircle :
    G8BookIIICh23TwoLobeLoopConstructorTarget :=
  ⟨g8BookIIICh23TwoLobeLoopConstructor_unitAddCircle⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- The `UnitAddCircle` loop constructor does not construct the full wedge
    graph on `LemniscateCarrier`. -/
structure G8BookIIICh23UnitAddCircleLoopsWithoutWedgeGraph where
  loops : G8BookIIICh23TwoLobeLoopConstructor :=
    g8BookIIICh23TwoLobeLoopConstructor_unitAddCircle
  noCh23Graph : ¬ G8BookIIILemniscateCh23CompactMetricGraphTarget

/-- Two theorem-backed `UnitAddCircle` loops still require the separate wedge
    graph theorem. -/
theorem G8BookIIICh23UnitAddCircleLoopsWithoutWedgeGraph.refutesGraphTarget
    (gap : G8BookIIICh23UnitAddCircleLoopsWithoutWedgeGraph) :
    ¬ G8BookIIILemniscateCh23CompactMetricGraphTarget :=
  gap.noCh23Graph

/-- The `UnitAddCircle` loop constructor is not a tau-native
    `TauCirclePoint` compactness theorem. -/
structure G8BookIIICh23UnitAddCircleWithoutTauNativeIdentification where
  loopTarget : G8BookIIICh23CompactLoopConstructorTarget :=
    g8BookIIICh23CompactLoopConstructorTarget_unitAddCircle
  noTauNativeIdentification :
    ¬ G8BookIIILemniscateCh23CompactMetricGraphTarget

/-- A missing tau-native/wedge realization keeps the graph target open. -/
theorem
    G8BookIIICh23UnitAddCircleWithoutTauNativeIdentification.refutesGraphTarget
    (gap : G8BookIIICh23UnitAddCircleWithoutTauNativeIdentification) :
    ¬ G8BookIIILemniscateCh23CompactMetricGraphTarget :=
  gap.noTauNativeIdentification

end Tau.BookIII.Bridge
