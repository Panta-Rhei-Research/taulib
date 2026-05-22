import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleWedgeGraphConstructor

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleRawCompactWedgeModel

Theorem-backed raw compact model for the concrete Ch.23 two-lobe wedge.

`G8BookIIICh23UnitAddCircleWedgeGraphConstructor` closes the quotient-core
facts for the two `UnitAddCircle` lobes and leaves the full quotient topology,
graph metric, and tau-native transfer as proof-carrying fields.  This module
adds the next load-bearing brick below that target: a compact raw disjoint
model consisting of one crossing point and two compact `UnitAddCircle` lobes,
together with the exact equivalence to the raw wedge-point presentation.

It deliberately does not claim that the quotient carrier has already been
given the shortest-path metric or that it is the tau-native `LemniscateCarrier`.
Those remain the next A1.1 transfer theorems.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- RAW COMPACT TWO-LOBE MODEL
-- ============================================================

/-- A compact raw disjoint model for the Ch.23 wedge before quotienting:
    one crossing point plus one `UnitAddCircle` copy for each lobe. -/
abbrev G8Ch23UnitAddCircleRawCompactWedgeModel : Type :=
  Unit ⊕ (UnitAddCircle ⊕ UnitAddCircle)

namespace G8Ch23UnitAddCircleRawCompactWedgeModel

/-- The raw crossing point in the compact disjoint model. -/
def crossing : G8Ch23UnitAddCircleRawCompactWedgeModel :=
  Sum.inl ()

/-- The raw plus-lobe point in the compact disjoint model. -/
def plusLobe (p : UnitAddCircle) :
    G8Ch23UnitAddCircleRawCompactWedgeModel :=
  Sum.inr (Sum.inl p)

/-- The raw minus-lobe point in the compact disjoint model. -/
def minusLobe (p : UnitAddCircle) :
    G8Ch23UnitAddCircleRawCompactWedgeModel :=
  Sum.inr (Sum.inr p)

/-- Sector-indexed raw lobe constructor for the compact disjoint model. -/
def lobe (s : LemniscateSector) (p : UnitAddCircle) :
    G8Ch23UnitAddCircleRawCompactWedgeModel :=
  match s with
  | .plus => plusLobe p
  | .minus => minusLobe p

/-- The topology on the raw compact model is the finite sum topology carried
    by `Unit` and the two compact `UnitAddCircle` lobes. -/
abbrev topology : TopologicalSpace G8Ch23UnitAddCircleRawCompactWedgeModel :=
  inferInstance

/-- Compactness of the raw compact model is theorem-backed by compactness of
    `Unit`, compactness of `UnitAddCircle`, and compactness of finite sums. -/
abbrev compactSpace :
    @CompactSpace G8Ch23UnitAddCircleRawCompactWedgeModel topology :=
  inferInstance

end G8Ch23UnitAddCircleRawCompactWedgeModel

/-- Exact equivalence between the compact disjoint raw model and the raw
    wedge-point presentation used by the quotient constructor. -/
noncomputable def g8Ch23UnitAddCircleRawCompactWedgeModelEquiv :
    G8Ch23UnitAddCircleRawCompactWedgeModel ≃
      G8Ch23UnitAddCircleWedgePoint where
  toFun
    | Sum.inl _ => G8Ch23UnitAddCircleWedgePoint.crossing
    | Sum.inr (Sum.inl p) =>
        G8Ch23UnitAddCircleWedgePoint.lobe .plus p
    | Sum.inr (Sum.inr p) =>
        G8Ch23UnitAddCircleWedgePoint.lobe .minus p
  invFun
    | G8Ch23UnitAddCircleWedgePoint.crossing => Sum.inl ()
    | G8Ch23UnitAddCircleWedgePoint.lobe .plus p =>
        Sum.inr (Sum.inl p)
    | G8Ch23UnitAddCircleWedgePoint.lobe .minus p =>
        Sum.inr (Sum.inr p)
  left_inv := by
    intro x
    cases x with
    | inl u =>
        cases u
        rfl
    | inr y =>
        cases y with
        | inl p => rfl
        | inr p => rfl
  right_inv := by
    intro x
    cases x with
    | crossing => rfl
    | lobe s p =>
        cases s <;> rfl

@[simp] theorem g8Ch23UnitAddCircleRawCompactWedgeModelEquiv_crossing :
    g8Ch23UnitAddCircleRawCompactWedgeModelEquiv
      G8Ch23UnitAddCircleRawCompactWedgeModel.crossing =
        G8Ch23UnitAddCircleWedgePoint.crossing :=
  rfl

@[simp] theorem g8Ch23UnitAddCircleRawCompactWedgeModelEquiv_plusLobe
    (p : UnitAddCircle) :
    g8Ch23UnitAddCircleRawCompactWedgeModelEquiv
      (G8Ch23UnitAddCircleRawCompactWedgeModel.plusLobe p) =
        G8Ch23UnitAddCircleWedgePoint.lobe .plus p :=
  rfl

@[simp] theorem g8Ch23UnitAddCircleRawCompactWedgeModelEquiv_minusLobe
    (p : UnitAddCircle) :
    g8Ch23UnitAddCircleRawCompactWedgeModelEquiv
      (G8Ch23UnitAddCircleRawCompactWedgeModel.minusLobe p) =
        G8Ch23UnitAddCircleWedgePoint.lobe .minus p :=
  rfl

@[simp] theorem g8Ch23UnitAddCircleRawCompactWedgeModelEquiv_lobe
    (s : LemniscateSector) (p : UnitAddCircle) :
    g8Ch23UnitAddCircleRawCompactWedgeModelEquiv
      (G8Ch23UnitAddCircleRawCompactWedgeModel.lobe s p) =
        G8Ch23UnitAddCircleWedgePoint.lobe s p := by
  cases s <;> rfl

/-- The raw compact model sends each lobe basepoint into the crossing class of
    the quotient relation. -/
theorem g8Ch23UnitAddCircleRawCompactWedgeModelEquiv_lobeBase_inCrossingClass
    (s : LemniscateSector) :
    G8Ch23UnitAddCircleWedgePoint.InCrossingClass
      (g8Ch23UnitAddCircleRawCompactWedgeModelEquiv
        (G8Ch23UnitAddCircleRawCompactWedgeModel.lobe s
          G8Ch23UnitAddCircleWedgePoint.basepoint)) := by
  cases s <;> rfl

-- ============================================================
-- THEOREM-BACKED SOURCE PACKAGE
-- ============================================================

/-- Closed raw compact two-lobe source underneath the concrete quotient graph.

This is not the full compact metric graph target: it proves that the pre-quotient
two-lobe Ch.23 carrier is a finite compact disjoint union and that it matches
the raw quotient presentation exactly. -/
structure G8BookIIICh23UnitAddCircleRawCompactWedgeModelSource where
  loops : G8BookIIICh23TwoLobeLoopConstructor
  loopTarget : G8BookIIICh23TwoLobeLoopConstructorTarget
  rawTopology : TopologicalSpace G8Ch23UnitAddCircleRawCompactWedgeModel
  rawCompact :
    @CompactSpace G8Ch23UnitAddCircleRawCompactWedgeModel rawTopology
  rawEquiv :
    G8Ch23UnitAddCircleRawCompactWedgeModel ≃
      G8Ch23UnitAddCircleWedgePoint
  crossing_matches :
    rawEquiv G8Ch23UnitAddCircleRawCompactWedgeModel.crossing =
      G8Ch23UnitAddCircleWedgePoint.crossing
  plusLobe_matches :
    ∀ p : UnitAddCircle,
      rawEquiv (G8Ch23UnitAddCircleRawCompactWedgeModel.plusLobe p) =
        G8Ch23UnitAddCircleWedgePoint.lobe .plus p
  minusLobe_matches :
    ∀ p : UnitAddCircle,
      rawEquiv (G8Ch23UnitAddCircleRawCompactWedgeModel.minusLobe p) =
        G8Ch23UnitAddCircleWedgePoint.lobe .minus p
  lobeBase_inCrossingClass :
    ∀ s : LemniscateSector,
      G8Ch23UnitAddCircleWedgePoint.InCrossingClass
        (rawEquiv
          (G8Ch23UnitAddCircleRawCompactWedgeModel.lobe s
            G8Ch23UnitAddCircleWedgePoint.basepoint))
  rawCompactFromFiniteTwoCircleSum : Prop
  rawCompactFromFiniteTwoCircleSumEvidence :
    rawCompactFromFiniteTwoCircleSum
  rawModelMatchesQuotientPresentation : Prop
  rawModelMatchesQuotientPresentationEvidence :
    rawModelMatchesQuotientPresentation
  status : SpineStatus := .conditional_interface

/-- The raw compact two-lobe source is theorem-backed by `UnitAddCircle`
    compactness and finite sum compactness. -/
noncomputable def g8BookIIICh23UnitAddCircleRawCompactWedgeModelSource :
    G8BookIIICh23UnitAddCircleRawCompactWedgeModelSource where
  loops :=
    g8BookIIICh23TwoLobeLoopConstructor_unitAddCircle
  loopTarget :=
    g8BookIIICh23TwoLobeLoopConstructorTarget_unitAddCircle
  rawTopology :=
    G8Ch23UnitAddCircleRawCompactWedgeModel.topology
  rawCompact :=
    G8Ch23UnitAddCircleRawCompactWedgeModel.compactSpace
  rawEquiv :=
    g8Ch23UnitAddCircleRawCompactWedgeModelEquiv
  crossing_matches :=
    g8Ch23UnitAddCircleRawCompactWedgeModelEquiv_crossing
  plusLobe_matches :=
    g8Ch23UnitAddCircleRawCompactWedgeModelEquiv_plusLobe
  minusLobe_matches :=
    g8Ch23UnitAddCircleRawCompactWedgeModelEquiv_minusLobe
  lobeBase_inCrossingClass :=
    g8Ch23UnitAddCircleRawCompactWedgeModelEquiv_lobeBase_inCrossingClass
  rawCompactFromFiniteTwoCircleSum :=
    CompactSpace G8Ch23UnitAddCircleRawCompactWedgeModel ∧
      CompactSpace UnitAddCircle
  rawCompactFromFiniteTwoCircleSumEvidence :=
    ⟨inferInstance, inferInstance⟩
  rawModelMatchesQuotientPresentation :=
    Nonempty (G8Ch23UnitAddCircleRawCompactWedgeModel ≃
      G8Ch23UnitAddCircleWedgePoint)
  rawModelMatchesQuotientPresentationEvidence :=
    ⟨g8Ch23UnitAddCircleRawCompactWedgeModelEquiv⟩
  status := .conditional_interface

/-- Target for the theorem-backed raw compact wedge model. -/
def G8BookIIICh23UnitAddCircleRawCompactWedgeModelTarget : Prop :=
  Nonempty G8BookIIICh23UnitAddCircleRawCompactWedgeModelSource

/-- The raw compact wedge model target is closed. -/
theorem g8BookIIICh23UnitAddCircleRawCompactWedgeModel_closed :
    G8BookIIICh23UnitAddCircleRawCompactWedgeModelTarget :=
  ⟨g8BookIIICh23UnitAddCircleRawCompactWedgeModelSource⟩

/-- The raw compact wedge model is an exact prerequisite for the full concrete
    compact metric graph target, but does not by itself supply the quotient
    topology or shortest-path metric. -/
structure G8BookIIICh23RawCompactWedgeModelWithoutConcreteMetricGraph where
  raw : G8BookIIICh23UnitAddCircleRawCompactWedgeModelSource
  noConcreteCompactMetricGraph :
    ¬ G8BookIIICh23ConcreteCompactMetricGraphTarget

/-- Absence of quotient topology/metric evidence refutes only the full concrete
    graph target, not the raw compact two-lobe model. -/
theorem
    G8BookIIICh23RawCompactWedgeModelWithoutConcreteMetricGraph.refutesConcreteTarget
    (gap : G8BookIIICh23RawCompactWedgeModelWithoutConcreteMetricGraph) :
    ¬ G8BookIIICh23ConcreteCompactMetricGraphTarget :=
  gap.noConcreteCompactMetricGraph

/-- A source whose raw equivalence fails to hit the explicit crossing point is
    not the canonical Ch.23 raw compact model. -/
structure G8BookIIICh23WrongRawCompactCrossingMatch
    (source : G8BookIIICh23UnitAddCircleRawCompactWedgeModelSource) where
  noCrossingMatch :
    source.rawEquiv G8Ch23UnitAddCircleRawCompactWedgeModel.crossing ≠
      G8Ch23UnitAddCircleWedgePoint.crossing

/-- The raw compact source carries exact crossing alignment. -/
theorem G8BookIIICh23WrongRawCompactCrossingMatch.refutesSource
    {source : G8BookIIICh23UnitAddCircleRawCompactWedgeModelSource}
    (gap : G8BookIIICh23WrongRawCompactCrossingMatch source) :
    False :=
  gap.noCrossingMatch source.crossing_matches

end Tau.BookIII.Bridge
