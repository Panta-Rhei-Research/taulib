import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleTauCircleCanonicalEquivalence

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleParametrizedCanonicalAngleSource

Parametrized canonical lobe source for the A1.1 tau-circle bridge.

The semantic quotient `TauCircleCanonicalPoint` is intentionally wider than
the tau-native `cisTauReal` image: a raw point stores an arbitrary unit
magnitude tau-complex value.  This module isolates the actual tau-native lobe
used by the Ch.23 angle bridge as the canonical image of bounded tau angles.

The source here is still proof-carrying: it asks for an exact period readout
`UnitAddCircle -> BoundedTauAngle` and inverse laws against the parametrized
canonical image.  It does not claim that every canonical tau-circle point is
already parametrized; that is a separate completeness theorem.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- PARAMETRIZED CANONICAL TAU-CIRCLE POINTS
-- ============================================================

namespace TauCircleCanonicalPoint

/-- A canonical tau-circle point is parametrized when it lies in the image of
    the theorem-backed bounded-angle `cisTauReal` constructor. -/
def IsParametrized (c : TauCircleCanonicalPoint) : Prop :=
  ∃ a : BoundedTauAngle, TauCircleCanonicalPoint.ofBoundedAngle a = c

end TauCircleCanonicalPoint

/-- The actual tau-native canonical lobe: canonical circle points that are
    represented by a bounded tau angle through `cisTauReal`. -/
abbrev TauCircleParametrizedCanonicalPoint : Type :=
  { c : TauCircleCanonicalPoint //
    TauCircleCanonicalPoint.IsParametrized c }

namespace TauCircleParametrizedCanonicalPoint

/-- Forget the parametrized-image proof and view a point in the wider
    canonical quotient. -/
def forget (p : TauCircleParametrizedCanonicalPoint) :
    TauCircleCanonicalPoint :=
  p.1

/-- The parametrized canonical point associated to a bounded tau angle. -/
def ofBoundedAngle
    (a : BoundedTauAngle) : TauCircleParametrizedCanonicalPoint :=
  ⟨TauCircleCanonicalPoint.ofBoundedAngle a, ⟨a, rfl⟩⟩

@[simp] theorem forget_ofBoundedAngle (a : BoundedTauAngle) :
    (ofBoundedAngle a).forget =
      TauCircleCanonicalPoint.ofBoundedAngle a :=
  rfl

@[simp] theorem coe_ofBoundedAngle (a : BoundedTauAngle) :
    ((ofBoundedAngle a : TauCircleParametrizedCanonicalPoint) :
      TauCircleCanonicalPoint) =
      TauCircleCanonicalPoint.ofBoundedAngle a :=
  rfl

/-- The parametrized canonical basepoint. -/
def base : TauCircleParametrizedCanonicalPoint :=
  ofBoundedAngle BoundedTauAngle.zero

@[simp] theorem ofBoundedAngle_zero :
    ofBoundedAngle BoundedTauAngle.zero = base :=
  rfl

@[simp] theorem forget_base :
    base.forget = TauCircleCanonicalPoint.base :=
  TauCircleCanonicalPoint.ofBoundedAngle_zero

@[simp] theorem coe_base :
    ((base : TauCircleParametrizedCanonicalPoint) :
      TauCircleCanonicalPoint) =
      TauCircleCanonicalPoint.base :=
  TauCircleCanonicalPoint.ofBoundedAngle_zero

/-- Extensionality for parametrized canonical points. -/
theorem ext {p q : TauCircleParametrizedCanonicalPoint}
    (h : p.forget = q.forget) : p = q :=
  Subtype.ext h

end TauCircleParametrizedCanonicalPoint

/-- Completeness of the canonical quotient with respect to the tau-native
    bounded-angle `cisTauReal` image.

This is deliberately separated from the parametrized source below.  The source
identifies `UnitAddCircle` with the actual parametrized lobe; this predicate is
the stronger statement that the wider canonical quotient has no extra
unit-magnitude value fibers beyond that lobe. -/
def G8BookIIICh23TauCircleCanonicalCisImageComplete : Prop :=
  ∀ c : TauCircleCanonicalPoint,
    TauCircleCanonicalPoint.IsParametrized c

-- ============================================================
-- PARAMETRIZED ANGLE-PERIOD SOURCE
-- ============================================================

/-- Exact period source from Mathlib's additive circle to the parametrized
    canonical tau-circle lobe.

The forward map is not an arbitrary canonical point map: it is explicitly a
bounded tau-angle readout followed by the theorem-backed `cisTauReal`
constructor. -/
structure
    G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSource where
  toBoundedAngle : UnitAddCircle → BoundedTauAngle
  fromParametrized :
    TauCircleParametrizedCanonicalPoint → UnitAddCircle
  left_inv :
    ∀ p : UnitAddCircle,
      fromParametrized
          (TauCircleParametrizedCanonicalPoint.ofBoundedAngle
            (toBoundedAngle p)) =
        p
  right_inv :
    ∀ p : TauCircleParametrizedCanonicalPoint,
      TauCircleParametrizedCanonicalPoint.ofBoundedAngle
          (toBoundedAngle (fromParametrized p)) =
        p
  basepoint_angle_preserving :
    toBoundedAngle G8Ch23UnitAddCircleWedgePoint.basepoint =
      BoundedTauAngle.zero
  lobeTopologyAgreement : Prop
  lobeTopologyAgreementEvidence : lobeTopologyAgreement
  lobeMetricAgreement : Prop
  lobeMetricAgreementEvidence : lobeMetricAgreement
  lobeCompactnessAgreement : Prop
  lobeCompactnessAgreementEvidence : lobeCompactnessAgreement
  anglePeriodBridge : Prop
  anglePeriodBridgeEvidence : anglePeriodBridge
  parametrizedCanonicalComplete : Prop
  parametrizedCanonicalCompleteEvidence :
    parametrizedCanonicalComplete
  status : SpineStatus := .conditional_interface

namespace G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSource

/-- The parametrized canonical map induced by the bounded-angle readout. -/
def toParametrized
    (source :
      G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSource) :
    UnitAddCircle → TauCircleParametrizedCanonicalPoint :=
  fun p =>
    TauCircleParametrizedCanonicalPoint.ofBoundedAngle
      (source.toBoundedAngle p)

/-- The induced equivalence between `UnitAddCircle` and the parametrized
    canonical tau-circle lobe. -/
def toParametrizedEquiv
    (source :
      G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSource) :
    UnitAddCircle ≃ TauCircleParametrizedCanonicalPoint where
  toFun := source.toParametrized
  invFun := source.fromParametrized
  left_inv := source.left_inv
  right_inv := source.right_inv

/-- The parametrized lobe equivalence preserves the distinguished basepoint. -/
theorem basepoint_preserving
    (source :
      G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSource) :
    source.toParametrized G8Ch23UnitAddCircleWedgePoint.basepoint =
      TauCircleParametrizedCanonicalPoint.base := by
  dsimp [toParametrized]
  rw [source.basepoint_angle_preserving]
  rfl

/-- The induced map to the wider canonical quotient. -/
def toCanonical
    (source :
      G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSource) :
    UnitAddCircle → TauCircleCanonicalPoint :=
  fun p => (source.toParametrized p).forget

/-- The induced canonical map preserves the distinguished basepoint. -/
theorem canonical_basepoint_preserving
    (source :
      G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSource) :
    source.toCanonical G8Ch23UnitAddCircleWedgePoint.basepoint =
      TauCircleCanonicalPoint.base := by
  dsimp [toCanonical]
  rw [source.basepoint_preserving]
  exact TauCircleParametrizedCanonicalPoint.forget_base

/-- If the wider canonical quotient is known to be exactly the `cisTauReal`
    image, then a parametrized source upgrades to the previous full canonical
    angle-period constructor. -/
noncomputable def toCanonicalAnglePeriodConstructor
    (source :
      G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSource)
    (complete : G8BookIIICh23TauCircleCanonicalCisImageComplete) :
    G8BookIIICh23TauCircleCanonicalAnglePeriodConstructor where
  toBoundedAngle := source.toBoundedAngle
  fromCanonical := fun c => source.fromParametrized ⟨c, complete c⟩
  left_inv := by
    intro p
    have hSubtype :
        (⟨TauCircleCanonicalPoint.ofBoundedAngle
              (source.toBoundedAngle p),
            complete
              (TauCircleCanonicalPoint.ofBoundedAngle
                (source.toBoundedAngle p))⟩ :
          TauCircleParametrizedCanonicalPoint) =
          TauCircleParametrizedCanonicalPoint.ofBoundedAngle
            (source.toBoundedAngle p) :=
      Subtype.ext rfl
    rw [hSubtype]
    exact source.left_inv p
  right_inv := by
    intro c
    exact congrArg TauCircleParametrizedCanonicalPoint.forget
      (source.right_inv ⟨c, complete c⟩)
  basepoint_angle_preserving := source.basepoint_angle_preserving
  lobeTopologyAgreement := source.lobeTopologyAgreement
  lobeTopologyAgreementEvidence := source.lobeTopologyAgreementEvidence
  lobeMetricAgreement := source.lobeMetricAgreement
  lobeMetricAgreementEvidence := source.lobeMetricAgreementEvidence
  lobeCompactnessAgreement := source.lobeCompactnessAgreement
  lobeCompactnessAgreementEvidence :=
    source.lobeCompactnessAgreementEvidence
  anglePeriodBridge := source.anglePeriodBridge
  anglePeriodBridgeEvidence := source.anglePeriodBridgeEvidence
  canonicalParametrizationComplete :=
    source.parametrizedCanonicalComplete ∧
      G8BookIIICh23TauCircleCanonicalCisImageComplete
  canonicalParametrizationCompleteEvidence :=
    ⟨source.parametrizedCanonicalCompleteEvidence, complete⟩
  status := source.status

end G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSource

/-- Target form of the parametrized canonical angle-period source. -/
def
    G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSourceTarget :
    Prop :=
  Nonempty
    G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSource

/-- A parametrized canonical angle-period source plus cis-image completeness is
    exactly sufficient for the full canonical angle-period constructor target. -/
theorem
    g8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSourceTarget_toFullConstructor
    (target :
      G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSourceTarget)
    (complete : G8BookIIICh23TauCircleCanonicalCisImageComplete) :
    G8BookIIICh23TauCircleCanonicalAnglePeriodConstructorTarget := by
  rcases target with ⟨source⟩
  exact ⟨source.toCanonicalAnglePeriodConstructor complete⟩

/-- A parametrized canonical angle-period source plus cis-image completeness
    supplies the full canonical lobe equivalence target. -/
theorem
    g8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSourceTarget_toFullLobeTarget
    (target :
      G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSourceTarget)
    (complete : G8BookIIICh23TauCircleCanonicalCisImageComplete) :
    G8BookIIICh23UnitAddCircleTauCircleCanonicalLobeEquivalenceTarget :=
  g8BookIIICh23TauCircleCanonicalAnglePeriodConstructorTarget_toLobeTarget
    (g8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSourceTarget_toFullConstructor
      target complete)

end Tau.BookIII.Bridge
