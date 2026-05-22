import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleParametrizedCanonicalAngleSource

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleCauchyParametrizedAngleSource

Cauchy-parametrized angle source for the Ch.23 unit-additive-circle bridge.

The previous parametrized source isolates the tau-native `cisTauReal` image of
bounded tau angles.  The next inverse step needs one extra datum: the angle
representative must be Cauchy, so that future real/period readout bridges can
move between tau angles and the Mathlib additive circle without pretending that
an arbitrary bounded presentation already has a real quotient value.

This module keeps that boundary explicit.  It defines the Cauchy-parametrized
sub-lobe, proves the forgetful adapters into the existing parametrized source,
and names the exact completeness obligation needed to recover the wider
parametrized source.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CAUCHY-PARAMETRIZED CANONICAL TAU-CIRCLE POINTS
-- ============================================================

namespace BoundedTauAngle

/-- A bounded tau angle is Cauchy when its underlying tau-real representative
    is Cauchy.  This is the precise extra datum needed by the real quotient
    bridge. -/
def IsCauchy (a : BoundedTauAngle) : Prop :=
  a.angle.IsCauchy

end BoundedTauAngle

namespace TauCircleCanonicalPoint

/-- A canonical tau-circle point is Cauchy-parametrized when it is represented
    by a bounded tau angle whose underlying tau-real is Cauchy. -/
def IsCauchyParametrized (c : TauCircleCanonicalPoint) : Prop :=
  ∃ a : BoundedTauAngle,
    BoundedTauAngle.IsCauchy a ∧
      TauCircleCanonicalPoint.ofBoundedAngle a = c

/-- Cauchy-parametrized points are parametrized after forgetting the Cauchy
    witness. -/
theorem isParametrized_of_isCauchyParametrized
    {c : TauCircleCanonicalPoint}
    (h : IsCauchyParametrized c) :
    TauCircleCanonicalPoint.IsParametrized c := by
  rcases h with ⟨a, _haCauchy, ha⟩
  exact ⟨a, ha⟩

end TauCircleCanonicalPoint

/-- The Cauchy-parametrized canonical tau-circle lobe. -/
abbrev TauCircleCauchyParametrizedCanonicalPoint : Type :=
  { c : TauCircleCanonicalPoint //
    TauCircleCanonicalPoint.IsCauchyParametrized c }

namespace TauCircleCauchyParametrizedCanonicalPoint

/-- Forget the Cauchy representative and view the point in the parametrized
    canonical lobe. -/
def forget
    (p : TauCircleCauchyParametrizedCanonicalPoint) :
    TauCircleParametrizedCanonicalPoint :=
  ⟨p.1,
    TauCircleCanonicalPoint.isParametrized_of_isCauchyParametrized p.2⟩

/-- The Cauchy-parametrized canonical point associated to a bounded Cauchy tau
    angle. -/
def ofBoundedAngle
    (a : BoundedTauAngle)
    (ha : BoundedTauAngle.IsCauchy a) :
    TauCircleCauchyParametrizedCanonicalPoint :=
  ⟨TauCircleCanonicalPoint.ofBoundedAngle a, ⟨a, ha, rfl⟩⟩

@[simp] theorem forget_forget
    (p : TauCircleCauchyParametrizedCanonicalPoint) :
    p.forget.forget = p.1 :=
  rfl

@[simp] theorem forget_ofBoundedAngle
    (a : BoundedTauAngle)
    (ha : BoundedTauAngle.IsCauchy a) :
    (ofBoundedAngle a ha).forget =
      TauCircleParametrizedCanonicalPoint.ofBoundedAngle a := by
  apply TauCircleParametrizedCanonicalPoint.ext
  rfl

@[simp] theorem coe_ofBoundedAngle
    (a : BoundedTauAngle)
    (ha : BoundedTauAngle.IsCauchy a) :
    ((ofBoundedAngle a ha : TauCircleCauchyParametrizedCanonicalPoint) :
      TauCircleCanonicalPoint) =
      TauCircleCanonicalPoint.ofBoundedAngle a :=
  rfl

/-- Extensionality for Cauchy-parametrized canonical points. -/
theorem ext {p q : TauCircleCauchyParametrizedCanonicalPoint}
    (h : p.forget = q.forget) : p = q :=
  Subtype.ext (congrArg TauCircleParametrizedCanonicalPoint.forget h)

end TauCircleCauchyParametrizedCanonicalPoint

/-- Completeness of the parametrized lobe with respect to Cauchy
    representatives.

This is the exact remaining bridge needed before an inverse period map can be
defined on all parametrized canonical points. -/
def G8BookIIICh23TauCircleParametrizedCauchyComplete : Prop :=
  ∀ p : TauCircleParametrizedCanonicalPoint,
    TauCircleCanonicalPoint.IsCauchyParametrized p.forget

-- ============================================================
-- CAUCHY ANGLE-PERIOD SOURCE
-- ============================================================

/-- Exact period source from Mathlib's additive circle to the
    Cauchy-parametrized canonical tau-circle lobe.

The inverse is deliberately defined only on the Cauchy-parametrized lobe.  A
separate completeness theorem upgrades it to the previous parametrized source. -/
structure G8BookIIICh23UnitAddCircleCauchyAnglePeriodSource where
  toBoundedAngle : UnitAddCircle → BoundedTauAngle
  toBoundedAngle_cauchy :
    ∀ p : UnitAddCircle,
      BoundedTauAngle.IsCauchy (toBoundedAngle p)
  fromCauchyParametrized :
    TauCircleCauchyParametrizedCanonicalPoint → UnitAddCircle
  left_inv :
    ∀ p : UnitAddCircle,
      fromCauchyParametrized
          (TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
            (toBoundedAngle p)
            (toBoundedAngle_cauchy p)) =
        p
  right_inv :
    ∀ p : TauCircleCauchyParametrizedCanonicalPoint,
      TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
          (toBoundedAngle (fromCauchyParametrized p))
          (toBoundedAngle_cauchy (fromCauchyParametrized p)) =
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
  cauchyParametrizedComplete : Prop
  cauchyParametrizedCompleteEvidence :
    cauchyParametrizedComplete
  status : SpineStatus := .conditional_interface

namespace G8BookIIICh23UnitAddCircleCauchyAnglePeriodSource

/-- The Cauchy-parametrized canonical map induced by the bounded-angle readout. -/
def toCauchyParametrized
    (source :
      G8BookIIICh23UnitAddCircleCauchyAnglePeriodSource) :
    UnitAddCircle → TauCircleCauchyParametrizedCanonicalPoint :=
  fun p =>
    TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
      (source.toBoundedAngle p)
      (source.toBoundedAngle_cauchy p)

/-- The induced equivalence between `UnitAddCircle` and the
    Cauchy-parametrized canonical tau-circle lobe. -/
def toCauchyParametrizedEquiv
    (source :
      G8BookIIICh23UnitAddCircleCauchyAnglePeriodSource) :
    UnitAddCircle ≃ TauCircleCauchyParametrizedCanonicalPoint where
  toFun := source.toCauchyParametrized
  invFun := source.fromCauchyParametrized
  left_inv := source.left_inv
  right_inv := source.right_inv

/-- Forgetting the Cauchy witness gives the previous parametrized source once
    every parametrized point is known to have a Cauchy representative. -/
noncomputable def toParametrizedSource
    (source :
      G8BookIIICh23UnitAddCircleCauchyAnglePeriodSource)
    (complete :
      G8BookIIICh23TauCircleParametrizedCauchyComplete) :
    G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSource where
  toBoundedAngle := source.toBoundedAngle
  fromParametrized := fun p =>
    source.fromCauchyParametrized ⟨p.forget, complete p⟩
  left_inv := by
    intro p
    have hSubtype :
        (⟨(TauCircleParametrizedCanonicalPoint.ofBoundedAngle
              (source.toBoundedAngle p)).forget,
            complete
              (TauCircleParametrizedCanonicalPoint.ofBoundedAngle
                (source.toBoundedAngle p))⟩ :
          TauCircleCauchyParametrizedCanonicalPoint) =
          TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
            (source.toBoundedAngle p)
            (source.toBoundedAngle_cauchy p) :=
      Subtype.ext rfl
    rw [hSubtype]
    exact source.left_inv p
  right_inv := by
    intro p
    apply TauCircleParametrizedCanonicalPoint.ext
    have h :=
      source.right_inv
        (⟨p.forget, complete p⟩ :
          TauCircleCauchyParametrizedCanonicalPoint)
    exact congrArg
      (fun q : TauCircleCauchyParametrizedCanonicalPoint =>
        q.forget.forget) h
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
  parametrizedCanonicalComplete :=
    source.cauchyParametrizedComplete ∧
      G8BookIIICh23TauCircleParametrizedCauchyComplete
  parametrizedCanonicalCompleteEvidence :=
    ⟨source.cauchyParametrizedCompleteEvidence, complete⟩
  status := source.status

end G8BookIIICh23UnitAddCircleCauchyAnglePeriodSource

/-- Target form of the Cauchy angle-period source. -/
def G8BookIIICh23UnitAddCircleCauchyAnglePeriodSourceTarget :
    Prop :=
  Nonempty G8BookIIICh23UnitAddCircleCauchyAnglePeriodSource

/-- A Cauchy angle-period source plus Cauchy completeness is sufficient for the
    parametrized angle-period source target. -/
theorem
    g8BookIIICh23UnitAddCircleCauchyAnglePeriodSourceTarget_toParametrizedTarget
    (target :
      G8BookIIICh23UnitAddCircleCauchyAnglePeriodSourceTarget)
    (complete :
      G8BookIIICh23TauCircleParametrizedCauchyComplete) :
    G8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSourceTarget := by
  rcases target with ⟨source⟩
  exact ⟨source.toParametrizedSource complete⟩

/-- A Cauchy angle-period source, Cauchy completeness, and cis-image
    completeness are jointly sufficient for the full canonical angle-period
    constructor target. -/
theorem
    g8BookIIICh23UnitAddCircleCauchyAnglePeriodSourceTarget_toFullConstructor
    (target :
      G8BookIIICh23UnitAddCircleCauchyAnglePeriodSourceTarget)
    (cauchyComplete :
      G8BookIIICh23TauCircleParametrizedCauchyComplete)
    (cisComplete : G8BookIIICh23TauCircleCanonicalCisImageComplete) :
    G8BookIIICh23TauCircleCanonicalAnglePeriodConstructorTarget :=
  g8BookIIICh23UnitAddCircleParametrizedCanonicalAnglePeriodSourceTarget_toFullConstructor
    (g8BookIIICh23UnitAddCircleCauchyAnglePeriodSourceTarget_toParametrizedTarget
      target cauchyComplete)
    cisComplete

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Falsifier surface: a parametrized canonical point with no Cauchy
    representative refutes Cauchy completeness. -/
structure G8BookIIICh23ParametrizedPointWithoutCauchyRepresentative where
  point : TauCircleParametrizedCanonicalPoint
  noCauchy :
    ¬ TauCircleCanonicalPoint.IsCauchyParametrized point.forget

/-- A parametrized point without a Cauchy representative blocks the completeness
    theorem needed to upgrade the Cauchy source. -/
theorem
    G8BookIIICh23ParametrizedPointWithoutCauchyRepresentative.refutesCompleteness
    (gap :
      G8BookIIICh23ParametrizedPointWithoutCauchyRepresentative) :
    ¬ G8BookIIICh23TauCircleParametrizedCauchyComplete := by
  intro complete
  exact gap.noCauchy (complete gap.point)

/-- Falsifier surface: a bounded angle alone is not enough for the Cauchy
    inverse corridor. -/
structure G8BookIIICh23BoundedAngleWithoutCauchy where
  angle : BoundedTauAngle
  notCauchy : ¬ BoundedTauAngle.IsCauchy angle

/-- A non-Cauchy bounded angle cannot be used as a Cauchy-parametrized point
    representative through `ofBoundedAngle`. -/
theorem
    G8BookIIICh23BoundedAngleWithoutCauchy.refutesPointwiseCauchyWitness
    (gap : G8BookIIICh23BoundedAngleWithoutCauchy) :
    ¬ BoundedTauAngle.IsCauchy gap.angle :=
  gap.notCauchy

end Tau.BookIII.Bridge
