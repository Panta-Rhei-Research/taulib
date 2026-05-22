import TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleCauchyParametrizedAngleSource
import TauLib.BookI.Boundary.Bridge.TauRealQRealBridge

/-!
# TauLib.BookIII.Bridge.G8BookIIICh23UnitAddCircleRealIcoCauchyAngleReadout

Real half-open period readout for the Ch.23 unit-additive-circle bridge.

The previous Cauchy-parametrized source names the exact tau-native inverse
problem.  This module closes the Mathlib side of that problem: every
`UnitAddCircle` point has a canonical real representative in `[0,1)` via
`AddCircle.equivIco`, and the basepoint reads as `0`.

The remaining Tau-native work is then split into two proof-carrying pieces:

* a controlled lift from real `[0,1)` periods to bounded Cauchy tau angles;
* a tau-cis soundness/inverse law showing that this lift really presents the
  Cauchy-parametrized tau-circle lobe.

No final-spine, RH, O3, determinant-transfer, or accepted-realization machinery
enters this A1.1 angle-period corridor.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.Boundary

-- ============================================================
-- REAL HALF-OPEN PERIOD READOUT
-- ============================================================

/-- The canonical real half-open interval used for the unit additive circle. -/
abbrev G8BookIIICh23UnitRealIco : Type :=
  { x : ℝ // x ∈ Set.Ico (0 : ℝ) ((0 : ℝ) + 1) }

/-- The distinguished zero representative in the canonical half-open interval. -/
def g8BookIIICh23UnitRealIcoZero : G8BookIIICh23UnitRealIco :=
  ⟨0, by
    constructor <;> norm_num⟩

/-- Mathlib's theorem-backed canonical period representative of a
    `UnitAddCircle` point in `[0,1)`. -/
noncomputable def g8BookIIICh23UnitAddCircleRealIcoAngle
    (p : UnitAddCircle) : G8BookIIICh23UnitRealIco :=
  AddCircle.equivIco (1 : ℝ) (0 : ℝ) p

/-- The real period readout really lands in `[0,1)`. -/
theorem g8BookIIICh23UnitAddCircleRealIcoAngle_mem
    (p : UnitAddCircle) :
    (g8BookIIICh23UnitAddCircleRealIcoAngle p).1 ∈
      Set.Ico (0 : ℝ) 1 :=
  by
    simpa using
      (g8BookIIICh23UnitAddCircleRealIcoAngle p).2

/-- The real period readout is inverse to the quotient map. -/
theorem g8BookIIICh23UnitAddCircleRealIcoAngle_symm_apply
    (p : UnitAddCircle) :
    (AddCircle.equivIco (1 : ℝ) (0 : ℝ)).symm
        (g8BookIIICh23UnitAddCircleRealIcoAngle p) =
      p :=
  (AddCircle.equivIco (1 : ℝ) (0 : ℝ)).symm_apply_apply p

/-- The basepoint has canonical real period `0`. -/
theorem g8BookIIICh23UnitAddCircleRealIcoAngle_basepoint :
    g8BookIIICh23UnitAddCircleRealIcoAngle
        G8Ch23UnitAddCircleWedgePoint.basepoint =
      g8BookIIICh23UnitRealIcoZero := by
  dsimp [g8BookIIICh23UnitAddCircleRealIcoAngle,
    g8BookIIICh23UnitRealIcoZero,
    G8Ch23UnitAddCircleWedgePoint.basepoint]
  have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) ((0 : ℝ) + (1 : ℝ)) := by
    constructor <;> norm_num
  simpa using
    (AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ))
      (x := (0 : ℝ)) h0)

-- ============================================================
-- CAUCHY TAU-REAL QUOTIENT READOUT FOR BOUNDED ANGLES
-- ============================================================

/-- The quotient real carried by a bounded Cauchy tau angle. -/
noncomputable def G8BookIIICh23CauchyBoundedAngle.toTauRealQ
    (a : BoundedTauAngle)
    (ha : BoundedTauAngle.IsCauchy a) : TauRealQ :=
  CauchyTauReal.toQ ⟨a.angle, ha⟩

/-- Exact real agreement between a bounded Cauchy tau angle and an orthodox
    real period. -/
def G8BookIIICh23CauchyBoundedAngleRepresentsReal
    (a : BoundedTauAngle)
    (ha : BoundedTauAngle.IsCauchy a)
    (x : ℝ) : Prop :=
  tauRealQRingEquivReal
      (G8BookIIICh23CauchyBoundedAngle.toTauRealQ a ha) =
    x

/-- A controlled lift from real `[0,1)` periods to bounded Cauchy tau angles.

This is the first remaining tau-native payload after the additive-circle
period readout is closed.  The lift must carry both pointwise boundedness
(`BoundedTauAngle`) and Cauchy convergence, and it must agree with the real
period through the established `TauRealQ ≃ ℝ` bridge. -/
structure G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource where
  toBoundedAngle : G8BookIIICh23UnitRealIco → BoundedTauAngle
  toBoundedAngle_cauchy :
    ∀ x : G8BookIIICh23UnitRealIco,
      BoundedTauAngle.IsCauchy (toBoundedAngle x)
  representsReal :
    ∀ x : G8BookIIICh23UnitRealIco,
      G8BookIIICh23CauchyBoundedAngleRepresentsReal
        (toBoundedAngle x)
        (toBoundedAngle_cauchy x)
        x.1
  basepoint_preserving :
    toBoundedAngle g8BookIIICh23UnitRealIcoZero =
      BoundedTauAngle.zero
  boundedLiftConstruction : Prop
  boundedLiftConstructionEvidence : boundedLiftConstruction
  quotientRealAgreement : Prop
  quotientRealAgreementEvidence : quotientRealAgreement
  status : SpineStatus := .conditional_interface

/-- Target form of the controlled real-Ico to bounded-Cauchy-tau-angle lift. -/
def G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftTarget : Prop :=
  Nonempty G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource

namespace G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource

/-- A lift source gives a Cauchy tau angle for every additive-circle point by
    composing with the theorem-backed real `[0,1)` readout. -/
noncomputable def toBoundedAngleOfUnitAddCircle
    (source : G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource)
    (p : UnitAddCircle) : BoundedTauAngle :=
  source.toBoundedAngle (g8BookIIICh23UnitAddCircleRealIcoAngle p)

/-- The composed additive-circle angle is Cauchy. -/
theorem toBoundedAngleOfUnitAddCircle_cauchy
    (source : G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource)
    (p : UnitAddCircle) :
    BoundedTauAngle.IsCauchy
      (source.toBoundedAngleOfUnitAddCircle p) :=
  source.toBoundedAngle_cauchy
    (g8BookIIICh23UnitAddCircleRealIcoAngle p)

/-- The composed additive-circle angle has the exact canonical real period. -/
theorem toBoundedAngleOfUnitAddCircle_representsReal
    (source : G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource)
    (p : UnitAddCircle) :
    G8BookIIICh23CauchyBoundedAngleRepresentsReal
      (source.toBoundedAngleOfUnitAddCircle p)
      (source.toBoundedAngleOfUnitAddCircle_cauchy p)
      (g8BookIIICh23UnitAddCircleRealIcoAngle p).1 :=
  source.representsReal
    (g8BookIIICh23UnitAddCircleRealIcoAngle p)

/-- The lift preserves the additive-circle basepoint. -/
theorem toBoundedAngleOfUnitAddCircle_basepoint
    (source : G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource) :
    source.toBoundedAngleOfUnitAddCircle
        G8Ch23UnitAddCircleWedgePoint.basepoint =
      BoundedTauAngle.zero := by
  dsimp [toBoundedAngleOfUnitAddCircle]
  rw [g8BookIIICh23UnitAddCircleRealIcoAngle_basepoint]
  exact source.basepoint_preserving

end G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource

-- ============================================================
-- TAU-CIS PERIOD SOUNDNESS
-- ============================================================

/-- Soundness/inverse-law source for the lifted Cauchy tau-cis image.

This is the second remaining tau-native payload.  It states that the real-Ico
lift, after applying `TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle`,
is exactly inverse to the desired period map on the Cauchy-parametrized lobe.
-/
structure G8BookIIICh23CauchyTauCirclePeriodSoundnessSource
    (lift : G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource) where
  fromCauchyParametrized :
    TauCircleCauchyParametrizedCanonicalPoint → UnitAddCircle
  left_inv :
    ∀ p : UnitAddCircle,
      fromCauchyParametrized
          (TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
            (lift.toBoundedAngleOfUnitAddCircle p)
            (lift.toBoundedAngleOfUnitAddCircle_cauchy p)) =
        p
  right_inv :
    ∀ p : TauCircleCauchyParametrizedCanonicalPoint,
      TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
          (lift.toBoundedAngleOfUnitAddCircle
            (fromCauchyParametrized p))
          (lift.toBoundedAngleOfUnitAddCircle_cauchy
            (fromCauchyParametrized p)) =
        p
  tauCisPeriodSoundness : Prop
  tauCisPeriodSoundnessEvidence : tauCisPeriodSoundness
  periodInjectivity : Prop
  periodInjectivityEvidence : periodInjectivity
  periodSurjectivity : Prop
  periodSurjectivityEvidence : periodSurjectivity
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

/-- Target form of the tau-cis period soundness source for a fixed lift. -/
def G8BookIIICh23CauchyTauCirclePeriodSoundnessTarget
    (lift : G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource) :
    Prop :=
  Nonempty (G8BookIIICh23CauchyTauCirclePeriodSoundnessSource lift)

namespace G8BookIIICh23CauchyTauCirclePeriodSoundnessSource

/-- A controlled real-Ico lift plus tau-cis period soundness constructs the
    Cauchy angle-period source. -/
noncomputable def toCauchyAnglePeriodSource
    {lift : G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource}
    (sound :
      G8BookIIICh23CauchyTauCirclePeriodSoundnessSource lift) :
    G8BookIIICh23UnitAddCircleCauchyAnglePeriodSource where
  toBoundedAngle := lift.toBoundedAngleOfUnitAddCircle
  toBoundedAngle_cauchy :=
    lift.toBoundedAngleOfUnitAddCircle_cauchy
  fromCauchyParametrized := sound.fromCauchyParametrized
  left_inv := sound.left_inv
  right_inv := sound.right_inv
  basepoint_angle_preserving :=
    lift.toBoundedAngleOfUnitAddCircle_basepoint
  lobeTopologyAgreement := sound.lobeTopologyAgreement
  lobeTopologyAgreementEvidence := sound.lobeTopologyAgreementEvidence
  lobeMetricAgreement := sound.lobeMetricAgreement
  lobeMetricAgreementEvidence := sound.lobeMetricAgreementEvidence
  lobeCompactnessAgreement := sound.lobeCompactnessAgreement
  lobeCompactnessAgreementEvidence :=
    sound.lobeCompactnessAgreementEvidence
  anglePeriodBridge := sound.anglePeriodBridge
  anglePeriodBridgeEvidence := sound.anglePeriodBridgeEvidence
  cauchyParametrizedComplete := sound.cauchyParametrizedComplete
  cauchyParametrizedCompleteEvidence :=
    sound.cauchyParametrizedCompleteEvidence
  status := sound.status

end G8BookIIICh23CauchyTauCirclePeriodSoundnessSource

/-- Combined construction source for the real-Ico lift and tau-cis soundness
    needed by the Cauchy angle-period source. -/
structure G8BookIIICh23UnitAddCircleRealIcoCauchyAnglePeriodConstructionSource where
  lift : G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource
  soundness : G8BookIIICh23CauchyTauCirclePeriodSoundnessSource lift
  realIcoReadoutClosed : Prop
  realIcoReadoutClosedEvidence : realIcoReadoutClosed
  tauNativeLiftClosed : Prop
  tauNativeLiftClosedEvidence : tauNativeLiftClosed
  tauCisSoundnessClosed : Prop
  tauCisSoundnessClosedEvidence : tauCisSoundnessClosed
  status : SpineStatus := .conditional_interface

namespace G8BookIIICh23UnitAddCircleRealIcoCauchyAnglePeriodConstructionSource

/-- The combined construction source supplies the Cauchy angle-period source. -/
noncomputable def toCauchyAnglePeriodSource
    (source :
      G8BookIIICh23UnitAddCircleRealIcoCauchyAnglePeriodConstructionSource) :
    G8BookIIICh23UnitAddCircleCauchyAnglePeriodSource :=
  source.soundness.toCauchyAnglePeriodSource

end G8BookIIICh23UnitAddCircleRealIcoCauchyAnglePeriodConstructionSource

/-- Target form of the combined real-Ico/Cauchy angle-period construction. -/
def G8BookIIICh23UnitAddCircleRealIcoCauchyAnglePeriodConstructionTarget :
    Prop :=
  Nonempty
    G8BookIIICh23UnitAddCircleRealIcoCauchyAnglePeriodConstructionSource

/-- The combined construction target discharges the previous Cauchy
    angle-period source target. -/
theorem
    g8BookIIICh23UnitAddCircleRealIcoCauchyAnglePeriodConstructionTarget_toCauchyTarget
    (target :
      G8BookIIICh23UnitAddCircleRealIcoCauchyAnglePeriodConstructionTarget) :
    G8BookIIICh23UnitAddCircleCauchyAnglePeriodSourceTarget := by
  rcases target with ⟨source⟩
  exact ⟨source.toCauchyAnglePeriodSource⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Falsifier surface: a candidate lift that fails real agreement cannot
    instantiate the controlled lift source. -/
structure G8BookIIICh23RealIcoLiftRealAgreementFailure
    (candidate : G8BookIIICh23UnitRealIco → BoundedTauAngle)
    (candidateCauchy :
      ∀ x : G8BookIIICh23UnitRealIco,
        BoundedTauAngle.IsCauchy (candidate x)) where
  point : G8BookIIICh23UnitRealIco
  mismatch :
    ¬ G8BookIIICh23CauchyBoundedAngleRepresentsReal
        (candidate point)
        (candidateCauchy point)
        point.1

/-- Real-agreement failure blocks the corresponding `representsReal` field. -/
theorem G8BookIIICh23RealIcoLiftRealAgreementFailure.refutesRepresentsReal
    {candidate : G8BookIIICh23UnitRealIco → BoundedTauAngle}
    {candidateCauchy :
      ∀ x : G8BookIIICh23UnitRealIco,
        BoundedTauAngle.IsCauchy (candidate x)}
    (gap :
      G8BookIIICh23RealIcoLiftRealAgreementFailure
        candidate candidateCauchy) :
    ¬ ∀ x : G8BookIIICh23UnitRealIco,
      G8BookIIICh23CauchyBoundedAngleRepresentsReal
        (candidate x)
        (candidateCauchy x)
        x.1 := by
  intro h
  exact gap.mismatch (h gap.point)

/-- Falsifier surface: inverse-law failure blocks tau-cis period soundness. -/
structure G8BookIIICh23CauchyTauCircleInverseLawFailure
    (lift : G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource)
    (fromCauchyParametrized :
      TauCircleCauchyParametrizedCanonicalPoint → UnitAddCircle) where
  point : UnitAddCircle
  leftMismatch :
    fromCauchyParametrized
        (TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
          (lift.toBoundedAngleOfUnitAddCircle point)
          (lift.toBoundedAngleOfUnitAddCircle_cauchy point)) ≠
      point

/-- A failed left inverse blocks the corresponding soundness field. -/
theorem G8BookIIICh23CauchyTauCircleInverseLawFailure.refutesLeftInv
    {lift : G8BookIIICh23RealIcoCauchyBoundedTauAngleLiftSource}
    {fromCauchyParametrized :
      TauCircleCauchyParametrizedCanonicalPoint → UnitAddCircle}
    (gap :
      G8BookIIICh23CauchyTauCircleInverseLawFailure
        lift fromCauchyParametrized) :
    ¬ ∀ p : UnitAddCircle,
      fromCauchyParametrized
          (TauCircleCauchyParametrizedCanonicalPoint.ofBoundedAngle
            (lift.toBoundedAngleOfUnitAddCircle p)
            (lift.toBoundedAngleOfUnitAddCircle_cauchy p)) =
        p := by
  intro h
  exact gap.leftMismatch (h gap.point)

end Tau.BookIII.Bridge
