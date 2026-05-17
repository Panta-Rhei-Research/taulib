import TauLib.BookI.Boundary.TauRealSinCos

/-!
# TauLib.BookIII.Bridge.TauCircleParam

Experimental G5 spine: τ-native circle parameterization.

This module creates the receiving interface for the completed τ-native
trigonometric stack.  Circle witnesses are built from
`TauComplex.cisTauReal`, whose addition, conjugation, and Pythagorean
unit-magnitude identities are proved in Book I.  Closure of bounded angle sums
is still recorded as a G5 obligation rather than smuggled in as an unsafe
claim.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.Boundary Tau.Denotation

/-- A τ-real angle whose approximants remain inside the bounded interval needed
    by the current `cisTauReal` addition and magnitude identities. -/
structure BoundedTauAngle where
  angle : TauReal
  bounded_one : ∀ n, (angle.approx n).abs.toRat ≤ 1

namespace BoundedTauAngle

/-- The zero τ-angle. -/
def zero : BoundedTauAngle where
  angle := TauReal.zero
  bounded_one := by
    intro n
    change (TauRat.abs TauRat.zero).toRat ≤ 1
    rw [TauRat.toRat_abs, toRat_zero, abs_zero]
    norm_num

/-- Negation preserves the bounded-angle predicate. -/
def neg (x : BoundedTauAngle) : BoundedTauAngle where
  angle := TauReal.negate x.angle
  bounded_one := by
    intro n
    exact TauReal.negate_approx_abs_toRat_le_one x.angle x.bounded_one n

end BoundedTauAngle

/-- Source-status labels for the experimental circle parameterization layer. -/
inductive TauCircleParamStatus where
  | tauNativeTrigInterface
  | scaffoldObligation
  | receivingBridge
  deriving Repr, DecidableEq

/-- Unit-magnitude predicate for a τ-complex point.  This is the exact
    Pythagorean surface that the future `cisTauReal_magSq_equiv_one` theorem
    should discharge. -/
def TauCircleUnitMagnitude (z : TauComplex) : Prop :=
  TauReal.equiv
    (TauReal.add (TauReal.mul z.re z.re) (TauReal.mul z.im z.im))
    TauReal.one

/-- τ-native rational-angle circle parameterization.  This is the branch-local
    `cis` surface we can already build without importing Mathlib trigonometry:
    `exp(i·a)` using TauLib's constructive exponential and pure-imaginary lift. -/
def cisTauRat (a : TauRat) : TauComplex :=
  TauComplex.exp (TauComplex.pureIm a)

/-- Euler real-part bridge for the rational τ-circle parameterization. -/
theorem cisTauRat_re_eq_cos (a : TauRat) (ha : |a.toRat| ≤ 1) :
    TauReal.equiv (cisTauRat a).re (TauReal.cos_of_rat a) :=
  TauComplex.exp_pureIm_re_eq_cos_target_proof a ha

/-- Euler imaginary-part bridge for the rational τ-circle parameterization. -/
theorem cisTauRat_im_eq_sin (a : TauRat) (ha : |a.toRat| ≤ 1) :
    TauReal.equiv (cisTauRat a).im (TauReal.sin_of_rat a) :=
  TauComplex.exp_pureIm_im_eq_sin_target_proof a ha

/-- A τ-native point on the unit circle, represented by a bounded τ-angle and a
    τ-complex value. -/
structure TauCirclePoint where
  param : BoundedTauAngle
  value : TauComplex
  unitMagnitude : TauCircleUnitMagnitude value
  sourceStatus : TauCircleParamStatus := .scaffoldObligation

namespace TauCirclePoint

/-- The base circle point at τ-angle zero. -/
def base : TauCirclePoint :=
  { param := BoundedTauAngle.zero
    value := TauComplex.cisTauReal TauReal.zero
    unitMagnitude := by
      exact TauComplex.cisTauReal_magSq_equiv_one
        TauReal.zero
        BoundedTauAngle.zero.bounded_one
    sourceStatus := .tauNativeTrigInterface }

/-- The τ-native unit-magnitude identity for a circle point. -/
theorem unit_magnitude (p : TauCirclePoint) :
    TauCircleUnitMagnitude p.value :=
  p.unitMagnitude

/-- The formal negated parameter circle point, implemented directly with the
    τ-native `cisTauReal` parameterization. -/
def neg (p : TauCirclePoint) : TauCirclePoint where
  param := BoundedTauAngle.neg p.param
  value := TauComplex.cisTauReal (TauReal.negate p.param.angle)
  unitMagnitude := by
    exact TauComplex.cisTauReal_magSq_equiv_one
      (TauReal.negate p.param.angle)
      (BoundedTauAngle.neg p.param).bounded_one
  sourceStatus := .tauNativeTrigInterface

/-- The τ-native conjugation/angle-negation identity for circle points. -/
theorem negate_equiv_conj (p : TauCirclePoint) :
    TauComplex.equiv
      (TauComplex.cisTauReal (TauReal.negate p.param.angle))
      (TauComplex.conj (TauComplex.cisTauReal p.param.angle)) :=
  TauComplex.cisTauReal_negate_equiv_conj p.param.angle

/-- The addition-law obligation for the τ-circle parameterization.  The current
    scaffold does not package angle-sum closure as a point; it records the exact
    replacement target for `cisTauReal_add`. -/
def AdditionLawObligation (p q : TauCirclePoint) : Prop :=
  ∃ r : TauCirclePoint, TauComplex.equiv r.value (TauComplex.mul p.value q.value)

/-- The bounded-angle addition law remains an explicit G5 obligation.  Book I
    proves `cisTauReal_add`; what is not automatic here is that the sum of two
    bounded circle parameters is again packaged as a bounded circle point on
    this carrier. -/
def cis_add_closure_obligation (p q : TauCirclePoint) : Prop :=
  AdditionLawObligation p q

end TauCirclePoint

/-- A rational-angle τ-circle point built from the actual τ-native exponential
    stack.  The remaining proof debt is only the packaging of boundedness and
    unit magnitude into the general `TauCirclePoint` carrier. -/
def TauCirclePoint.ofRat (a : TauRat) (_ha : |a.toRat| ≤ 1) : TauCirclePoint :=
  { param :=
      { angle := TauReal.fromTauRat a
        bounded_one := by
          intro n
          change (TauRat.abs a).toRat ≤ 1
          rw [TauRat.toRat_abs]
          exact _ha }
    value := TauComplex.cisTauReal (TauReal.fromTauRat a)
    unitMagnitude := by
      exact TauComplex.cisTauReal_magSq_equiv_one
        (TauReal.fromTauRat a)
        (fun n => by
          change (TauRat.abs a).toRat ≤ 1
          rw [TauRat.toRat_abs]
          exact _ha)
    sourceStatus := .tauNativeTrigInterface }

end Tau.BookIII.Bridge
