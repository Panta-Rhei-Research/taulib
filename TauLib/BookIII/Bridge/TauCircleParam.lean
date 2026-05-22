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

/-- Semantic equivalence for the current raw tau-circle presentation.

The raw carrier stores proof data and a source-status tag.  Those are
presentation data, not geometric circle data, so the canonical quotient keeps
only the tau-angle and tau-complex value up to the kernel equivalences already
used throughout Book I. -/
def CanonicalEquivalent (p q : TauCirclePoint) : Prop :=
  TauReal.equiv p.param.angle q.param.angle ∧
    TauComplex.equiv p.value q.value

/-- Canonical tau-circle equivalence is reflexive. -/
theorem canonicalEquivalent_refl (p : TauCirclePoint) :
    CanonicalEquivalent p p :=
  ⟨TauReal.equiv_refl p.param.angle, TauComplex.equiv_refl p.value⟩

/-- Canonical tau-circle equivalence is symmetric. -/
theorem canonicalEquivalent_symm {p q : TauCirclePoint}
    (h : CanonicalEquivalent p q) :
    CanonicalEquivalent q p :=
  ⟨TauReal.equiv_symm h.1, TauComplex.equiv_symm h.2⟩

/-- Canonical tau-circle equivalence is transitive. -/
theorem canonicalEquivalent_trans {p q r : TauCirclePoint}
    (hpq : CanonicalEquivalent p q)
    (hqr : CanonicalEquivalent q r) :
    CanonicalEquivalent p r :=
  ⟨TauReal.equiv_trans hpq.1 hqr.1,
    TauComplex.equiv_trans hpq.2 hqr.2⟩

/-- Setoid quotienting raw tau-circle presentations by their semantic
    parameter/value data and ignoring source-status and proof-field fibers. -/
def canonicalSetoid : Setoid TauCirclePoint where
  r := CanonicalEquivalent
  iseqv :=
    ⟨canonicalEquivalent_refl,
      fun h => canonicalEquivalent_symm h,
      fun hpq hqr => canonicalEquivalent_trans hpq hqr⟩

/-- The base circle point at τ-angle zero. -/
def base : TauCirclePoint :=
  { param := BoundedTauAngle.zero
    value := TauComplex.cisTauReal TauReal.zero
    unitMagnitude := by
      exact TauComplex.cisTauReal_magSq_equiv_one
        TauReal.zero
        BoundedTauAngle.zero.bounded_one
    sourceStatus := .tauNativeTrigInterface }

/-- The τ-native circle point represented by a bounded τ-angle via the
    theorem-backed `cisTauReal` unit-magnitude identity. -/
def ofBoundedAngle (a : BoundedTauAngle) : TauCirclePoint :=
  { param := a
    value := TauComplex.cisTauReal a.angle
    unitMagnitude := by
      exact TauComplex.cisTauReal_magSq_equiv_one a.angle a.bounded_one
    sourceStatus := .tauNativeTrigInterface }

@[simp] theorem ofBoundedAngle_param (a : BoundedTauAngle) :
    (ofBoundedAngle a).param = a :=
  rfl

@[simp] theorem ofBoundedAngle_value (a : BoundedTauAngle) :
    (ofBoundedAngle a).value = TauComplex.cisTauReal a.angle :=
  rfl

@[simp] theorem ofBoundedAngle_status (a : BoundedTauAngle) :
    (ofBoundedAngle a).sourceStatus =
      TauCircleParamStatus.tauNativeTrigInterface :=
  rfl

/-- The bounded-angle constructor at zero is semantically equivalent to the
    raw base presentation.  We state this semantically because the raw
    structure also stores proof fields. -/
theorem ofBoundedAngle_zero_canonicalEquivalent :
    CanonicalEquivalent (ofBoundedAngle BoundedTauAngle.zero) base :=
  ⟨TauReal.equiv_refl _, TauComplex.equiv_refl _⟩

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

/-- Canonical tau-circle point: the semantic quotient of raw
    `TauCirclePoint` presentations. -/
abbrev TauCircleCanonicalPoint : Type :=
  Quotient TauCirclePoint.canonicalSetoid

namespace TauCircleCanonicalPoint

/-- Project a raw tau-circle presentation to the canonical circle quotient. -/
def mk (p : TauCirclePoint) : TauCircleCanonicalPoint :=
  Quotient.mk TauCirclePoint.canonicalSetoid p

/-- The canonical base point. -/
def base : TauCircleCanonicalPoint :=
  mk TauCirclePoint.base

/-- The canonical tau-circle point represented by a bounded tau angle through
    the theorem-backed `cisTauReal` parameterization. -/
def ofBoundedAngle (a : BoundedTauAngle) : TauCircleCanonicalPoint :=
  mk (TauCirclePoint.ofBoundedAngle a)

@[simp] theorem ofBoundedAngle_zero :
    ofBoundedAngle BoundedTauAngle.zero = base :=
  Quotient.sound TauCirclePoint.ofBoundedAngle_zero_canonicalEquivalent

/-- Equivalent raw presentations define the same canonical point. -/
theorem sound {p q : TauCirclePoint}
    (h : TauCirclePoint.CanonicalEquivalent p q) :
    mk p = mk q :=
  Quotient.sound h

/-- Raw presentations with the same semantic angle and value project to the
    same canonical point, independently of status and proof fields. -/
theorem eq_of_param_value {p q : TauCirclePoint}
    (hParam : TauReal.equiv p.param.angle q.param.angle)
    (hValue : TauComplex.equiv p.value q.value) :
    mk p = mk q :=
  sound ⟨hParam, hValue⟩

/-- The raw base presentation maps to the canonical base point. -/
@[simp] theorem mk_base :
    mk TauCirclePoint.base = base :=
  rfl

/-- Every canonical tau-circle point has a raw representative whose status has
    been normalized to the tau-native trigonometric interface.

This theorem closes the source-status fiber exposed by the A1.1 reality check:
status is presentation data, so it can be normalized inside the quotient
without changing the canonical point. -/
theorem exists_tauNativeStatus_rep
    (c : TauCircleCanonicalPoint) :
    ∃ p : TauCirclePoint,
      p.sourceStatus = TauCircleParamStatus.tauNativeTrigInterface ∧
      TauCircleUnitMagnitude p.value ∧
      mk p = c := by
  refine Quotient.inductionOn c ?_
  intro q
  refine ⟨{ q with sourceStatus := TauCircleParamStatus.tauNativeTrigInterface },
    rfl, ?_, ?_⟩
  · exact q.unitMagnitude
  · exact eq_of_param_value
      (TauReal.equiv_refl _)
      (TauComplex.equiv_refl _)

end TauCircleCanonicalPoint

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
