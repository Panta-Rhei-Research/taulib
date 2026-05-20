import TauLib.BookIII.Bridge.G8ActualXiOrthodoxCore

/-!
# TauLib.BookIII.Bridge.G8ActualXiZeroHeightAxisGuardCore

Low-level real-axis zero-height guard for Lane A.

This module contains only the orthodox `xi`/zeta nonvanishing interfaces and
the theorem-backed outside-zone reductions.  It deliberately does not import
the height-split, accepted-tower, final-spine, O3, divisor-transfer, or
completion-uniqueness layers.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex

-- ============================================================
-- REAL-AXIS NONVANISHING INTERFACES
-- ============================================================

/-- Zero-height actual `xi` carriers must already lie on the orthodox critical
    axis.  This is a receiving-side guard, not a spectral theorem. -/
def G8ActualXiZeroHeightAxisGuard : Prop :=
  ∀ z : OrthodoxXiZeroCarrier,
    z.toZero.point.im = 0 → ¬ OrthodoxXiCarrierOffCritical z

/-- Real-axis nonvanishing for the orthodox `xi` wrapper. -/
def G8OrthodoxXiRealAxisNonvanishing : Prop :=
  ∀ x : ℝ, orthodoxXi (x : ℂ) ≠ 0

/-- The residual zero-height target: nonvanishing on the real open interval
    between the pole-removed normalization points. -/
def G8OrthodoxXiOpenUnitIntervalNonvanishing : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 → orthodoxXi (x : ℂ) ≠ 0

/-- The corresponding narrow classical zeta target on the real open interval.
    This is the exact theorem needed by the eta lane below. -/
def G8RiemannZetaOpenUnitIntervalNonvanishing : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 → riemannZeta (x : ℂ) ≠ 0

/-- The theorem-backed outside-zone target. -/
def G8OrthodoxXiOutsideUnitIntervalNonvanishing : Prop :=
  ∀ x : ℝ, x ≤ 0 ∨ 1 ≤ x → orthodoxXi (x : ℂ) ≠ 0

/-- The zero-height guard discharge carries exactly the residual real-axis
    theorem not supplied by the outside-zone argument. -/
structure G8ActualXiZeroHeightAxisGuardDischarge where
  openUnitNonvanishing : G8OrthodoxXiOpenUnitIntervalNonvanishing

-- ============================================================
-- XI AND COMPLETED-ZETA ALGEBRA
-- ============================================================

/-- Away from `0` and `1`, the pole-removed `xi` wrapper is the usual
    completed-zeta product. -/
theorem orthodoxXi_eq_completedRiemannZeta_of_ne_zero_ne_one
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    orthodoxXi s =
      (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s) := by
  have hOneSub : 1 - s ≠ 0 := by
    intro h
    exact hs1 (sub_eq_zero.mp h).symm
  have hSubOne : s - 1 ≠ 0 := by
    intro h
    exact hs1 (sub_eq_zero.mp h)
  unfold orthodoxXi
  rw [completedRiemannZeta_eq]
  field_simp [hs0, hOneSub, hSubOne]
  ring

/-- Nonvanishing of zeta forces nonvanishing of the completed zeta away from
    the pole-removed point `0`. -/
theorem completedRiemannZeta_ne_zero_of_riemannZeta_ne_zero
    {s : ℂ} (hs0 : s ≠ 0) (hzeta : riemannZeta s ≠ 0) :
    completedRiemannZeta s ≠ 0 := by
  intro hCompleted
  have hZetaEq := riemannZeta_def_of_ne_zero hs0
  rw [hCompleted, zero_div] at hZetaEq
  exact hzeta hZetaEq

/-- Completed-zeta nonvanishing gives `xi` nonvanishing away from `0` and `1`. -/
theorem orthodoxXi_ne_zero_of_completedRiemannZeta_ne_zero
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hCompleted : completedRiemannZeta s ≠ 0) :
    orthodoxXi s ≠ 0 := by
  rw [orthodoxXi_eq_completedRiemannZeta_of_ne_zero_ne_one hs0 hs1]
  exact mul_ne_zero (by norm_num)
    (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hCompleted)

/-- Zeta nonvanishing gives `xi` nonvanishing away from the normalization
    points `0` and `1`. -/
theorem orthodoxXi_ne_zero_of_riemannZeta_ne_zero
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0) :
    orthodoxXi s ≠ 0 :=
  orthodoxXi_ne_zero_of_completedRiemannZeta_ne_zero hs0 hs1
    (completedRiemannZeta_ne_zero_of_riemannZeta_ne_zero hs0 hzeta)

/-- `xi` does not vanish in the strict right half-plane. -/
theorem orthodoxXi_ne_zero_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    orthodoxXi s ≠ 0 := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  exact orthodoxXi_ne_zero_of_completedRiemannZeta_ne_zero hs0 hs1
    (completedRiemannZeta_ne_zero_of_riemannZeta_ne_zero hs0
      (riemannZeta_ne_zero_of_one_le_re (le_of_lt hs)))

-- ============================================================
-- THEOREM-BACKED OUTSIDE-ZONE NONVANISHING
-- ============================================================

/-- The normalization gives a nonzero value at `0`. -/
theorem orthodoxXi_zero_ne_zero :
    orthodoxXi (0 : ℂ) ≠ 0 := by
  unfold orthodoxXi
  norm_num

/-- The normalization gives a nonzero value at `1`. -/
theorem orthodoxXi_one_ne_zero :
    orthodoxXi (1 : ℂ) ≠ 0 := by
  unfold orthodoxXi
  norm_num

/-- Real right outside-zone nonvanishing. -/
theorem orthodoxXi_ofReal_ne_zero_of_one_le
    {x : ℝ} (hx : 1 ≤ x) :
    orthodoxXi (x : ℂ) ≠ 0 := by
  rcases lt_or_eq_of_le hx with hxLt | hxEq
  · exact orthodoxXi_ne_zero_of_one_lt_re (by simpa using hxLt)
  · subst x
    simpa using orthodoxXi_one_ne_zero

/-- Real left outside-zone nonvanishing, reflected to the strict right
    half-plane by the `xi` functional equation. -/
theorem orthodoxXi_ofReal_ne_zero_of_nonpos
    {x : ℝ} (hx : x ≤ 0) :
    orthodoxXi (x : ℂ) ≠ 0 := by
  rcases lt_or_eq_of_le hx with hxLt | hxEq
  · have hRight : 1 < 1 - x := by linarith
    have hRightXi : orthodoxXi ((1 - x : ℝ) : ℂ) ≠ 0 :=
      orthodoxXi_ne_zero_of_one_lt_re (by simpa using hRight)
    have hRightXi' : orthodoxXi (1 - (x : ℂ)) ≠ 0 := by
      simpa using hRightXi
    intro hZero
    exact hRightXi' (by
      rw [orthodoxXi_one_sub]
      exact hZero)
  · subst x
    simpa using orthodoxXi_zero_ne_zero

/-- The outside-unit-interval real-axis nonvanishing theorem. -/
theorem g8OrthodoxXiOutsideUnitIntervalNonvanishing :
    G8OrthodoxXiOutsideUnitIntervalNonvanishing := by
  intro x hx
  rcases hx with hxLeft | hxRight
  · exact orthodoxXi_ofReal_ne_zero_of_nonpos hxLeft
  · exact orthodoxXi_ofReal_ne_zero_of_one_le hxRight

-- ============================================================
-- OPEN INTERVAL REDUCTIONS TO THE ZERO-HEIGHT GUARD
-- ============================================================

/-- On the open unit interval, zeta nonvanishing is sufficient for `xi`
    nonvanishing because the pole-removal factors are nonzero. -/
theorem orthodoxXi_ofReal_ne_zero_of_openUnit_riemannZeta_ne_zero
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hzeta : riemannZeta (x : ℂ) ≠ 0) :
    orthodoxXi (x : ℂ) ≠ 0 := by
  have hs0 : (x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hx0)
  have hs1 : (x : ℂ) ≠ 1 := by
    intro h
    have hxEq : x = 1 := by
      exact_mod_cast h
    exact (ne_of_lt hx1) hxEq
  exact orthodoxXi_ne_zero_of_riemannZeta_ne_zero hs0 hs1 hzeta

/-- The narrow zeta open-unit theorem supplies the residual `xi` open-unit
    theorem. -/
theorem g8OrthodoxXiOpenUnitIntervalNonvanishing_of_riemannZetaOpenUnit
    (hzetaOpen : G8RiemannZetaOpenUnitIntervalNonvanishing) :
    G8OrthodoxXiOpenUnitIntervalNonvanishing := by
  intro x hx0 hx1
  exact orthodoxXi_ofReal_ne_zero_of_openUnit_riemannZeta_ne_zero
    hx0 hx1 (hzetaOpen x hx0 hx1)

/-- Open-unit plus outside-zone nonvanishing covers the full real axis. -/
theorem g8OrthodoxXiRealAxisNonvanishing_of_openUnit_and_outside
    (hOpen : G8OrthodoxXiOpenUnitIntervalNonvanishing)
    (hOutside : G8OrthodoxXiOutsideUnitIntervalNonvanishing) :
    G8OrthodoxXiRealAxisNonvanishing := by
  intro x
  by_cases hxLeft : x ≤ 0
  · exact hOutside x (Or.inl hxLeft)
  by_cases hxRight : 1 ≤ x
  · exact hOutside x (Or.inr hxRight)
  exact hOpen x (lt_of_not_ge hxLeft) (lt_of_not_ge hxRight)

/-- The residual open-unit theorem is sufficient for real-axis nonvanishing,
    because the outside zones are theorem-backed above. -/
theorem g8OrthodoxXiRealAxisNonvanishing_of_openUnit
    (hOpen : G8OrthodoxXiOpenUnitIntervalNonvanishing) :
    G8OrthodoxXiRealAxisNonvanishing :=
  g8OrthodoxXiRealAxisNonvanishing_of_openUnit_and_outside
    hOpen g8OrthodoxXiOutsideUnitIntervalNonvanishing

/-- Real-axis nonvanishing discharges the zero-height axis guard. -/
theorem G8OrthodoxXiRealAxisNonvanishing.toZeroHeightAxisGuard
    (hReal : G8OrthodoxXiRealAxisNonvanishing) :
    G8ActualXiZeroHeightAxisGuard := by
  intro z hZero _hOff
  have hPoint :
      z.toZero.point = ((z.toZero.point.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hZero
  have hXiZero :
      orthodoxXi ((z.toZero.point.re : ℝ) : ℂ) = 0 := by
    have hZeroPoint := z.toZero.isZero
    rw [hPoint] at hZeroPoint
    exact hZeroPoint
  exact hReal z.toZero.point.re hXiZero

/-- The discharge package supplies the zero-height axis guard. -/
theorem G8ActualXiZeroHeightAxisGuardDischarge.zeroHeightAxisGuard
    (discharge : G8ActualXiZeroHeightAxisGuardDischarge) :
    G8ActualXiZeroHeightAxisGuard :=
  (g8OrthodoxXiRealAxisNonvanishing_of_openUnit
    discharge.openUnitNonvanishing).toZeroHeightAxisGuard

/-- A zeta nonvanishing theorem on the real open unit interval is exactly
    sufficient to build the zero-height discharge package. -/
def G8ActualXiZeroHeightAxisGuardDischarge.ofRiemannZetaOpenUnit
    (hzetaOpen : G8RiemannZetaOpenUnitIntervalNonvanishing) :
    G8ActualXiZeroHeightAxisGuardDischarge where
  openUnitNonvanishing :=
    g8OrthodoxXiOpenUnitIntervalNonvanishing_of_riemannZetaOpenUnit hzetaOpen

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A zero-height carrier that is nevertheless off-critical refutes the
    zero-height axis guard. -/
structure G8ActualXiZeroHeightOffCriticalFalsifier where
  z : OrthodoxXiZeroCarrier
  zeroHeight : z.toZero.point.im = 0
  offCritical : OrthodoxXiCarrierOffCritical z

/-- Zero-height off-critical evidence refutes the zero-height axis guard. -/
theorem G8ActualXiZeroHeightOffCriticalFalsifier.refutesZeroHeightAxis
    (w : G8ActualXiZeroHeightOffCriticalFalsifier)
    (guard : G8ActualXiZeroHeightAxisGuard) :
    False :=
  guard w.z w.zeroHeight w.offCritical

/-- A real open-unit zero of `orthodoxXi` refutes the residual open-unit
    theorem target. -/
structure G8OrthodoxXiOpenUnitIntervalZeroFalsifier where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  xiZero : orthodoxXi (x : ℂ) = 0

/-- Open-unit real-axis zero evidence refutes the residual theorem target. -/
theorem G8OrthodoxXiOpenUnitIntervalZeroFalsifier.refutesOpenUnit
    (w : G8OrthodoxXiOpenUnitIntervalZeroFalsifier)
    (hOpen : G8OrthodoxXiOpenUnitIntervalNonvanishing) :
    False :=
  hOpen w.x w.pos w.lt_one w.xiZero

end Tau.BookIII.Bridge
