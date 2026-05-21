import TauLib.BookIII.Bridge.G8ActualXiSpectralRealityCore

/-!
# TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightSpectralCore

Clean nonzero-height centered-quadratic core for Lane A.

This module names the nonzero-height carrier and the exact centered-quadratic
spectral-reality payload without importing the zero-height branch, accepted
coverage, final live hinge, O3, divisor transfer, or analytic-completion
machinery.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- NONZERO-HEIGHT CORE PAYLOAD
-- ============================================================

/-- Actual `xi` carriers whose orthodox point has nonzero imaginary height. -/
abbrev G8ActualXiNonzeroHeightCarrier : Type 2 :=
  { z : OrthodoxXiZeroCarrier // z.toZero.point.im ≠ 0 }

/-- The sharpened Lane-A spectral payload: the centered quadratic parameter is
    real only on actual `xi` carriers with nonzero imaginary height. -/
def G8ActualXiNonzeroHeightSpectralParameterReal : Prop :=
  ∀ z : G8ActualXiNonzeroHeightCarrier,
    (orthodoxXiCarrierCenteredQuadratic z.1).im = 0

-- ============================================================
-- PURE CENTERED-QUADRATIC ALGEBRA
-- ============================================================

/-- Pure algebraic forcing step: a real central-quadratic readout and nonzero
    height force the centered real coordinate onto the critical axis. -/
theorem g8CenteredQuadraticReality_forces_re_eq_half
    {sigma gamma : ℝ}
    (hReality : gamma * (1 - 2 * sigma) = 0)
    (hHeight : gamma ≠ 0) :
    sigma = (1 / 2 : ℝ) := by
  rcases mul_eq_zero.mp hReality with hGamma | hAxis
  · exact False.elim (hHeight hGamma)
  · have hTwo : (2 : ℝ) * sigma = 1 :=
      (sub_eq_zero.mp hAxis).symm
    calc
      sigma = ((2 : ℝ) * sigma) / 2 := by ring
      _ = 1 / 2 := by rw [hTwo]

/-- On the nonzero-height subtype, real centered quadratic parameter plus the
    theorem-backed readout forces the critical axis. -/
theorem g8NonzeroHeightSpectralParameterReal_forces_re_eq_half
    (hReal : G8ActualXiNonzeroHeightSpectralParameterReal)
    (z : G8ActualXiNonzeroHeightCarrier) :
    z.1.toZero.point.re = (1 / 2 : ℝ) := by
  apply
    g8CenteredQuadraticReality_forces_re_eq_half
      (sigma := z.1.toZero.point.re)
      (gamma := z.1.toZero.point.im)
  · change orthodoxXiCarrierCenteredQuadraticImagReadout z.1 = 0
    rw [← orthodoxXiCarrierCenteredQuadratic_im z.1]
    exact hReal z
  · exact z.2

/-- Nonzero-height spectral reality excludes off-criticality on the
    nonzero-height subtype. -/
theorem g8NonzeroHeightSpectralParameterReal_noOffCritical
    (hReal : G8ActualXiNonzeroHeightSpectralParameterReal)
    (z : G8ActualXiNonzeroHeightCarrier) :
    ¬ OrthodoxXiCarrierOffCritical z.1 := by
  intro hOff
  exact hOff (g8NonzeroHeightSpectralParameterReal_forces_re_eq_half hReal z)

/-- Conversely, nonzero-height off-critical exclusion is exactly sufficient to
    make the centered quadratic parameter real on the nonzero-height subtype.

This identifies the remaining nonzero-height Lane-A payload precisely: it is
not a bookkeeping condition, but the nonzero-height off-critical exclusion
theorem in centered-quadratic form. -/
theorem g8NonzeroHeightSpectralParameterReal_of_noOffCritical
    (hNoOff :
      ∀ z : G8ActualXiNonzeroHeightCarrier,
        ¬ OrthodoxXiCarrierOffCritical z.1) :
    G8ActualXiNonzeroHeightSpectralParameterReal := by
  intro z
  have hRe : z.1.toZero.point.re = (1 / 2 : ℝ) := by
    by_contra hNe
    exact hNoOff z hNe
  rw [orthodoxXiCarrierCenteredQuadratic_im]
  unfold orthodoxXiCarrierCenteredQuadraticImagReadout
  rw [hRe]
  ring

/-- The sharpened spectral-reality payload is equivalent to excluding
    off-critical nonzero-height carriers. -/
theorem g8NonzeroHeightSpectralParameterReal_iff_noOffCritical :
    G8ActualXiNonzeroHeightSpectralParameterReal ↔
      ∀ z : G8ActualXiNonzeroHeightCarrier,
        ¬ OrthodoxXiCarrierOffCritical z.1 := by
  constructor
  · exact g8NonzeroHeightSpectralParameterReal_noOffCritical
  · exact g8NonzeroHeightSpectralParameterReal_of_noOffCritical

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A nonzero-height carrier with non-real centered quadratic parameter
    refutes the nonzero-height spectral-parameter reality target. -/
structure G8ActualXiNonzeroHeightCenteredQuadraticNonrealFalsifier where
  z : G8ActualXiNonzeroHeightCarrier
  nonreal :
    (orthodoxXiCarrierCenteredQuadratic z.1).im ≠ 0

/-- Nonzero-height non-real centered quadratic evidence refutes the clean
    nonzero-height payload. -/
theorem
    G8ActualXiNonzeroHeightCenteredQuadraticNonrealFalsifier.refutesSpectralParameterReal
    (w : G8ActualXiNonzeroHeightCenteredQuadraticNonrealFalsifier)
    (hReal : G8ActualXiNonzeroHeightSpectralParameterReal) :
    False :=
  w.nonreal (hReal w.z)

end Tau.BookIII.Bridge
