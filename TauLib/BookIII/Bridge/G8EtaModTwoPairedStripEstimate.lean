import TauLib.BookIII.Bridge.G8EtaModTwoPairedPositiveHalfPlaneAnalyticity

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoPairedStripEstimate

Strip-estimate reduction for the paired eta positive-half-plane route.

The next analytic proof stone is the mean-value/derivative estimate for
`t ↦ (t : ℂ) ^ (-s)` on the interval `[2n+1, 2n+2]`.  This module packages
that bound as the exact remaining local theorem target and proves that it is
precisely sufficient for the strip estimate consumed by the local-uniform
convergence corridor.  It also closes the elementary p-series summability
selector for the resulting majorant.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, pullback machinery, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex

-- ============================================================
-- STRIP MAJORANT
-- ============================================================

/-- The strip majorant expected from the derivative/MVT estimate. -/
def g8EtaModTwoPairedStripMajorant
    (delta B : ℝ) (n : ℕ) : ℝ :=
  B * ((n + 1 : ℝ) ^ (-(delta + 1)))

/-- The strip majorant is summable whenever `delta > 0`.

This is the theorem-backed p-series part of the strip-estimate route.  The
analytic work that remains is the pointwise derivative/MVT comparison to this
majorant. -/
theorem g8EtaModTwoPairedStripMajorant_summable
    {delta B : ℝ} (hdelta : 0 < delta) :
    Summable (fun n : ℕ =>
      g8EtaModTwoPairedStripMajorant delta B n) := by
  have hp : -(delta + 1) < -1 := by
    linarith
  have hbase :
      Summable (fun n : ℕ => (n : ℝ) ^ (-(delta + 1))) :=
    Real.summable_nat_rpow.mpr hp
  have hshift :
      Summable (fun n : ℕ => ((n + 1 : ℝ) ^ (-(delta + 1)))) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff
        (f := fun n : ℕ => (n : ℝ) ^ (-(delta + 1))) 1).mpr hbase)
  simpa [g8EtaModTwoPairedStripMajorant] using
    (Summable.mul_left B hshift)

-- ============================================================
-- DERIVATIVE / MVT RESIDUAL
-- ============================================================

/-- The exact derivative/MVT bound still needed to prove the strip estimate.

Mathematically this should follow from
`Complex.deriv_ofReal_cpow_const`, the mean-value inequality on
`[2n+1, 2n+2]`, and the strip hypotheses `delta ≤ re s`, `‖s‖ ≤ B`.
It is kept separate from the local-uniform convergence package so this wave
does not hide the real analytic payload behind a broader interface. -/
structure G8EtaModTwoPairedDerivativeStripBound where
  endpointBound :
    ∀ (delta B : ℝ), 0 < delta → 0 ≤ B →
      ∀ (s : ℂ) (n : ℕ), delta ≤ s.re → ‖s‖ ≤ B →
        ‖(((2 * n + 1 : ℕ) : ℂ) ^ (-s) -
          ((2 * n + 2 : ℕ) : ℂ) ^ (-s))‖ ≤
          g8EtaModTwoPairedStripMajorant delta B n

/-- The derivative/MVT endpoint bound is exactly sufficient for the strip
    estimate required by the positive-half-plane analyticity package. -/
def G8EtaModTwoPairedDerivativeStripBound.toStripEstimate
    (hBound : G8EtaModTwoPairedDerivativeStripBound) :
    G8EtaModTwoPairedPositiveHalfPlaneStripEstimate where
  estimate := by
    intro delta B hdelta hB s n hsRe hsNorm
    simpa [g8EtaModTwoPairedEtaTerm,
      g8EtaModTwoPairedStripMajorant] using
      hBound.endpointBound delta B hdelta hB s n hsRe hsNorm

/-- Selector form of the endpoint bound. -/
theorem g8EtaModTwoPairedDerivativeStrip_endpointBound
    (hBound : G8EtaModTwoPairedDerivativeStripBound)
    {delta B : ℝ} (hdelta : 0 < delta) (hB : 0 ≤ B)
    {s : ℂ} {n : ℕ} (hsRe : delta ≤ s.re) (hsNorm : ‖s‖ ≤ B) :
    ‖(((2 * n + 1 : ℕ) : ℂ) ^ (-s) -
      ((2 * n + 2 : ℕ) : ℂ) ^ (-s))‖ ≤
      g8EtaModTwoPairedStripMajorant delta B n :=
  hBound.endpointBound delta B hdelta hB s n hsRe hsNorm

/-- Selector form after converting the derivative/MVT bound to the existing
    strip-estimate interface. -/
theorem g8EtaModTwoPairedStripEstimate_of_derivativeBound
    (hBound : G8EtaModTwoPairedDerivativeStripBound)
    {delta B : ℝ} (hdelta : 0 < delta) (hB : 0 ≤ B)
    {s : ℂ} {n : ℕ} (hsRe : delta ≤ s.re) (hsNorm : ‖s‖ ≤ B) :
    ‖g8EtaModTwoPairedEtaTerm s n‖ ≤
      B * ((n + 1 : ℝ) ^ (-(delta + 1))) :=
  hBound.toStripEstimate.estimate delta B hdelta hB s n hsRe hsNorm

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A pointwise failure of the derivative/MVT endpoint estimate refutes the
    derivative strip bound. -/
structure G8EtaModTwoPairedDerivativeStripBoundFailure where
  delta : ℝ
  B : ℝ
  pos_delta : 0 < delta
  nonneg_B : 0 ≤ B
  s : ℂ
  n : ℕ
  strip_re : delta ≤ s.re
  strip_norm : ‖s‖ ≤ B
  violates :
    ¬ (‖(((2 * n + 1 : ℕ) : ℂ) ^ (-s) -
      ((2 * n + 2 : ℕ) : ℂ) ^ (-s))‖ ≤
      g8EtaModTwoPairedStripMajorant delta B n)

/-- A derivative strip-bound failure refutes the derivative strip-bound
    payload. -/
theorem G8EtaModTwoPairedDerivativeStripBoundFailure.refutes
    (w : G8EtaModTwoPairedDerivativeStripBoundFailure)
    (hBound : G8EtaModTwoPairedDerivativeStripBound) :
    False :=
  w.violates
    (hBound.endpointBound w.delta w.B w.pos_delta w.nonneg_B
      w.s w.n w.strip_re w.strip_norm)

/-- A strip-estimate failure from the positive-half-plane module refutes a
    derivative/MVT bound through the adapter above. -/
theorem G8EtaModTwoPairedPositiveHalfPlaneStripEstimateFailure.refutes_derivativeBound
    (w : G8EtaModTwoPairedPositiveHalfPlaneStripEstimateFailure)
    (hBound : G8EtaModTwoPairedDerivativeStripBound) :
    False :=
  w.refutes hBound.toStripEstimate

end Tau.BookIII.Bridge
