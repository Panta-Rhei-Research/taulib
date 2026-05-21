import TauLib.BookIII.Bridge.G8EtaModTwoPairedStripEstimate

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoPairedDerivativeMVT

Mean-value/derivative estimator for the paired eta strip bound.

This module proves the local calculus bound requested by the paired eta
positive-half-plane route.  The proof stays upstream of the final RH spine: it
uses only the paired eta strip-estimate interface, elementary real interval
arithmetic, Mathlib's derivative formula for `t ↦ (t : ℂ) ^ c`, and the
one-dimensional mean-value norm inequality.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, pullback machinery, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex

-- ============================================================
-- REAL CPOW KERNEL
-- ============================================================

/-- The real-variable kernel behind each paired eta term. -/
def g8EtaModTwoRealCpowKernel (s : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (-s)

/-- Derivative formula for the real-variable complex-power kernel away from
    the harmless `s = 0` constant case. -/
theorem g8EtaModTwoRealCpowKernel_deriv
    {s : ℂ} (hs : s ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    deriv (fun u : ℝ => g8EtaModTwoRealCpowKernel s u) t =
      (-s) * (t : ℂ) ^ (-s - 1) := by
  simpa [g8EtaModTwoRealCpowKernel] using
    (Complex.deriv_ofReal_cpow_const (x := t) (c := -s)
      ht (neg_ne_zero.mpr hs))

/-- Interval lower endpoint positivity. -/
theorem g8EtaModTwo_pair_left_pos (n : ℕ) :
    0 < ((2 * n + 1 : ℕ) : ℝ) := by
  exact_mod_cast Nat.succ_pos (2 * n)

/-- Interval right endpoint positivity. -/
theorem g8EtaModTwo_pair_right_pos (n : ℕ) :
    0 < ((2 * n + 2 : ℕ) : ℝ) := by
  exact_mod_cast Nat.succ_pos (2 * n + 1)

/-- Every point in the pair interval is positive. -/
theorem g8EtaModTwo_pair_interval_pos
    {n : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc ((2 * n + 1 : ℕ) : ℝ) ((2 * n + 2 : ℕ) : ℝ)) :
    0 < t :=
  (g8EtaModTwo_pair_left_pos n).trans_le ht.1

/-- The pair interval sits to the right of `n+1`. -/
theorem g8EtaModTwo_pair_interval_ge_base
    {n : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc ((2 * n + 1 : ℕ) : ℝ) ((2 * n + 2 : ℕ) : ℝ)) :
    ((n + 1 : ℕ) : ℝ) ≤ t := by
  have hleft : ((n + 1 : ℕ) : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    have hleftNat : n + 1 ≤ 2 * n + 1 := by omega
    exact_mod_cast hleftNat
  exact hleft.trans ht.1

/-- The distance between paired endpoints is exactly one. -/
theorem g8EtaModTwo_pair_endpoint_norm (n : ℕ) :
    ‖(((2 * n + 2 : ℕ) : ℝ) - ((2 * n + 1 : ℕ) : ℝ))‖ = (1 : ℝ) := by
  have hsub :
      ((2 * n + 2 : ℕ) : ℝ) - ((2 * n + 1 : ℕ) : ℝ) = 1 := by
    norm_num
  rw [hsub]
  norm_num

-- ============================================================
-- DERIVATIVE MAJORANT
-- ============================================================

/-- The pointwise derivative majorant on a paired interval. -/
theorem g8EtaModTwoRealCpowKernel_deriv_norm_le_pairMajorant
    {delta B : ℝ} (hdelta : 0 < delta) (hB : 0 ≤ B)
    {s : ℂ} {n : ℕ} {t : ℝ}
    (hsRe : delta ≤ s.re) (hsNorm : ‖s‖ ≤ B)
    (ht : t ∈ Set.Icc ((2 * n + 1 : ℕ) : ℝ) ((2 * n + 2 : ℕ) : ℝ)) :
    ‖(-s) * (t : ℂ) ^ (-s - 1)‖ ≤
      g8EtaModTwoPairedStripMajorant delta B n := by
  have htpos : 0 < t := g8EtaModTwo_pair_interval_pos ht
  have htbase : ((n + 1 : ℕ) : ℝ) ≤ t :=
    g8EtaModTwo_pair_interval_ge_base ht
  have hbasepos : 0 < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  have hexp_nonpos : -(delta + 1) ≤ 0 := by
    linarith
  have hpow_base :
      t ^ (-(delta + 1)) ≤
        ((n + 1 : ℕ) : ℝ) ^ (-(delta + 1)) :=
    Real.rpow_le_rpow_of_nonpos hbasepos htbase hexp_nonpos
  have hexp_le : -s.re - 1 ≤ -(delta + 1) := by
    linarith
  have ht_ge_one : 1 ≤ t := by
    have hleft : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (2 * n))
    exact hleft.trans ht.1
  have hpow_exp :
      t ^ (-s.re - 1) ≤ t ^ (-(delta + 1)) :=
    Real.rpow_le_rpow_of_exponent_le ht_ge_one hexp_le
  have hpow :
      t ^ (-s.re - 1) ≤
        ((n + 1 : ℕ) : ℝ) ^ (-(delta + 1)) :=
    hpow_exp.trans hpow_base
  have hpow' :
      t ^ (-s.re - 1) ≤
        ((n : ℝ) + 1) ^ (-(delta + 1)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hpow
  have hnorm_eq :
      ‖(-s) * (t : ℂ) ^ (-s - 1)‖ =
        ‖s‖ * t ^ (-s.re - 1) := by
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    simp [sub_re]
  rw [hnorm_eq, g8EtaModTwoPairedStripMajorant]
  exact mul_le_mul hsNorm hpow' (Real.rpow_nonneg (le_of_lt htpos) _) hB

-- ============================================================
-- MEAN-VALUE ENDPOINT ESTIMATE
-- ============================================================

/-- The endpoint derivative/MVT estimate for one paired eta interval. -/
theorem g8EtaModTwoPairedDerivativeStrip_endpointBound_theorem
    {delta B : ℝ} (hdelta : 0 < delta) (hB : 0 ≤ B)
    {s : ℂ} {n : ℕ} (hsRe : delta ≤ s.re) (hsNorm : ‖s‖ ≤ B) :
    ‖(((2 * n + 1 : ℕ) : ℂ) ^ (-s) -
      ((2 * n + 2 : ℕ) : ℂ) ^ (-s))‖ ≤
      g8EtaModTwoPairedStripMajorant delta B n := by
  by_cases hs : s = 0
  · subst s
    have hmaj_nonneg :
        0 ≤ g8EtaModTwoPairedStripMajorant delta B n := by
      dsimp [g8EtaModTwoPairedStripMajorant]
      exact mul_nonneg hB (Real.rpow_nonneg (by positivity) _)
    simpa using hmaj_nonneg
  · let a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
    let b : ℝ := ((2 * n + 2 : ℕ) : ℝ)
    let C : ℝ := g8EtaModTwoPairedStripMajorant delta B n
    let f : ℝ → ℂ := fun t => g8EtaModTwoRealCpowKernel s t
    let f' : ℝ → ℂ := fun t => (-s) * (t : ℂ) ^ (-s - 1)
    have ha : a ∈ Set.Icc a b := by
      constructor <;> simp [a, b]
    have hb : b ∈ Set.Icc a b := by
      constructor <;> simp [a, b]
    have hderiv :
        ∀ t ∈ Set.Icc a b, HasDerivWithinAt f (f' t) (Set.Icc a b) t := by
      intro t ht
      have htpos : 0 < t := by
        exact g8EtaModTwo_pair_interval_pos (n := n) (by simpa [a, b] using ht)
      exact
        (hasDerivAt_ofReal_cpow_const
          (x := t) (r := -s) htpos.ne' (neg_ne_zero.mpr hs)).hasDerivWithinAt
    have hbound :
        ∀ t ∈ Set.Icc a b, ‖f' t‖ ≤ C := by
      intro t ht
      exact
        g8EtaModTwoRealCpowKernel_deriv_norm_le_pairMajorant
          hdelta hB hsRe hsNorm (n := n)
          (by simpa [a, b, f', C] using ht)
    have hmvt :
        ‖f b - f a‖ ≤ C * ‖b - a‖ :=
      (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
        hderiv hbound ha hb
    have hC_nonneg : 0 ≤ C := by
      dsimp [C, g8EtaModTwoPairedStripMajorant]
      exact mul_nonneg hB (Real.rpow_nonneg (by positivity) _)
    have hdist : ‖b - a‖ = (1 : ℝ) := by
      simpa [a, b] using g8EtaModTwo_pair_endpoint_norm n
    have hmvt' : ‖f b - f a‖ ≤ C := by
      simpa [hdist] using hmvt
    have hsym : ‖f a - f b‖ = ‖f b - f a‖ := by
      rw [← norm_neg, neg_sub]
    have hmvt_rev : ‖f a - f b‖ ≤ C := by
      rw [hsym]
      exact hmvt'
    simpa [a, b, f, C, g8EtaModTwoRealCpowKernel] using hmvt_rev

/-- The paired eta derivative/MVT strip-bound payload is theorem-backed. -/
def g8EtaModTwoPairedDerivativeStripBound_theorem :
    G8EtaModTwoPairedDerivativeStripBound where
  endpointBound := by
    intro delta B hdelta hB s n hsRe hsNorm
    exact
      g8EtaModTwoPairedDerivativeStrip_endpointBound_theorem
        hdelta hB hsRe hsNorm

/-- The MVT estimator supplies the existing positive-half-plane strip estimate. -/
def g8EtaModTwoPairedPositiveHalfPlaneStripEstimate_from_mvt :
    G8EtaModTwoPairedPositiveHalfPlaneStripEstimate :=
  g8EtaModTwoPairedDerivativeStripBound_theorem.toStripEstimate

end Tau.BookIII.Bridge
