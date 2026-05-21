import TauLib.BookIII.Bridge.G8EtaModTwoPairedDerivativeMVT

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoPairedLocalUniformConvergence

Local-uniform convergence for the paired eta positive-half-plane route.

The previous module proved the MVT/derivative strip estimate.  This module
turns that estimate into the Weierstrass majorant argument on compact subsets
of the positive half-plane and supplies the convergence package expected by
the positive-half-plane analyticity layer.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, pullback machinery, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex

open scoped Topology

-- ============================================================
-- COMPACT STRIP ENVELOPES
-- ============================================================

/-- Compact subsets of the positive half-plane sit inside a closed strip
    `delta ≤ re s`, `‖s‖ ≤ B` with `delta > 0`.

This is the compactness input needed to globalize the pointwise MVT strip
estimate into local-uniform summability. -/
theorem g8EtaModTwoCompactPositiveHalfPlaneStripEnvelopeExists
    {K : Set ℂ}
    (hKsub : K ⊆ G8EtaModTwoPositiveHalfPlane)
    (hKc : IsCompact K) :
    ∃ delta B : ℝ,
      0 < delta ∧ 0 ≤ B ∧
        ∀ s ∈ K, delta ≤ s.re ∧ ‖s‖ ≤ B := by
  by_cases hne : K.Nonempty
  · obtain ⟨sMin, hsMin, hMin⟩ :=
      hKc.exists_isMinOn hne continuous_re.continuousOn
    obtain ⟨sMax, hsMax, hMax⟩ :=
      hKc.exists_isMaxOn hne continuous_norm.continuousOn
    refine ⟨sMin.re, ‖sMax‖, hKsub hsMin, norm_nonneg sMax, ?_⟩
    intro s hs
    exact ⟨isMinOn_iff.mp hMin s hs, isMaxOn_iff.mp hMax s hs⟩
  · refine ⟨1, 0, by norm_num, le_rfl, ?_⟩
    intro s hs
    exact False.elim (hne ⟨s, hs⟩)

-- ============================================================
-- LOCAL-UNIFORM CONVERGENCE
-- ============================================================

/-- The positive half-plane is open. -/
theorem g8EtaModTwoPositiveHalfPlane_isOpen :
    IsOpen G8EtaModTwoPositiveHalfPlane := by
  simpa [G8EtaModTwoPositiveHalfPlane] using
    isOpen_lt continuous_const continuous_re

/-- The theorem-backed MVT strip estimate gives local-uniform summability of
    the paired eta terms on the positive half-plane. -/
theorem g8EtaModTwoPairedPositiveHalfPlane_locallyUniform_from_mvt :
    SummableLocallyUniformlyOn
      (fun n : ℕ => fun s : ℂ => g8EtaModTwoPairedEtaTerm s n)
      G8EtaModTwoPositiveHalfPlane := by
  refine SummableLocallyUniformlyOn_of_locally_bounded
    g8EtaModTwoPositiveHalfPlane_isOpen ?_
  intro K hKsub hKc
  obtain ⟨delta, B, hdelta, hB, hEnvelope⟩ :=
    g8EtaModTwoCompactPositiveHalfPlaneStripEnvelopeExists hKsub hKc
  refine ⟨g8EtaModTwoPairedStripMajorant delta B,
    g8EtaModTwoPairedStripMajorant_summable hdelta, ?_⟩
  intro n s hs
  obtain ⟨hsRe, hsNorm⟩ := hEnvelope s hs
  simpa [g8EtaModTwoPairedStripMajorant] using
    g8EtaModTwoPairedPositiveHalfPlaneStripEstimate_from_mvt.estimate
      delta B hdelta hB s n hsRe hsNorm

/-- Pointwise summability on the positive half-plane follows from local-uniform
    summability. -/
theorem g8EtaModTwoPairedPositiveHalfPlane_summable_from_mvt
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => g8EtaModTwoPairedEtaTerm s n) :=
  g8EtaModTwoPairedPositiveHalfPlane_locallyUniform_from_mvt.summable hs

/-- The MVT strip estimate supplies the convergence component of the
    positive-half-plane analytic package. -/
def g8EtaModTwoPairedPositiveHalfPlaneConvergence_from_mvt :
    G8EtaModTwoPairedPositiveHalfPlaneConvergence where
  stripEstimate := g8EtaModTwoPairedPositiveHalfPlaneStripEstimate_from_mvt
  locallyUniform := g8EtaModTwoPairedPositiveHalfPlane_locallyUniform_from_mvt
  summable := fun _s hs =>
    g8EtaModTwoPairedPositiveHalfPlane_summable_from_mvt hs

end Tau.BookIII.Bridge
