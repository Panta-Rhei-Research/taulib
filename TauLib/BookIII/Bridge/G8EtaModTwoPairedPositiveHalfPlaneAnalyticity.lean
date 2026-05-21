import TauLib.BookIII.Bridge.G8EtaModTwoPairedExpZetaBoundaryTheorem

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoPairedPositiveHalfPlaneAnalyticity

Proof-facing positive-half-plane analyticity package for the paired eta route.

The previous module reduced the zero-height eta payload to one exact theorem:
the paired eta series converges on `0 < re s` and has Mathlib's continued
additive-character `-expZeta` value there.  This module decomposes that theorem
into the analytic work that should prove it: strip estimates, local-uniform
convergence/analyticity, safe-half-plane agreement, and analytic continuation.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, pullback machinery, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped Topology

-- ============================================================
-- POSITIVE-HALF-PLANE ANALYTIC TARGETS
-- ============================================================

/-- The positive half-plane for the paired eta analytic proof. -/
abbrev G8EtaModTwoPositiveHalfPlane : Set ℂ :=
  {s : ℂ | 0 < s.re}

/-- The safe half-plane where ordinary `LSeries` identities are theorem-backed. -/
abbrev G8EtaModTwoSafeHalfPlane : Set ℂ :=
  {s : ℂ | 1 < s.re}

/-- The concrete strip estimate that should drive the local-uniform convergence
    proof on compact subsets of the positive half-plane.

The intended proof uses the mean-value estimate for
`t ↦ (t : ℂ) ^ (-s)` on `[2n+1, 2n+2]`, bounded on strips
`δ ≤ re s`, `‖s‖ ≤ B`, followed by the summable majorant
`(n+1)^(-(δ+1))`. -/
structure G8EtaModTwoPairedPositiveHalfPlaneStripEstimate where
  estimate :
    ∀ (δ B : ℝ), 0 < δ → 0 ≤ B →
      ∀ (s : ℂ) (n : ℕ), δ ≤ s.re → ‖s‖ ≤ B →
        ‖g8EtaModTwoPairedEtaTerm s n‖ ≤
          B * ((n + 1 : ℝ) ^ (-(δ + 1)))

/-- Local-uniform convergence data for the paired eta series on the positive
    half-plane, together with its pointwise summability consequence. -/
structure G8EtaModTwoPairedPositiveHalfPlaneConvergence where
  stripEstimate : G8EtaModTwoPairedPositiveHalfPlaneStripEstimate
  locallyUniform :
    SummableLocallyUniformlyOn
      (fun n : ℕ => fun s : ℂ => g8EtaModTwoPairedEtaTerm s n)
      G8EtaModTwoPositiveHalfPlane
  summable :
    ∀ (s : ℂ), 0 < s.re →
      Summable (fun n : ℕ => g8EtaModTwoPairedEtaTerm s n)

/-- Analyticity data needed for the identity-theorem continuation step. -/
structure G8EtaModTwoPairedPositiveHalfPlaneAnalyticity where
  convergence : G8EtaModTwoPairedPositiveHalfPlaneConvergence
  pairedAnalytic :
    AnalyticOnNhd ℂ g8EtaModTwoPairedEtaSeries
      G8EtaModTwoPositiveHalfPlane
  negExpZetaAnalytic :
    AnalyticOnNhd ℂ
      (fun s : ℂ =>
        - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s)
      G8EtaModTwoPositiveHalfPlane

/-- Agreement on the safe half-plane `1 < re s`, where the ordinary
    Dirichlet-series algebra and Mathlib's `ZMod.LFunction` theorem apply. -/
structure G8EtaModTwoPairedSafeHalfPlaneAgreement where
  agreement :
    ∀ (s : ℂ), 1 < s.re →
      g8EtaModTwoPairedEtaSeries s =
        - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s

/-- The identity-theorem continuation payload from the safe half-plane to all
    of `0 < re s`.  This is separated from the raw analytic fields so that the
    remaining proof obligation is exactly visible if the local-uniform
    estimates are theorem-backed before the identity-theorem application. -/
structure G8EtaModTwoPairedPositiveHalfPlaneContinuation where
  analyticity : G8EtaModTwoPairedPositiveHalfPlaneAnalyticity
  safeAgreement : G8EtaModTwoPairedSafeHalfPlaneAgreement
  continuedAgreement :
    ∀ (s : ℂ), 0 < s.re →
      g8EtaModTwoPairedEtaSeries s =
        - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s

/-- The compact package for the positive-half-plane paired eta proof. -/
structure G8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage where
  continuation : G8EtaModTwoPairedPositiveHalfPlaneContinuation

-- ============================================================
-- SELECTORS AND ADAPTERS
-- ============================================================

/-- Selector for the strip estimate from the compact package. -/
theorem g8EtaModTwoPairedPositiveHalfPlane_stripEstimate
    (pkg : G8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage) :
    G8EtaModTwoPairedPositiveHalfPlaneStripEstimate :=
  pkg.continuation.analyticity.convergence.stripEstimate

/-- Selector for pointwise summability on the positive half-plane. -/
theorem g8EtaModTwoPairedPositiveHalfPlane_summable
    (pkg : G8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage)
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => g8EtaModTwoPairedEtaTerm s n) :=
  pkg.continuation.analyticity.convergence.summable s hs

/-- Selector for safe-half-plane paired eta / `-expZeta` agreement. -/
theorem g8EtaModTwoPairedSafeHalfPlane_agreement
    (pkg : G8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage)
    {s : ℂ} (hs : 1 < s.re) :
    g8EtaModTwoPairedEtaSeries s =
      - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s :=
  pkg.continuation.safeAgreement.agreement s hs

/-- Selector for the continued positive-half-plane equality. -/
theorem g8EtaModTwoPairedPositiveHalfPlane_agreement
    (pkg : G8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage)
    {s : ℂ} (hs : 0 < s.re) :
    g8EtaModTwoPairedEtaSeries s =
      - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s :=
  pkg.continuation.continuedAgreement s hs

/-- The analyticity package is exactly sufficient for the existing
    positive-half-plane paired eta core. -/
def G8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage.toPositiveHalfPlaneCore
    (pkg : G8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage) :
    G8EtaModTwoPairedEtaSeriesEqNegExpZetaOnPositiveHalfPlane where
  summable := fun _s hs =>
    g8EtaModTwoPairedPositiveHalfPlane_summable pkg hs
  eq_neg_expZeta := fun _s hs =>
    g8EtaModTwoPairedPositiveHalfPlane_agreement pkg hs

/-- The analyticity package supplies the paired ExpZeta boundary theorem. -/
theorem g8EtaModTwoPairedExpZetaBoundaryOnOpenUnit_of_positiveHalfPlaneAnalyticPackage
    (pkg : G8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage) :
    G8EtaModTwoPairedExpZetaBoundaryOnOpenUnit :=
  g8EtaModTwoPairedExpZetaBoundaryOnOpenUnit_of_posHalfPlane
    pkg.toPositiveHalfPlaneCore

/-- The analyticity package supplies the pointwise ExpZeta/concrete-eta
    equality. -/
theorem g8EtaModTwoExpZetaConcreteEtaOnOpenUnit_of_positiveHalfPlaneAnalyticPackage
    (pkg : G8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage) :
    G8EtaModTwoExpZetaConcreteEtaOnOpenUnit :=
  g8EtaModTwoExpZetaConcreteEtaOnOpenUnit_of_posHalfPlane
    pkg.toPositiveHalfPlaneCore

/-- The analyticity package discharges the zero-height guard through the
    existing paired positive-half-plane adapter. -/
def G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoPairedPositiveHalfPlaneAnalyticPackage
    (pkg : G8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage) :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoPairedPositiveHalfPlane
    pkg.toPositiveHalfPlaneCore

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A single strip point violating the intended majorant refutes the strip
    estimate payload. -/
structure G8EtaModTwoPairedPositiveHalfPlaneStripEstimateFailure where
  delta : ℝ
  B : ℝ
  pos_delta : 0 < delta
  nonneg_B : 0 ≤ B
  s : ℂ
  n : ℕ
  strip_re : delta ≤ s.re
  strip_norm : ‖s‖ ≤ B
  violates :
    ¬ (‖g8EtaModTwoPairedEtaTerm s n‖ ≤
      B * ((n + 1 : ℝ) ^ (-(delta + 1))))

/-- A strip-estimate failure refutes the strip estimate payload. -/
theorem G8EtaModTwoPairedPositiveHalfPlaneStripEstimateFailure.refutes
    (w : G8EtaModTwoPairedPositiveHalfPlaneStripEstimateFailure)
    (hStrip : G8EtaModTwoPairedPositiveHalfPlaneStripEstimate) :
    False :=
  w.violates
    (hStrip.estimate w.delta w.B w.pos_delta w.nonneg_B
      w.s w.n w.strip_re w.strip_norm)

/-- Failure of local-uniform convergence refutes the convergence package. -/
structure G8EtaModTwoPairedPositiveHalfPlaneLocalUniformFailure where
  not_locallyUniform :
    ¬ SummableLocallyUniformlyOn
      (fun n : ℕ => fun s : ℂ => g8EtaModTwoPairedEtaTerm s n)
      G8EtaModTwoPositiveHalfPlane

/-- A local-uniform failure refutes positive-half-plane convergence data. -/
theorem G8EtaModTwoPairedPositiveHalfPlaneLocalUniformFailure.refutes
    (w : G8EtaModTwoPairedPositiveHalfPlaneLocalUniformFailure)
    (hConv : G8EtaModTwoPairedPositiveHalfPlaneConvergence) :
    False :=
  w.not_locallyUniform hConv.locallyUniform

/-- A safe-half-plane mismatch refutes the safe agreement payload. -/
structure G8EtaModTwoPairedSafeHalfPlaneAgreementMismatch where
  s : ℂ
  safe_re : 1 < s.re
  mismatch :
    g8EtaModTwoPairedEtaSeries s ≠
      - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s

/-- A safe-half-plane mismatch refutes safe agreement. -/
theorem G8EtaModTwoPairedSafeHalfPlaneAgreementMismatch.refutes
    (w : G8EtaModTwoPairedSafeHalfPlaneAgreementMismatch)
    (hSafe : G8EtaModTwoPairedSafeHalfPlaneAgreement) :
    False :=
  w.mismatch (hSafe.agreement w.s w.safe_re)

/-- A positive-half-plane continuation mismatch refutes the compact analytic
    package. -/
structure G8EtaModTwoPairedPositiveHalfPlaneContinuationMismatch where
  s : ℂ
  pos_re : 0 < s.re
  mismatch :
    g8EtaModTwoPairedEtaSeries s ≠
      - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s

/-- A continuation mismatch refutes the compact analytic package. -/
theorem G8EtaModTwoPairedPositiveHalfPlaneContinuationMismatch.refutes
    (w : G8EtaModTwoPairedPositiveHalfPlaneContinuationMismatch)
    (pkg : G8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage) :
    False :=
  w.mismatch
    (g8EtaModTwoPairedPositiveHalfPlane_agreement pkg w.pos_re)

/-- A positive-half-plane pointwise value mismatch from the previous module
    refutes the compact analytic package through the core adapter. -/
theorem G8EtaModTwoPairedEtaSeriesPositiveHalfPlaneValueMismatch.refutes_package
    (w : G8EtaModTwoPairedEtaSeriesPositiveHalfPlaneValueMismatch)
    (pkg : G8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage) :
    False :=
  w.refutes pkg.toPositiveHalfPlaneCore

/-- A pointwise paired-boundary mismatch refutes the compact analytic package
    through the existing paired-boundary adapter. -/
theorem G8EtaModTwoPairedExpZetaBoundaryMismatch.refutes_positiveHalfPlaneAnalyticPackage
    (w : G8EtaModTwoPairedExpZetaBoundaryMismatch)
    (pkg : G8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage) :
    False :=
  w.refutes
    (g8EtaModTwoPairedExpZetaBoundaryOnOpenUnit_of_positiveHalfPlaneAnalyticPackage
      pkg)

end Tau.BookIII.Bridge
