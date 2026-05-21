import TauLib.BookIII.Bridge.G8EtaModTwoPairedSeriesBoundary

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoPairedExpZetaBoundaryTheorem

Proof-facing paired ExpZeta boundary surface for the remaining Lane-A
zero-height eta payload.

The finite grouping and concrete eta limit are theorem-backed in
`G8EtaModTwoPairedSeriesBoundary`.  This module closes the low-level bridge
between those concrete paired partial sums and the analytic paired series
`g8EtaModTwoPairedEtaSeries`.  The remaining analytic payload is now the
single positive-half-plane theorem saying that the paired eta series converges
and has Mathlib's continued additive-character `-expZeta` value.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, pullback machinery, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped BigOperators Topology

-- ============================================================
-- CONCRETE / ANALYTIC PAIRED-SERIES BRIDGE
-- ============================================================

/-- Finite partial sums of the analytic paired eta series. -/
def g8EtaModTwoPairedEtaPartial (s : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, g8EtaModTwoPairedEtaTerm s k

/-- The concrete real paired term is the analytic paired eta term specialized
    to the real point `s = x`. -/
theorem g8EtaModTwoConcretePairedTerm_eq_pairedEtaTerm
    (x : ℝ) (n : ℕ) :
    g8EtaModTwoConcretePairedTerm x n =
      g8EtaModTwoPairedEtaTerm (x : ℂ) n := by
  unfold g8EtaModTwoConcretePairedTerm g8EtaModTwoPairedEtaTerm
  have hOdd : g8EtaModTwoNatCoeff (2 * n + 1) = 1 :=
    (g8EtaModTwoNatCoeff_odd_even_pair n).1
  have hEven : g8EtaModTwoNatCoeff (2 * n + 2) = -1 :=
    (g8EtaModTwoNatCoeff_odd_even_pair n).2
  rw [hOdd, hEven]
  simp only [one_mul, neg_mul, one_mul]
  have hpow1 :
      (((2 * (n : ℝ) + 1) ^ (-x : ℝ) : ℝ) : ℂ) =
        (((2 * (n : ℝ) + 1 : ℝ) : ℂ) ^ (-(x : ℂ))) := by
    calc
      (((2 * (n : ℝ) + 1) ^ (-x : ℝ) : ℝ) : ℂ) =
          (((2 * (n : ℝ) + 1 : ℝ) : ℂ) ^ ((-x : ℝ) : ℂ)) := by
        exact Complex.ofReal_cpow
          (by positivity : 0 ≤ 2 * (n : ℝ) + 1) (-x)
      _ = (((2 * (n : ℝ) + 1 : ℝ) : ℂ) ^ (-(x : ℂ))) := by
        congr 1
        norm_num
  have hpow2 :
      (((2 * (n : ℝ) + 1 + 1) ^ (-x : ℝ) : ℝ) : ℂ) =
        (((2 * (n : ℝ) + 2 : ℝ) : ℂ) ^ (-(x : ℂ))) := by
    calc
      (((2 * (n : ℝ) + 1 + 1) ^ (-x : ℝ) : ℝ) : ℂ) =
          (((2 * (n : ℝ) + 1 + 1 : ℝ) : ℂ) ^
            ((-x : ℝ) : ℂ)) := by
        exact Complex.ofReal_cpow
          (by positivity : 0 ≤ 2 * (n : ℝ) + 1 + 1) (-x)
      _ = (((2 * (n : ℝ) + 2 : ℝ) : ℂ) ^ (-(x : ℂ))) := by
        congr 1
        · ring_nf
        · norm_num
  simp [g8DirichletEtaMagnitude, hpow1, hpow2]
  ring

/-- Concrete paired partial sums are the analytic paired partial sums at the
    real point `s = x`. -/
theorem g8EtaModTwoConcretePairedPartial_eq_pairedEtaPartial
    (x : ℝ) (n : ℕ) :
    g8EtaModTwoConcretePairedPartial x n =
      g8EtaModTwoPairedEtaPartial (x : ℂ) n := by
  simp [g8EtaModTwoConcretePairedPartial, g8EtaModTwoPairedEtaPartial,
    g8EtaModTwoConcretePairedTerm_eq_pairedEtaTerm]

/-- If the analytic paired eta series is summable, then its finite paired
    partial sums tend to the corresponding `tsum`. -/
theorem g8EtaModTwoPairedEtaPartial_tendsto_pairedEtaSeries_of_summable
    {s : ℂ}
    (hSummable : Summable (fun n : ℕ => g8EtaModTwoPairedEtaTerm s n)) :
    Tendsto (g8EtaModTwoPairedEtaPartial s) atTop
      (𝓝 (g8EtaModTwoPairedEtaSeries s)) := by
  simpa [g8EtaModTwoPairedEtaPartial, g8EtaModTwoPairedEtaSeries] using
    hSummable.hasSum.tendsto_sum_nat

/-- If the analytic paired eta series is summable at `(x : ℂ)`, then the
    concrete paired partial sums tend to its analytic paired-series value. -/
theorem g8EtaModTwoConcretePairedPartial_tendsto_pairedEtaSeries_of_summable
    (x : ℝ)
    (hSummable :
      Summable (fun n : ℕ => g8EtaModTwoPairedEtaTerm (x : ℂ) n)) :
    Tendsto (g8EtaModTwoConcretePairedPartial x) atTop
      (𝓝 (g8EtaModTwoPairedEtaSeries (x : ℂ))) :=
  (g8EtaModTwoPairedEtaPartial_tendsto_pairedEtaSeries_of_summable
      (s := (x : ℂ)) hSummable).congr'
    (Eventually.of_forall fun n =>
      (g8EtaModTwoConcretePairedPartial_eq_pairedEtaPartial x n).symm)

-- ============================================================
-- EXACT POSITIVE-HALF-PLANE ANALYTIC PAYLOAD
-- ============================================================

/-- The single remaining analytic payload for the paired ExpZeta route.

It combines the two positive-half-plane facts needed to turn paired partial
sums into the ExpZeta boundary value: convergence of the paired eta series and
identification of its sum with Mathlib's continued additive-character
`-expZeta` value. -/
structure G8EtaModTwoPairedEtaSeriesEqNegExpZetaOnPositiveHalfPlane where
  summable :
    ∀ (s : ℂ), 0 < s.re →
      Summable (fun n : ℕ => g8EtaModTwoPairedEtaTerm s n)
  eq_neg_expZeta :
    ∀ (s : ℂ), 0 < s.re →
      g8EtaModTwoPairedEtaSeries s =
        - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s

/-- Selector for paired-series convergence on the positive half-plane. -/
theorem g8EtaModTwoPairedEtaTerm_summable_of_pos_re
    (hCore : G8EtaModTwoPairedEtaSeriesEqNegExpZetaOnPositiveHalfPlane)
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => g8EtaModTwoPairedEtaTerm s n) :=
  hCore.summable s hs

/-- Selector for the positive-half-plane paired eta / ExpZeta equality. -/
theorem g8EtaModTwoPairedEtaSeries_eq_neg_expZeta_of_pos_re
    (hCore : G8EtaModTwoPairedEtaSeriesEqNegExpZetaOnPositiveHalfPlane)
    {s : ℂ} (hs : 0 < s.re) :
    g8EtaModTwoPairedEtaSeries s =
      - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s :=
  hCore.eq_neg_expZeta s hs

/-- The positive-half-plane paired-series theorem is exactly sufficient for
    the existing real open-unit paired ExpZeta boundary target. -/
theorem g8EtaModTwoPairedExpZetaBoundaryOnOpenUnit_of_posHalfPlane
    (hCore : G8EtaModTwoPairedEtaSeriesEqNegExpZetaOnPositiveHalfPlane) :
    G8EtaModTwoPairedExpZetaBoundaryOnOpenUnit := by
  intro x hx0 hx1
  have hxRe : 0 < ((x : ℂ).re) := by
    simpa using hx0
  have hTendsto :
      Tendsto (g8EtaModTwoConcretePairedPartial x) atTop
        (𝓝 (g8EtaModTwoPairedEtaSeries (x : ℂ))) :=
    g8EtaModTwoConcretePairedPartial_tendsto_pairedEtaSeries_of_summable x
      (hCore.summable (x : ℂ) hxRe)
  have hValue :
      g8EtaModTwoPairedEtaSeries (x : ℂ) =
        - HurwitzZeta.expZeta
          (ZMod.toAddCircle (1 : ZMod 2)) (x : ℂ) :=
    hCore.eq_neg_expZeta (x : ℂ) hxRe
  simpa [hValue] using hTendsto

/-- The positive-half-plane paired-series theorem supplies the pointwise
    ExpZeta/concrete-eta equality. -/
theorem g8EtaModTwoExpZetaConcreteEtaOnOpenUnit_of_posHalfPlane
    (hCore : G8EtaModTwoPairedEtaSeriesEqNegExpZetaOnPositiveHalfPlane) :
    G8EtaModTwoExpZetaConcreteEtaOnOpenUnit :=
  g8EtaModTwoExpZetaConcreteEtaOnOpenUnit_of_pairedBoundary
    (g8EtaModTwoPairedExpZetaBoundaryOnOpenUnit_of_posHalfPlane hCore)

/-- The positive-half-plane paired-series theorem discharges the zero-height
    guard through the existing paired-boundary adapter. -/
def G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoPairedPositiveHalfPlane
    (hCore : G8EtaModTwoPairedEtaSeriesEqNegExpZetaOnPositiveHalfPlane) :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoPairedBoundary
    (g8EtaModTwoPairedExpZetaBoundaryOnOpenUnit_of_posHalfPlane hCore)

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A positive-half-plane point where the paired series is not summable
    refutes the positive-half-plane analytic payload. -/
structure G8EtaModTwoPairedEtaSeriesPositiveHalfPlaneSummabilityFailure where
  s : ℂ
  pos_re : 0 < s.re
  not_summable :
    ¬ Summable (fun n : ℕ => g8EtaModTwoPairedEtaTerm s n)

/-- A summability failure refutes the positive-half-plane paired-series
    payload. -/
theorem G8EtaModTwoPairedEtaSeriesPositiveHalfPlaneSummabilityFailure.refutes
    (w : G8EtaModTwoPairedEtaSeriesPositiveHalfPlaneSummabilityFailure)
    (hCore : G8EtaModTwoPairedEtaSeriesEqNegExpZetaOnPositiveHalfPlane) :
    False :=
  w.not_summable (hCore.summable w.s w.pos_re)

/-- A positive-half-plane point where the paired series value differs from
    `-expZeta` refutes the positive-half-plane analytic payload. -/
structure G8EtaModTwoPairedEtaSeriesPositiveHalfPlaneValueMismatch where
  s : ℂ
  pos_re : 0 < s.re
  mismatch :
    g8EtaModTwoPairedEtaSeries s ≠
      - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s

/-- A value mismatch refutes the positive-half-plane paired-series payload. -/
theorem G8EtaModTwoPairedEtaSeriesPositiveHalfPlaneValueMismatch.refutes
    (w : G8EtaModTwoPairedEtaSeriesPositiveHalfPlaneValueMismatch)
    (hCore : G8EtaModTwoPairedEtaSeriesEqNegExpZetaOnPositiveHalfPlane) :
    False :=
  w.mismatch (hCore.eq_neg_expZeta w.s w.pos_re)

/-- A pointwise paired-boundary mismatch refutes the positive-half-plane
    analytic payload through the theorem-backed adapter. -/
theorem G8EtaModTwoPairedExpZetaBoundaryMismatch.refutes_posHalfPlane
    (w : G8EtaModTwoPairedExpZetaBoundaryMismatch)
    (hCore : G8EtaModTwoPairedEtaSeriesEqNegExpZetaOnPositiveHalfPlane) :
    False :=
  w.refutes
    (g8EtaModTwoPairedExpZetaBoundaryOnOpenUnit_of_posHalfPlane hCore)

end Tau.BookIII.Bridge
