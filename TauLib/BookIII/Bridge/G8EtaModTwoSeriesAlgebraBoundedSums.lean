import TauLib.BookIII.Bridge.G8RiemannZetaOpenUnitEtaLFunctionIdentity

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoSeriesAlgebraBoundedSums

Bounded mod-2 eta coefficient algebra for the Lane-A zero-height corridor.

The previous mod-2 L-function module isolates the two analytic identities still
needed on the real open unit interval.  This module closes the purely
arithmetic part: the mod-2 coefficients alternate, their signed partial sums
over positive integers are binary, and hence those ordinary partial sums are
`O(1)`.

The remaining bridge is deliberately conditional.  Mathlib's `LSeriesSummable`
is an absolute-convergence predicate, so it is not the right open-unit eta
series object.  We therefore name the conditional eta-series value explicitly
and prove that agreement with the mod-2 `LFunction` is exactly sufficient for
the existing series-identity target.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped BigOperators Topology

-- ============================================================
-- NATURAL MOD-2 COEFFICIENTS
-- ============================================================

/-- Natural-indexed wrapper for the mod-2 alternating coefficient. -/
def g8EtaModTwoNatCoeff (n : ℕ) : ℂ :=
  g8EtaModTwoCoeff (n : ZMod 2)

@[simp] theorem g8EtaModTwoNatCoeff_one :
    g8EtaModTwoNatCoeff 1 = 1 := by
  norm_num [g8EtaModTwoNatCoeff]

@[simp] theorem g8EtaModTwoNatCoeff_two :
    g8EtaModTwoNatCoeff 2 = -1 := by
  change g8EtaModTwoCoeff (((2 : ℕ) : ZMod 2)) = -1
  rw [ZMod.natCast_self]
  simp

/-- Even positive indices carry the negative eta coefficient. -/
theorem g8EtaModTwoNatCoeff_of_even
    {n : ℕ} (h : Even n) :
    g8EtaModTwoNatCoeff n = -1 := by
  unfold g8EtaModTwoNatCoeff
  rw [(ZMod.natCast_eq_zero_iff_even).mpr h]
  simp

/-- Odd positive indices carry the positive eta coefficient. -/
theorem g8EtaModTwoNatCoeff_of_odd
    {n : ℕ} (h : Odd n) :
    g8EtaModTwoNatCoeff n = 1 := by
  unfold g8EtaModTwoNatCoeff
  rw [(ZMod.natCast_eq_one_iff_odd).mpr h]
  simp

/-- The mod-2 natural coefficient is two-periodic. -/
theorem g8EtaModTwoNatCoeff_add_two (n : ℕ) :
    g8EtaModTwoNatCoeff (n + 2) = g8EtaModTwoNatCoeff n := by
  have hper : (((n + 2 : ℕ) : ZMod 2) = (n : ZMod 2)) := by
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := ZMod.natCast_self 2
    simpa [Nat.cast_add, h2]
  simp [g8EtaModTwoNatCoeff, hper]

/-- Shifted by one, the mod-2 coefficient is the usual eta sign. -/
theorem g8EtaModTwoNatCoeff_succ_eq_pow (n : ℕ) :
    g8EtaModTwoNatCoeff (n + 1) = (-1 : ℂ) ^ n := by
  rcases Nat.even_or_odd n with hEven | hOdd
  · have hOddSucc : Odd (n + 1) := by
      rcases hEven with ⟨m, hm⟩
      use m
      omega
    rw [g8EtaModTwoNatCoeff_of_odd hOddSucc]
    exact (hEven.neg_one_pow : (-1 : ℂ) ^ n = 1).symm
  · have hEvenSucc : Even (n + 1) := by
      rcases hOdd with ⟨m, hm⟩
      use m + 1
      omega
    rw [g8EtaModTwoNatCoeff_of_even hEvenSucc]
    exact (hOdd.neg_one_pow : (-1 : ℂ) ^ n = -1).symm

-- ============================================================
-- BOUNDED ORDINARY PARTIAL SUMS
-- ============================================================

/-- Signed positive-index partial sums of the mod-2 eta coefficient. -/
def g8EtaModTwoPartialSum (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 n, g8EtaModTwoNatCoeff k

/-- Even/odd closed form for positive-index mod-2 coefficient sums. -/
theorem g8EtaModTwoPartialSum_even_odd (m : ℕ) :
    g8EtaModTwoPartialSum (2 * m) = 0 ∧
      g8EtaModTwoPartialSum (2 * m + 1) = 1 := by
  induction m with
  | zero =>
      constructor <;> simp [g8EtaModTwoPartialSum, g8EtaModTwoNatCoeff]
  | succ m ih =>
      rcases ih with ⟨_heven, hodd⟩
      have hevenSucc :
          g8EtaModTwoPartialSum (2 * Nat.succ m) = 0 := by
        rw [show 2 * Nat.succ m = 2 * m + 1 + 1 by omega]
        change
          (∑ k ∈ Finset.Icc 1 (2 * m + 1 + 1),
            g8EtaModTwoNatCoeff k) = 0
        rw [Finset.sum_Icc_succ_top
          (by omega : 1 ≤ 2 * m + 1 + 1)]
        change
          g8EtaModTwoPartialSum (2 * m + 1) +
            g8EtaModTwoNatCoeff (2 * m + 1 + 1) = 0
        rw [hodd]
        have he : Even (2 * m + 1 + 1) := by
          use m + 1
          omega
        rw [g8EtaModTwoNatCoeff_of_even he]
        norm_num
      constructor
      · exact hevenSucc
      · change
          (∑ k ∈ Finset.Icc 1 (2 * Nat.succ m + 1),
            g8EtaModTwoNatCoeff k) = 1
        rw [Finset.sum_Icc_succ_top
          (by omega : 1 ≤ 2 * Nat.succ m + 1)]
        change
          g8EtaModTwoPartialSum (2 * Nat.succ m) +
            g8EtaModTwoNatCoeff (2 * Nat.succ m + 1) = 1
        rw [hevenSucc]
        have ho : Odd (2 * Nat.succ m + 1) := by
          use Nat.succ m
        rw [g8EtaModTwoNatCoeff_of_odd ho]
        norm_num

/-- Every signed positive-index mod-2 partial sum is either `0` or `1`. -/
theorem g8EtaModTwoPartialSum_eq_zero_or_one (n : ℕ) :
    g8EtaModTwoPartialSum n = 0 ∨
      g8EtaModTwoPartialSum n = 1 := by
  rcases Nat.even_or_odd n with hEven | hOdd
  · rcases hEven with ⟨m, hm⟩
    left
    have hn : n = 2 * m := by omega
    rw [hn]
    exact (g8EtaModTwoPartialSum_even_odd m).1
  · rcases hOdd with ⟨m, hm⟩
    right
    have hn : n = 2 * m + 1 := by omega
    rw [hn]
    exact (g8EtaModTwoPartialSum_even_odd m).2

/-- The ordinary signed partial sums are bounded by one. -/
theorem g8EtaModTwoPartialSum_norm_le_one (n : ℕ) :
    ‖g8EtaModTwoPartialSum n‖ ≤ 1 := by
  rcases g8EtaModTwoPartialSum_eq_zero_or_one n with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- The ordinary signed partial sums are `O(1)`. -/
theorem g8EtaModTwoPartialSum_isBigO_one :
    (fun n : ℕ => g8EtaModTwoPartialSum n) =O[atTop]
      (fun _n : ℕ => (1 : ℂ)) := by
  exact Asymptotics.IsBigO.of_bound 1
    (Eventually.of_forall fun n => by
      simpa using g8EtaModTwoPartialSum_norm_le_one n)

-- ============================================================
-- CONDITIONAL NAIVE ETA SERIES BRIDGE
-- ============================================================

/-- Conditional eta partial sums built from the natural mod-2 coefficient.

This is the conditional series object, not Mathlib's absolute-convergence
`LSeries`. -/
def g8EtaModTwoNaiveConditionalPartial (x : ℝ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n,
    g8EtaModTwoNatCoeff (k + 1) *
      (g8DirichletEtaMagnitude x k : ℂ)

/-- Real part of the complex eta sign. -/
theorem g8EtaModTwo_negOnePow_re (n : ℕ) :
    ((-1 : ℂ) ^ n).re = (-1 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      simp [ih]

/-- Imaginary part of the complex eta sign. -/
theorem g8EtaModTwo_negOnePow_im (n : ℕ) :
    ((-1 : ℂ) ^ n).im = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      simp [ih]

/-- The mod-2 conditional partial sums are exactly the complexification of the
    concrete real eta partial sums already used by the zero-height corridor. -/
theorem g8EtaModTwoNaiveConditionalPartial_eq_concreteEtaPartial
    (x : ℝ) (n : ℕ) :
    g8EtaModTwoNaiveConditionalPartial x n =
      (g8DirichletEtaPartial x n : ℂ) := by
  simp [g8EtaModTwoNaiveConditionalPartial, g8DirichletEtaPartial,
    g8DirichletEtaTerm, g8EtaModTwoNatCoeff_succ_eq_pow]

/-- Real-part selector for the theorem-backed partial-sum identification. -/
theorem g8EtaModTwoNaiveConditionalPartial_re
    (x : ℝ) (n : ℕ) :
    (g8EtaModTwoNaiveConditionalPartial x n).re =
      g8DirichletEtaPartial x n := by
  rw [g8EtaModTwoNaiveConditionalPartial_eq_concreteEtaPartial]
  simp

/-- Imaginary-part selector for the theorem-backed partial-sum identification. -/
theorem g8EtaModTwoNaiveConditionalPartial_im
    (x : ℝ) (n : ℕ) :
    (g8EtaModTwoNaiveConditionalPartial x n).im = 0 := by
  rw [g8EtaModTwoNaiveConditionalPartial_eq_concreteEtaPartial]
  simp

/-- The exact named conditional-summability target for the naive eta series on
    the open right half-line. -/
structure G8EtaModTwoNaiveConditionalSeriesValue (x : ℝ) where
  value : ℂ
  partialTendsto :
    Tendsto (g8EtaModTwoNaiveConditionalPartial x) atTop (𝓝 value)

/-- Open-right-half-plane conditional convergence target for the naive eta
    partial sums.  This is intentionally not Mathlib's `LSeriesSummable`,
    which is absolute convergence. -/
abbrev G8EtaModTwoNaiveLSeriesSummableOnOpenRightHalfPlane : Prop :=
  ∀ (x : ℝ), 0 < x →
    Nonempty (G8EtaModTwoNaiveConditionalSeriesValue x)

/-- A proof-carrying bridge saying the conditional naive eta series agrees
    with the concrete eta value already used by the zero-height corridor. -/
structure G8EtaModTwoNaiveLSeriesAgreesWithConcreteEtaOnOpenUnit where
  naiveSeries :
    ∀ (x : ℝ), 0 < x → x < 1 →
      G8EtaModTwoNaiveConditionalSeriesValue x
  naiveRe_eq_etaValue :
    ∀ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1),
      ((naiveSeries x hx0 hx1).value).re =
        (g8DirichletEtaOpenUnitSeriesValue (x := x) hx0).etaValue
  naiveIm_eq_zero :
    ∀ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1),
      ((naiveSeries x hx0 hx1).value).im = 0

/-- The concrete-agreement bridge supplies conditional convergence on the
    open right half-line segment needed by the open-unit corridor. -/
theorem G8EtaModTwoNaiveLSeriesAgreesWithConcreteEtaOnOpenUnit.summableOpenUnit
    (hNaive : G8EtaModTwoNaiveLSeriesAgreesWithConcreteEtaOnOpenUnit)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Nonempty (G8EtaModTwoNaiveConditionalSeriesValue x) :=
  ⟨hNaive.naiveSeries x hx0 hx1⟩

/-- The remaining series-identification target: the mod-2 L-function agrees
    with the conditional naive eta-series value on the real open unit
    interval. -/
abbrev G8EtaModTwoLFunctionEqualsNaiveLSeriesOnOpenUnit
    (hNaive : G8EtaModTwoNaiveLSeriesAgreesWithConcreteEtaOnOpenUnit) :
    Prop :=
  ∀ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1),
    g8EtaModTwoLFunction (x : ℂ) =
      (hNaive.naiveSeries x hx0 hx1).value

/-- Conditional naive-series agreement plus L-function agreement gives the
    existing mod-2 series identity target. -/
theorem g8EtaModTwoLFunctionSeriesIdentityOnOpenUnit_of_naiveLSeries
    (hNaive : G8EtaModTwoNaiveLSeriesAgreesWithConcreteEtaOnOpenUnit)
    (hLFunction :
      G8EtaModTwoLFunctionEqualsNaiveLSeriesOnOpenUnit hNaive) :
    G8EtaModTwoLFunctionSeriesIdentityOnOpenUnit := by
  intro x hx0 hx1
  exact {
    lFunctionRe_eq_etaValue := by
      rw [hLFunction x hx0 hx1]
      exact hNaive.naiveRe_eq_etaValue x hx0 hx1
    lFunctionIm_eq_zero := by
      rw [hLFunction x hx0 hx1]
      exact hNaive.naiveIm_eq_zero x hx0 hx1
  }

/-- Product identity plus the conditional series bridge imply the eta-zeta
    identity needed by the previous zero-height module. -/
theorem g8DirichletEtaZetaIdentityOnOpenUnit_of_etaModTwoNaiveLSeries
    (hProduct : G8EtaModTwoLFunctionProductIdentityOnOpenUnit)
    (hNaive : G8EtaModTwoNaiveLSeriesAgreesWithConcreteEtaOnOpenUnit)
    (hLFunction :
      G8EtaModTwoLFunctionEqualsNaiveLSeriesOnOpenUnit hNaive) :
    G8DirichletEtaZetaIdentityOnOpenUnit :=
  g8DirichletEtaZetaIdentityOnOpenUnit_of_etaModTwoLFunction
    hProduct
    (g8EtaModTwoLFunctionSeriesIdentityOnOpenUnit_of_naiveLSeries
      hNaive hLFunction)

/-- Product identity plus the conditional series bridge imply open-unit zeta
    nonvanishing. -/
theorem g8RiemannZetaOpenUnitIntervalNonvanishing_of_etaModTwoNaiveLSeries
    (hProduct : G8EtaModTwoLFunctionProductIdentityOnOpenUnit)
    (hNaive : G8EtaModTwoNaiveLSeriesAgreesWithConcreteEtaOnOpenUnit)
    (hLFunction :
      G8EtaModTwoLFunctionEqualsNaiveLSeriesOnOpenUnit hNaive) :
    G8RiemannZetaOpenUnitIntervalNonvanishing :=
  g8RiemannZetaOpenUnitIntervalNonvanishing_of_etaIdentity
    (g8DirichletEtaZetaIdentityOnOpenUnit_of_etaModTwoNaiveLSeries
      hProduct hNaive hLFunction)

/-- Product identity plus the conditional series bridge discharge the
    zero-height guard. -/
def G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoNaiveLSeries
    (hProduct : G8EtaModTwoLFunctionProductIdentityOnOpenUnit)
    (hNaive : G8EtaModTwoNaiveLSeriesAgreesWithConcreteEtaOnOpenUnit)
    (hLFunction :
      G8EtaModTwoLFunctionEqualsNaiveLSeriesOnOpenUnit hNaive) :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  G8ActualXiZeroHeightAxisGuardDischarge.ofDirichletEtaIdentity
    (g8DirichletEtaZetaIdentityOnOpenUnit_of_etaModTwoNaiveLSeries
      hProduct hNaive hLFunction)

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A bounded-sum falsifier would be a positive-index partial sum exceeding
    the theorem-backed bound `1`. -/
structure G8EtaModTwoPartialSumsExceedOne where
  n : ℕ
  exceeds : 1 < ‖g8EtaModTwoPartialSum n‖

/-- The theorem-backed bounded-sum lemma refutes any exceed-one witness. -/
theorem G8EtaModTwoPartialSumsExceedOne.refutes
    (w : G8EtaModTwoPartialSumsExceedOne) :
    False :=
  not_lt_of_ge (g8EtaModTwoPartialSum_norm_le_one w.n) w.exceeds

/-- Missing agreement between the conditional naive eta series and the
    concrete eta value refutes the concrete-agreement target. -/
structure G8EtaModTwoNaiveConcreteSeriesMismatch where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  noAgreement :
    G8EtaModTwoNaiveLSeriesAgreesWithConcreteEtaOnOpenUnit → False

/-- A concrete-series mismatch refutes any supplied concrete-agreement bridge. -/
theorem G8EtaModTwoNaiveConcreteSeriesMismatch.refutesNaiveAgreement
    (w : G8EtaModTwoNaiveConcreteSeriesMismatch)
    (hNaive : G8EtaModTwoNaiveLSeriesAgreesWithConcreteEtaOnOpenUnit) :
    False :=
  w.noAgreement hNaive

/-- A point where the mod-2 L-function does not equal the conditional naive
    eta value refutes the L-function/series bridge. -/
structure G8EtaModTwoLFunctionNaiveSeriesMismatch
    (hNaive : G8EtaModTwoNaiveLSeriesAgreesWithConcreteEtaOnOpenUnit) where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  mismatch :
    g8EtaModTwoLFunction (x : ℂ) ≠
      (hNaive.naiveSeries x pos lt_one).value

/-- A pointwise L-function/series mismatch refutes the global bridge. -/
theorem G8EtaModTwoLFunctionNaiveSeriesMismatch.refutesLFunctionBridge
    {hNaive : G8EtaModTwoNaiveLSeriesAgreesWithConcreteEtaOnOpenUnit}
    (w : G8EtaModTwoLFunctionNaiveSeriesMismatch hNaive)
    (hLFunction :
      G8EtaModTwoLFunctionEqualsNaiveLSeriesOnOpenUnit hNaive) :
    False :=
  w.mismatch (hLFunction w.x w.pos w.lt_one)

end Tau.BookIII.Bridge
