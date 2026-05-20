import TauLib.BookIII.Bridge.G8ActualXiZeroHeightAxisGuardCore

/-!
# TauLib.BookIII.Bridge.G8RiemannZetaOpenUnitEtaNonvanishing

Dirichlet-eta reduction for the real open-unit zero-height branch.

The zero-height guard is now reduced to the narrow classical target
`riemannZeta (x : ℂ) ≠ 0` for `0 < x < 1`.  This module records the
eta-sign route without pretending that Mathlib already supplies the full
analytic-continuation identity needed on the open unit interval.

The theorem-backed part here is now split into two pieces: the concrete
alternating eta series on `0 < x < 1` exists and has positive limit, and a
positive eta value plus the identity

`eta(x) = (1 - 2^(1-x)) * zeta(x)`

forces the real part of zeta to be negative on `0 < x < 1`, hence nonzero.
The remaining analytic-continuation bridge from this concrete eta series to
Mathlib's `riemannZeta` is kept as the named proof-carrying target.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped BigOperators Topology

-- ============================================================
-- LOCAL ETA TARGET
-- ============================================================

/-- The decreasing positive magnitudes in the real Dirichlet-eta series. -/
def g8DirichletEtaMagnitude (x : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (-x)

/-- The real Dirichlet-eta terms, indexed from `n = 0`. -/
def g8DirichletEtaTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * g8DirichletEtaMagnitude x n

/-- Partial sums of the concrete real Dirichlet-eta series. -/
def g8DirichletEtaPartial (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, g8DirichletEtaTerm x i

/-- On `0 < x`, the eta magnitudes are antitone. -/
theorem g8DirichletEtaMagnitude_antitone
    {x : ℝ} (hx0 : 0 < x) :
    Antitone (g8DirichletEtaMagnitude x) := by
  intro m n hmn
  unfold g8DirichletEtaMagnitude
  exact Real.rpow_le_rpow_of_nonpos (Nat.cast_add_one_pos m)
    (by
      have hmnR : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
      linarith)
    (by linarith)

/-- On `0 < x`, the eta magnitudes tend to zero. -/
theorem g8DirichletEtaMagnitude_tendsto_zero
    {x : ℝ} (hx0 : 0 < x) :
    Tendsto (g8DirichletEtaMagnitude x) atTop (𝓝 0) := by
  unfold g8DirichletEtaMagnitude
  exact (tendsto_rpow_neg_atTop hx0).comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      tendsto_natCast_atTop_atTop)

/-- The theorem-backed value of the concrete eta series at `x`. -/
structure G8DirichletEtaOpenUnitSeriesValue (x : ℝ) where
  etaValue : ℝ
  etaTendsto : Tendsto (g8DirichletEtaPartial x) atTop (𝓝 etaValue)

/-- The concrete eta series converges on `0 < x`. -/
theorem g8DirichletEtaOpenUnitSeriesValue_exists
    {x : ℝ} (hx0 : 0 < x) :
    Nonempty (G8DirichletEtaOpenUnitSeriesValue x) := by
  obtain ⟨l, hl⟩ :=
    (g8DirichletEtaMagnitude_antitone hx0).tendsto_alternating_series_of_tendsto_zero
      (g8DirichletEtaMagnitude_tendsto_zero hx0)
  exact ⟨{
    etaValue := l
    etaTendsto := by
      simpa [g8DirichletEtaPartial, g8DirichletEtaTerm] using hl
  }⟩

/-- A canonical noncomputable choice of the concrete eta series value. -/
noncomputable def g8DirichletEtaOpenUnitSeriesValue
    {x : ℝ} (hx0 : 0 < x) :
    G8DirichletEtaOpenUnitSeriesValue x :=
  Classical.choice (g8DirichletEtaOpenUnitSeriesValue_exists hx0)

/-- The first even partial sum of the eta series is `1 - 2^(-x)`. -/
theorem g8DirichletEta_first_even_partial
    (x : ℝ) :
    g8DirichletEtaPartial x (2 * 1) =
      1 - (2 : ℝ) ^ (-x) := by
  simp [g8DirichletEtaPartial, g8DirichletEtaTerm,
    g8DirichletEtaMagnitude, Finset.sum_range_succ, Real.one_rpow]
  ring_nf

/-- The concrete eta series value is positive on the open unit interval. -/
theorem G8DirichletEtaOpenUnitSeriesValue.etaPositive
    {x : ℝ} (series : G8DirichletEtaOpenUnitSeriesValue x)
    (hx0 : 0 < x) (_hx1 : x < 1) :
    0 < series.etaValue := by
  have hLower :=
    (g8DirichletEtaMagnitude_antitone hx0).alternating_series_le_tendsto
      series.etaTendsto 1
  have hSum :
      (∑ i ∈ Finset.range (2 * 1),
        (-1 : ℝ) ^ i * g8DirichletEtaMagnitude x i) =
        1 - (2 : ℝ) ^ (-x) := by
    simpa [g8DirichletEtaPartial, g8DirichletEtaTerm]
      using g8DirichletEta_first_even_partial x
  have hPow : (2 : ℝ) ^ (-x) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hPos : 0 < 1 - (2 : ℝ) ^ (-x) := by linarith
  rw [hSum] at hLower
  linarith

/-- The real denominator in the eta-zeta identity on the open unit interval. -/
def g8DirichletEtaDenominator (x : ℝ) : ℝ :=
  1 - (2 : ℝ) ^ (1 - x)

/-- On `0 < x < 1`, the eta-zeta denominator is strictly negative. -/
theorem g8DirichletEtaDenominator_neg
    {x : ℝ} (_hx0 : 0 < x) (hx1 : x < 1) :
    g8DirichletEtaDenominator x < 0 := by
  unfold g8DirichletEtaDenominator
  have hExp : 0 < 1 - x := sub_pos.mpr hx1
  have hPow : 1 < (2 : ℝ) ^ (1 - x) :=
    Real.one_lt_rpow (by norm_num) hExp
  linarith

/-- The eta-zeta denominator is nonzero on the open unit interval. -/
theorem g8DirichletEtaDenominator_ne_zero
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    g8DirichletEtaDenominator x ≠ 0 :=
  ne_of_lt (g8DirichletEtaDenominator_neg hx0 hx1)

/-- A pointwise eta witness for the classical open-unit proof route.

`etaValue` is kept abstract so this module does not need to build a new eta
function.  The load-bearing analytic target is the final identity field,
which is exactly the eta-zeta identity specialized to real `0 < x < 1` and
read through the real part of Mathlib's complex zeta. -/
structure G8DirichletEtaOpenUnitWitness (x : ℝ) where
  etaValue : ℝ
  etaPositive : 0 < etaValue
  zetaReal : (riemannZeta (x : ℂ)).im = 0
  etaZetaIdentity :
    (riemannZeta (x : ℂ)).re =
      etaValue / g8DirichletEtaDenominator x

/-- The named open-unit eta theorem target: eta positivity plus the eta-zeta
    identity at every real `0 < x < 1`.

This is data, not a mere proposition, because a pointwise witness carries the
actual eta value used in the sign computation. -/
structure G8DirichletEtaZetaAnalyticIdentityAtOpenUnit
    (x : ℝ) (series : G8DirichletEtaOpenUnitSeriesValue x) where
  zetaReal : (riemannZeta (x : ℂ)).im = 0
  etaZetaIdentity :
    (riemannZeta (x : ℂ)).re =
      series.etaValue / g8DirichletEtaDenominator x

/-- The named remaining analytic-continuation target on the real open unit
    interval: the concrete eta-series value agrees with the zeta readout. -/
abbrev G8DirichletEtaZetaIdentityOnOpenUnit : Prop :=
  ∀ (x : ℝ) (hx0 : 0 < x), x < 1 →
    G8DirichletEtaZetaAnalyticIdentityAtOpenUnit x
      (g8DirichletEtaOpenUnitSeriesValue (x := x) hx0)

/-- The theorem-backed eta series positivity plus the analytic identity produce
    the older pointwise eta witness consumed by the sign algebra. -/
def G8DirichletEtaZetaAnalyticIdentityAtOpenUnit.toWitness
    {x : ℝ} {series : G8DirichletEtaOpenUnitSeriesValue x}
    (hIdentity : G8DirichletEtaZetaAnalyticIdentityAtOpenUnit x series)
    (hx0 : 0 < x) (hx1 : x < 1) :
    G8DirichletEtaOpenUnitWitness x where
  etaValue := series.etaValue
  etaPositive := series.etaPositive hx0 hx1
  zetaReal := hIdentity.zetaReal
  etaZetaIdentity := hIdentity.etaZetaIdentity

/-- Extract the pointwise eta witness from the open-unit analytic identity. -/
def g8DirichletEtaOpenUnitWitness_of_etaIdentity
    (heta : G8DirichletEtaZetaIdentityOnOpenUnit)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    G8DirichletEtaOpenUnitWitness x :=
  (heta x hx0 hx1).toWitness hx0 hx1

-- ============================================================
-- SIGN ALGEBRA: ETA ROUTE TO ZETA NONVANISHING
-- ============================================================

/-- A pointwise eta witness forces the real part of zeta to be negative. -/
theorem G8DirichletEtaOpenUnitWitness.riemannZeta_re_neg
    {x : ℝ} (w : G8DirichletEtaOpenUnitWitness x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (riemannZeta (x : ℂ)).re < 0 := by
  rw [w.etaZetaIdentity]
  exact div_neg_of_pos_of_neg w.etaPositive
    (g8DirichletEtaDenominator_neg hx0 hx1)

/-- A pointwise eta witness gives zeta nonvanishing on the real open unit
    interval. -/
theorem G8DirichletEtaOpenUnitWitness.riemannZeta_ne_zero
    {x : ℝ} (w : G8DirichletEtaOpenUnitWitness x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 := by
  intro hZero
  have hReNeg := w.riemannZeta_re_neg hx0 hx1
  have hReZero : (riemannZeta (x : ℂ)).re = 0 := by
    simp [hZero]
  have hContr : (0 : ℝ) < 0 := by
    rw [hReZero] at hReNeg
    exact hReNeg
  exact (lt_irrefl (0 : ℝ)) hContr

/-- The eta theorem target is sufficient for the exact zeta open-unit
    nonvanishing theorem needed by the zero-height guard. -/
theorem g8RiemannZetaOpenUnitIntervalNonvanishing_of_etaIdentity
    (heta : G8DirichletEtaZetaIdentityOnOpenUnit) :
    G8RiemannZetaOpenUnitIntervalNonvanishing := by
  intro x hx0 hx1
  exact (g8DirichletEtaOpenUnitWitness_of_etaIdentity heta x hx0 hx1)
    |>.riemannZeta_ne_zero hx0 hx1

/-- The eta theorem target supplies open-unit `xi` nonvanishing. -/
theorem g8OrthodoxXiOpenUnitIntervalNonvanishing_of_etaIdentity
    (heta : G8DirichletEtaZetaIdentityOnOpenUnit) :
    G8OrthodoxXiOpenUnitIntervalNonvanishing :=
  g8OrthodoxXiOpenUnitIntervalNonvanishing_of_riemannZetaOpenUnit
    (g8RiemannZetaOpenUnitIntervalNonvanishing_of_etaIdentity heta)

/-- The eta theorem target is sufficient to discharge the zero-height guard. -/
def G8ActualXiZeroHeightAxisGuardDischarge.ofDirichletEtaIdentity
    (heta : G8DirichletEtaZetaIdentityOnOpenUnit) :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  G8ActualXiZeroHeightAxisGuardDischarge.ofRiemannZetaOpenUnit
    (g8RiemannZetaOpenUnitIntervalNonvanishing_of_etaIdentity heta)

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A point in the open unit interval where no eta witness exists refutes the
    eta theorem target. -/
structure G8DirichletEtaOpenUnitWitnessFailure where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  noWitness : ¬ Nonempty (G8DirichletEtaOpenUnitWitness x)

/-- Missing pointwise eta evidence refutes the global eta theorem target. -/
theorem G8DirichletEtaOpenUnitWitnessFailure.refutesEtaIdentity
    (w : G8DirichletEtaOpenUnitWitnessFailure)
    (heta : G8DirichletEtaZetaIdentityOnOpenUnit) :
    False :=
  w.noWitness
    ⟨g8DirichletEtaOpenUnitWitness_of_etaIdentity heta
      w.x w.pos w.lt_one⟩

/-- A point where the concrete eta series lacks the analytic zeta identity
    refutes the global open-unit eta-zeta identity target. -/
structure G8DirichletEtaZetaAnalyticIdentityFailure where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  noAnalyticIdentity :
    ¬ G8DirichletEtaZetaAnalyticIdentityAtOpenUnit x
      (g8DirichletEtaOpenUnitSeriesValue (x := x) pos)

/-- Missing analytic-continuation evidence refutes the eta identity target. -/
theorem G8DirichletEtaZetaAnalyticIdentityFailure.refutesEtaIdentity
    (w : G8DirichletEtaZetaAnalyticIdentityFailure)
    (heta : G8DirichletEtaZetaIdentityOnOpenUnit) :
    False :=
  w.noAnalyticIdentity (heta w.x w.pos w.lt_one)

/-- A real open-unit zeta zero refutes the eta theorem target through the
    sign algebra above. -/
structure G8RiemannZetaOpenUnitZeroFalsifier where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  zetaZero : riemannZeta (x : ℂ) = 0

/-- Open-unit zeta zero evidence refutes the eta theorem target. -/
theorem G8RiemannZetaOpenUnitZeroFalsifier.refutesEtaIdentity
    (w : G8RiemannZetaOpenUnitZeroFalsifier)
    (heta : G8DirichletEtaZetaIdentityOnOpenUnit) :
    False :=
  (g8RiemannZetaOpenUnitIntervalNonvanishing_of_etaIdentity heta)
    w.x w.pos w.lt_one w.zetaZero

end Tau.BookIII.Bridge
