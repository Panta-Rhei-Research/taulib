import TauLib.BookIII.Bridge.G8EtaModTwoSeriesAlgebraBoundedSums

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoConditionalSeriesProductBridge

Conditional eta-series and safe half-plane product bridge for Lane A.

The bounded-sums module proves the mod-two coefficient algebra and isolates
the conditional eta-series value.  This module discharges the concrete
conditional-series agreement with the existing real eta value, proves the
Mathlib-backed half-plane equality between `ZMod.LFunction` and the ordinary
`LSeries`, and names the remaining analytic product/continuation payloads.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped BigOperators Topology

-- ============================================================
-- CONCRETE CONDITIONAL ETA AGREEMENT
-- ============================================================

/-- The naive conditional mod-two eta series is already the concrete real eta
    series, transported through `ℝ → ℂ`. -/
def g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit :
    G8EtaModTwoNaiveLSeriesAgreesWithConcreteEtaOnOpenUnit where
  naiveSeries := fun x hx0 _hx1 => {
    value := ((g8DirichletEtaOpenUnitSeriesValue (x := x) hx0).etaValue : ℂ)
    partialTendsto := by
      have hReal :
          Tendsto (g8DirichletEtaPartial x) atTop
            (𝓝 (g8DirichletEtaOpenUnitSeriesValue (x := x) hx0).etaValue) :=
        (g8DirichletEtaOpenUnitSeriesValue (x := x) hx0).etaTendsto
      have hComplex :
          Tendsto (fun n : ℕ => (g8DirichletEtaPartial x n : ℂ)) atTop
            (𝓝 ((g8DirichletEtaOpenUnitSeriesValue (x := x) hx0).etaValue : ℂ)) :=
        Filter.tendsto_ofReal_iff.mpr hReal
      exact hComplex.congr'
        (Eventually.of_forall fun n =>
          (g8EtaModTwoNaiveConditionalPartial_eq_concreteEtaPartial x n).symm)
  }
  naiveRe_eq_etaValue := by
    intro x hx0 hx1
    simp
  naiveIm_eq_zero := by
    intro x hx0 hx1
    simp

/-- Open-unit conditional convergence follows theorem-backed from the concrete
    eta convergence proof. -/
theorem g8EtaModTwoNaiveConditionalSeriesValue_exists_openUnit
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Nonempty (G8EtaModTwoNaiveConditionalSeriesValue x) :=
  g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.summableOpenUnit
    x hx0 hx1

-- ============================================================
-- SAFE HALF-PLANE L-FUNCTION FACTS
-- ============================================================

/-- On `1 < Re(s)`, the natural mod-two coefficient has an absolutely
    convergent Mathlib L-series.  This is the safe half-plane only. -/
theorem g8EtaModTwoNatCoeff_LSeriesSummable_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable g8EtaModTwoNatCoeff s := by
  simpa [g8EtaModTwoNatCoeff] using
    (ZMod.LSeriesSummable_of_one_lt_re g8EtaModTwoCoeff (s := s) hs)

/-- On `1 < Re(s)`, Mathlib's `ZMod.LFunction` agrees with the ordinary
    `LSeries` of the natural mod-two coefficient. -/
theorem g8EtaModTwoLFunction_eq_LSeries_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    g8EtaModTwoLFunction s = LSeries g8EtaModTwoNatCoeff s := by
  simpa [g8EtaModTwoLFunction, g8EtaModTwoNatCoeff] using
    (ZMod.LFunction_eq_LSeries g8EtaModTwoCoeff (s := s) hs)

/-- Odd/even paired coefficient readout, the sign convention consumed by the
    eta product algebra. -/
theorem g8EtaModTwoNatCoeff_odd_even_pair (m : ℕ) :
    g8EtaModTwoNatCoeff (2 * m + 1) = 1 ∧
      g8EtaModTwoNatCoeff (2 * m + 2) = -1 := by
  constructor
  · exact g8EtaModTwoNatCoeff_of_odd ⟨m, by omega⟩
  · exact g8EtaModTwoNatCoeff_of_even ⟨m + 1, by omega⟩

-- ============================================================
-- RIGHT-HALF-PLANE PRODUCT STAGING
-- ============================================================

/-- The exact ordinary `LSeries` product identity still needed on the safe
    half-plane.  This is the series-algebra form of
    `η(s) = (1 - 2^(1-s)) ζ(s)` for `1 < Re(s)`. -/
structure G8EtaModTwoLSeriesProductIdentityAtRightHalfPlane
    (s : ℂ) where
  productIdentity :
    LSeries g8EtaModTwoNatCoeff s =
      (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/-- Global safe-half-plane ordinary `LSeries` product target. -/
abbrev G8EtaModTwoLSeriesProductIdentityOnRightHalfPlane : Prop :=
  ∀ (s : ℂ), 1 < s.re →
    G8EtaModTwoLSeriesProductIdentityAtRightHalfPlane s

/-- The corresponding safe-half-plane product identity for the mod-two
    L-function. -/
structure G8EtaModTwoLFunctionProductIdentityAtRightHalfPlane
    (s : ℂ) where
  productIdentity :
    g8EtaModTwoLFunction s =
      (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/-- Global safe-half-plane mod-two L-function product target. -/
abbrev G8EtaModTwoLFunctionProductIdentityOnRightHalfPlane : Prop :=
  ∀ (s : ℂ), 1 < s.re →
    G8EtaModTwoLFunctionProductIdentityAtRightHalfPlane s

/-- The ordinary `LSeries` product identity implies the L-function product
    identity on the safe half-plane by Mathlib's `ZMod.LFunction_eq_LSeries`. -/
theorem g8EtaModTwoLFunctionProductIdentityOnRightHalfPlane_of_LSeriesProduct
    (hProduct : G8EtaModTwoLSeriesProductIdentityOnRightHalfPlane) :
    G8EtaModTwoLFunctionProductIdentityOnRightHalfPlane := by
  intro s hs
  exact {
    productIdentity := by
      rw [g8EtaModTwoLFunction_eq_LSeries_of_one_lt_re hs]
      exact (hProduct s hs).productIdentity
  }

-- ============================================================
-- CONTINUATION TO THE OPEN UNIT
-- ============================================================

/-- Proof-carrying analytic continuation bridge from the safe half-plane
    product identity to the real open-unit product identity consumed by the
    zero-height corridor. -/
structure G8EtaModTwoProductContinuationToOpenUnit
    (hRight : G8EtaModTwoLFunctionProductIdentityOnRightHalfPlane) where
  zetaReal :
    ∀ (x : ℝ), 0 < x → x < 1 →
      (riemannZeta (x : ℂ)).im = 0
  openUnitProduct :
    ∀ (x : ℝ), 0 < x → x < 1 →
      g8EtaModTwoLFunction (x : ℂ) =
        (g8DirichletEtaDenominator x : ℂ) * riemannZeta (x : ℂ)

/-- The continuation bridge supplies the existing open-unit product target. -/
theorem G8EtaModTwoProductContinuationToOpenUnit.toOpenUnitProduct
    {hRight : G8EtaModTwoLFunctionProductIdentityOnRightHalfPlane}
    (hContinuation : G8EtaModTwoProductContinuationToOpenUnit hRight) :
    G8EtaModTwoLFunctionProductIdentityOnOpenUnit := by
  intro x hx0 hx1
  exact {
    zetaReal := hContinuation.zetaReal x hx0 hx1
    productIdentity := hContinuation.openUnitProduct x hx0 hx1
  }

/-- With concrete eta agreement discharged, the remaining open-unit
    L-function/series identity can be stated without an extra parameter. -/
abbrev G8EtaModTwoLFunctionEqualsConcreteEtaOnOpenUnit : Prop :=
  G8EtaModTwoLFunctionEqualsNaiveLSeriesOnOpenUnit
    g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit

/-- Product continuation plus the concrete L-function/eta identity imply the
    eta-zeta identity used by the zero-height proof. -/
theorem g8DirichletEtaZetaIdentityOnOpenUnit_of_etaModTwoContinuation
    {hRight : G8EtaModTwoLFunctionProductIdentityOnRightHalfPlane}
    (hContinuation : G8EtaModTwoProductContinuationToOpenUnit hRight)
    (hLFunction : G8EtaModTwoLFunctionEqualsConcreteEtaOnOpenUnit) :
    G8DirichletEtaZetaIdentityOnOpenUnit :=
  g8DirichletEtaZetaIdentityOnOpenUnit_of_etaModTwoNaiveLSeries
    hContinuation.toOpenUnitProduct
    g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit
    hLFunction

/-- Product continuation plus the concrete L-function/eta identity imply
    open-unit zeta nonvanishing. -/
theorem g8RiemannZetaOpenUnitIntervalNonvanishing_of_etaModTwoContinuation
    {hRight : G8EtaModTwoLFunctionProductIdentityOnRightHalfPlane}
    (hContinuation : G8EtaModTwoProductContinuationToOpenUnit hRight)
    (hLFunction : G8EtaModTwoLFunctionEqualsConcreteEtaOnOpenUnit) :
    G8RiemannZetaOpenUnitIntervalNonvanishing :=
  g8RiemannZetaOpenUnitIntervalNonvanishing_of_etaIdentity
    (g8DirichletEtaZetaIdentityOnOpenUnit_of_etaModTwoContinuation
      hContinuation hLFunction)

/-- Product continuation plus the concrete L-function/eta identity discharge
    the zero-height axis guard. -/
def G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoContinuation
    {hRight : G8EtaModTwoLFunctionProductIdentityOnRightHalfPlane}
    (hContinuation : G8EtaModTwoProductContinuationToOpenUnit hRight)
    (hLFunction : G8EtaModTwoLFunctionEqualsConcreteEtaOnOpenUnit) :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  G8ActualXiZeroHeightAxisGuardDischarge.ofDirichletEtaIdentity
    (g8DirichletEtaZetaIdentityOnOpenUnit_of_etaModTwoContinuation
      hContinuation hLFunction)

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A point where the ordinary `LSeries` product formula fails refutes the
    safe-half-plane product target. -/
structure G8EtaModTwoLSeriesProductRightHalfPlaneMismatch where
  s : ℂ
  halfPlane : 1 < s.re
  mismatch :
    LSeries g8EtaModTwoNatCoeff s ≠
      (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/-- A safe-half-plane product mismatch refutes the ordinary product target. -/
theorem G8EtaModTwoLSeriesProductRightHalfPlaneMismatch.refutes
    (w : G8EtaModTwoLSeriesProductRightHalfPlaneMismatch)
    (hProduct : G8EtaModTwoLSeriesProductIdentityOnRightHalfPlane) :
    False :=
  w.mismatch (hProduct w.s w.halfPlane).productIdentity

/-- A point where continuation fails to give the open-unit product identity
    refutes the continuation bridge. -/
structure G8EtaModTwoProductContinuationOpenUnitMismatch
    (hRight : G8EtaModTwoLFunctionProductIdentityOnRightHalfPlane) where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  mismatch :
    g8EtaModTwoLFunction (x : ℂ) ≠
      (g8DirichletEtaDenominator x : ℂ) * riemannZeta (x : ℂ)

/-- An open-unit continuation mismatch refutes any supplied continuation
    bridge. -/
theorem G8EtaModTwoProductContinuationOpenUnitMismatch.refutes
    {hRight : G8EtaModTwoLFunctionProductIdentityOnRightHalfPlane}
    (w : G8EtaModTwoProductContinuationOpenUnitMismatch hRight)
    (hContinuation : G8EtaModTwoProductContinuationToOpenUnit hRight) :
    False :=
  w.mismatch (hContinuation.openUnitProduct w.x w.pos w.lt_one)

end Tau.BookIII.Bridge
