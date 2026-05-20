import TauLib.BookIII.Bridge.G8RiemannZetaOpenUnitEtaNonvanishing

/-!
# TauLib.BookIII.Bridge.G8RiemannZetaOpenUnitEtaLFunctionIdentity

Mod-2 L-function bridge for the Lane-A real open-unit eta target.

The previous eta module proves the concrete alternating eta series exists and
is positive on `0 < x < 1`, then reduces the zero-height guard to the
eta-zeta identity on that interval.  This module sharpens the remaining
classical-analysis payload by naming the two exact L-function identities still
needed:

* the mod-2 alternating L-function has the expected zeta-product readout;
* that L-function agrees with the concrete alternating eta series value.

Both are proof-carrying inputs here.  The theorem-backed part is the mod-2
character, its zero-average/differentiability selectors, and the adapter from
those two identities into the existing zero-height guard corridor.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped BigOperators Topology

-- ============================================================
-- MOD-2 ALTERNATING L-FUNCTION
-- ============================================================

/-- The mod-2 alternating coefficient used for the eta L-function.

`LSeries.term` starts at `n = 1` because its `n = 0` term is zero.  With this
choice, the coefficient on `n + 1` matches the concrete eta sign
`(-1)^n`: odd positive integers carry `+1`, even positive integers carry
`-1`. -/
def g8EtaModTwoCoeff : ZMod 2 → ℂ :=
  fun j => if j = 0 then (-1 : ℂ) else 1

@[simp] theorem g8EtaModTwoCoeff_zero :
    g8EtaModTwoCoeff (0 : ZMod 2) = -1 := by
  simp [g8EtaModTwoCoeff]

@[simp] theorem g8EtaModTwoCoeff_one :
    g8EtaModTwoCoeff (1 : ZMod 2) = 1 := by
  norm_num [g8EtaModTwoCoeff]

/-- The mod-2 alternating coefficient has zero average, so Mathlib's
    continuation API gives a globally differentiable L-function. -/
theorem g8EtaModTwoCoeff_sum_zero :
    (∑ j : ZMod 2, g8EtaModTwoCoeff j) = 0 := by
  rw [← (ZMod.finEquiv 2).toEquiv.sum_comp g8EtaModTwoCoeff]
  rw [Fin.sum_univ_two]
  norm_num [g8EtaModTwoCoeff, ZMod.finEquiv]

/-- The mod-2 alternating L-function. -/
def g8EtaModTwoLFunction (s : ℂ) : ℂ :=
  ZMod.LFunction g8EtaModTwoCoeff s

/-- The mod-2 alternating L-function is differentiable because its coefficient
    has zero average. -/
theorem g8EtaModTwoLFunction_differentiable :
    Differentiable ℂ g8EtaModTwoLFunction := by
  unfold g8EtaModTwoLFunction
  exact ZMod.differentiable_LFunction_of_sum_zero
    g8EtaModTwoCoeff_sum_zero

/-- Pointwise differentiability selector for the mod-2 eta L-function. -/
theorem g8EtaModTwoLFunction_differentiableAt (s : ℂ) :
    DifferentiableAt ℂ g8EtaModTwoLFunction s :=
  g8EtaModTwoLFunction_differentiable.differentiableAt

-- ============================================================
-- OPEN-UNIT IDENTITY TARGETS
-- ============================================================

/-- The real-axis product identity target for the mod-2 eta L-function.

This is the real-open-unit specialization of the expected identity
`η(s) = (1 - 2^(1-s)) ζ(s)`, expressed with the real denominator already used
by the sign algebra in `G8RiemannZetaOpenUnitEtaNonvanishing`. -/
structure G8EtaModTwoLFunctionProductIdentityAtOpenUnit
    (x : ℝ) where
  zetaReal : (riemannZeta (x : ℂ)).im = 0
  productIdentity :
    g8EtaModTwoLFunction (x : ℂ) =
      (g8DirichletEtaDenominator x : ℂ) * riemannZeta (x : ℂ)

/-- The global open-unit product identity target. -/
abbrev G8EtaModTwoLFunctionProductIdentityOnOpenUnit : Prop :=
  ∀ (x : ℝ), 0 < x → x < 1 →
    G8EtaModTwoLFunctionProductIdentityAtOpenUnit x

/-- The open-unit series identity target connecting the mod-2 L-function to
    the concrete alternating eta series value already proved positive. -/
structure G8EtaModTwoLFunctionSeriesIdentityAtOpenUnit
    (x : ℝ) (series : G8DirichletEtaOpenUnitSeriesValue x) where
  lFunctionRe_eq_etaValue :
    (g8EtaModTwoLFunction (x : ℂ)).re = series.etaValue
  lFunctionIm_eq_zero :
    (g8EtaModTwoLFunction (x : ℂ)).im = 0

/-- The global open-unit series identity target. -/
abbrev G8EtaModTwoLFunctionSeriesIdentityOnOpenUnit : Prop :=
  ∀ (x : ℝ) (hx0 : 0 < x), x < 1 →
    G8EtaModTwoLFunctionSeriesIdentityAtOpenUnit x
      (g8DirichletEtaOpenUnitSeriesValue (x := x) hx0)

/-- The product identity gives the real-part equation consumed by the sign
    algebra. -/
theorem G8EtaModTwoLFunctionProductIdentityAtOpenUnit.productRe
    {x : ℝ}
    (hProduct : G8EtaModTwoLFunctionProductIdentityAtOpenUnit x) :
    (g8EtaModTwoLFunction (x : ℂ)).re =
      g8DirichletEtaDenominator x * (riemannZeta (x : ℂ)).re := by
  rw [hProduct.productIdentity]
  simp

/-- Product identity plus series identity produce the pointwise eta-zeta
    analytic identity needed by the previous module. -/
def G8DirichletEtaZetaAnalyticIdentityAtOpenUnit.ofEtaModTwoLFunction
    {x : ℝ} {series : G8DirichletEtaOpenUnitSeriesValue x}
    (hx0 : 0 < x) (hx1 : x < 1)
    (hProduct : G8EtaModTwoLFunctionProductIdentityAtOpenUnit x)
    (hSeries : G8EtaModTwoLFunctionSeriesIdentityAtOpenUnit x series) :
    G8DirichletEtaZetaAnalyticIdentityAtOpenUnit x series where
  zetaReal := hProduct.zetaReal
  etaZetaIdentity := by
    have hDen : g8DirichletEtaDenominator x ≠ 0 :=
      g8DirichletEtaDenominator_ne_zero hx0 hx1
    have hMul :
        g8DirichletEtaDenominator x *
            (riemannZeta (x : ℂ)).re =
          series.etaValue := by
      rw [← hProduct.productRe, hSeries.lFunctionRe_eq_etaValue]
    rw [← hMul]
    field_simp [hDen]

/-- The two L-function identity targets are exactly sufficient for the
    existing open-unit eta-zeta identity target. -/
theorem g8DirichletEtaZetaIdentityOnOpenUnit_of_etaModTwoLFunction
    (hProduct : G8EtaModTwoLFunctionProductIdentityOnOpenUnit)
    (hSeries : G8EtaModTwoLFunctionSeriesIdentityOnOpenUnit) :
    G8DirichletEtaZetaIdentityOnOpenUnit := by
  intro x hx0 hx1
  exact G8DirichletEtaZetaAnalyticIdentityAtOpenUnit.ofEtaModTwoLFunction
    hx0 hx1 (hProduct x hx0 hx1) (hSeries x hx0 hx1)

-- ============================================================
-- ADAPTERS INTO THE ZERO-HEIGHT CORRIDOR
-- ============================================================

/-- Product plus series identity imply open-unit zeta nonvanishing. -/
theorem g8RiemannZetaOpenUnitIntervalNonvanishing_of_etaModTwoLFunction
    (hProduct : G8EtaModTwoLFunctionProductIdentityOnOpenUnit)
    (hSeries : G8EtaModTwoLFunctionSeriesIdentityOnOpenUnit) :
    G8RiemannZetaOpenUnitIntervalNonvanishing :=
  g8RiemannZetaOpenUnitIntervalNonvanishing_of_etaIdentity
    (g8DirichletEtaZetaIdentityOnOpenUnit_of_etaModTwoLFunction
      hProduct hSeries)

/-- Product plus series identity imply open-unit `xi` nonvanishing. -/
theorem g8OrthodoxXiOpenUnitIntervalNonvanishing_of_etaModTwoLFunction
    (hProduct : G8EtaModTwoLFunctionProductIdentityOnOpenUnit)
    (hSeries : G8EtaModTwoLFunctionSeriesIdentityOnOpenUnit) :
    G8OrthodoxXiOpenUnitIntervalNonvanishing :=
  g8OrthodoxXiOpenUnitIntervalNonvanishing_of_etaIdentity
    (g8DirichletEtaZetaIdentityOnOpenUnit_of_etaModTwoLFunction
      hProduct hSeries)

/-- Product plus series identity discharge the zero-height guard. -/
def G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoLFunction
    (hProduct : G8EtaModTwoLFunctionProductIdentityOnOpenUnit)
    (hSeries : G8EtaModTwoLFunctionSeriesIdentityOnOpenUnit) :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  G8ActualXiZeroHeightAxisGuardDischarge.ofDirichletEtaIdentity
    (g8DirichletEtaZetaIdentityOnOpenUnit_of_etaModTwoLFunction
      hProduct hSeries)

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A point where the mod-2 L-function lacks the zeta-product identity refutes
    the product-identity target. -/
structure G8EtaModTwoLFunctionProductIdentityFailure where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  noProductIdentity :
    ¬ G8EtaModTwoLFunctionProductIdentityAtOpenUnit x

/-- Missing product evidence refutes the global product target. -/
theorem G8EtaModTwoLFunctionProductIdentityFailure.refutesProductIdentity
    (w : G8EtaModTwoLFunctionProductIdentityFailure)
    (hProduct : G8EtaModTwoLFunctionProductIdentityOnOpenUnit) :
    False :=
  w.noProductIdentity (hProduct w.x w.pos w.lt_one)

/-- A point where the mod-2 L-function lacks the concrete eta-series identity
    refutes the series-identity target. -/
structure G8EtaModTwoLFunctionSeriesIdentityFailure where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  noSeriesIdentity :
    ¬ G8EtaModTwoLFunctionSeriesIdentityAtOpenUnit x
      (g8DirichletEtaOpenUnitSeriesValue (x := x) pos)

/-- Missing series evidence refutes the global series target. -/
theorem G8EtaModTwoLFunctionSeriesIdentityFailure.refutesSeriesIdentity
    (w : G8EtaModTwoLFunctionSeriesIdentityFailure)
    (hSeries : G8EtaModTwoLFunctionSeriesIdentityOnOpenUnit) :
    False :=
  w.noSeriesIdentity (hSeries w.x w.pos w.lt_one)

end Tau.BookIII.Bridge
