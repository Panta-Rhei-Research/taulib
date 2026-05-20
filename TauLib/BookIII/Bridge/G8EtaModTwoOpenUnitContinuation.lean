import TauLib.BookIII.Bridge.G8EtaModTwoRightHalfPlaneProduct

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoOpenUnitContinuation

Open-unit continuation handoff for the Lane-A eta bridge.

The right-half-plane eta product is theorem-backed in
`G8EtaModTwoRightHalfPlaneProduct`.  The genuinely analytic open-unit payloads
remain explicit proof-carrying fields:

* continuation of the product identity from the safe half-plane to `0 < x < 1`;
* identification of Mathlib's mod-two `LFunction` with the concrete
  conditional eta value on that interval.

Together they discharge the real open-unit zeta nonvanishing target and hence
the zero-height axis guard.  No result here uses RH, accepted coverage, the
final live hinge, O3, full divisor transfer, or analytic-completion
uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped BigOperators Topology

-- ============================================================
-- THEOREM-BACKED PRODUCT CONTINUATION
-- ============================================================

/-- The safe-half-plane eta product identity analytically continues to the
    punctured plane.  This closes the product side of the Lane-A eta bridge;
    the remaining open-unit payload is the real-valued zeta readout and the
    L-function/concrete-eta identification. -/
theorem g8EtaModTwoLFunctionProductIdentityOnPuncturedPlane
    {s : ℂ} (hs : s ≠ 1) :
    g8EtaModTwoLFunction s =
      (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  let U : Set ℂ := {z | z ≠ (1 : ℂ)}
  let F : ℂ → ℂ := fun z => g8EtaModTwoLFunction z
  let G : ℂ → ℂ :=
    fun z => (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z
  have hUopen : IsOpen U := by
    change IsOpen ({(1 : ℂ)}ᶜ : Set ℂ)
    exact isOpen_compl_singleton
  have hF : AnalyticOnNhd ℂ F U := by
    have hdiff : Differentiable ℂ F := by
      dsimp [F, g8EtaModTwoLFunction]
      exact ZMod.differentiable_LFunction_of_sum_zero
        (Φ := g8EtaModTwoCoeff) g8EtaModTwoCoeff_sum_zero
    exact DifferentiableOn.analyticOnNhd
      (fun z _hz => (hdiff z).differentiableWithinAt) hUopen
  have hG : AnalyticOnNhd ℂ G U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    have hz1 : z ≠ 1 := by
      simpa [U] using hz
    have hpowArg :
        DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) - z) z := by
      exact (differentiableAt_const (1 : ℂ)).sub differentiableAt_id
    have hpow :
        DifferentiableAt ℂ
          (fun z : ℂ => (2 : ℂ) ^ ((1 : ℂ) - z)) z := by
      exact hpowArg.const_cpow (.inl (by norm_num : (2 : ℂ) ≠ 0))
    have hfactor :
        DifferentiableAt ℂ
          (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z)) z := by
      exact (differentiableAt_const (1 : ℂ)).sub hpow
    have hzeta : DifferentiableAt ℂ riemannZeta z :=
      differentiableAt_riemannZeta hz1
    exact (by
      simpa [G] using (hfactor.mul hzeta).differentiableWithinAt)
  have hUpre : IsPreconnected U := by
    simpa [U] using
      (isConnected_compl_singleton_of_one_lt_rank (E := ℂ)
        (by simp) (1 : ℂ)).isPreconnected
  have hbase : (2 : ℂ) ∈ U := by
    norm_num [U]
  have heqNhds : F =ᶠ[𝓝 (2 : ℂ)] G := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const continuous_re
    have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      hopen.mem_nhds (by norm_num)
    filter_upwards [hmem] with z hz
    dsimp [F, G]
    exact
      (g8EtaModTwoLFunctionProductIdentityOnRightHalfPlane_theorem
        z hz).productIdentity
  have hsU : s ∈ U := by
    simpa [U] using hs
  exact
    hF.eqOn_of_preconnected_of_eventuallyEq hG hUpre
      hbase heqNhds hsU

/-- Cast the real eta denominator into the complex product factor. -/
theorem g8EtaModTwo_complexDenominator_eq
    (x : ℝ) :
    (1 - (2 : ℂ) ^ (1 - (x : ℂ))) =
      (g8DirichletEtaDenominator x : ℂ) := by
  unfold g8DirichletEtaDenominator
  have hpow :
      (2 : ℂ) ^ (1 - (x : ℂ)) =
        (((2 : ℝ) ^ (1 - x : ℝ) : ℝ) : ℂ) := by
    calc
      (2 : ℂ) ^ (1 - (x : ℂ)) =
          (2 : ℂ) ^ ((1 - x : ℝ) : ℂ) := by
        congr 1
        norm_num
      _ = (((2 : ℝ) ^ (1 - x : ℝ) : ℝ) : ℂ) := by
        exact (Complex.ofReal_cpow
          (by norm_num : 0 ≤ (2 : ℝ)) (1 - x)).symm
  rw [hpow]
  norm_num

/-- The product identity on the real open unit interval is theorem-backed.
    This theorem supplies the `openUnitProduct` field of the continuation
    object; only the real-valued zeta readout remains separate. -/
theorem g8EtaModTwoLFunction_openUnitProductIdentity
    (x : ℝ) (_hx0 : 0 < x) (hx1 : x < 1) :
    g8EtaModTwoLFunction (x : ℂ) =
      (g8DirichletEtaDenominator x : ℂ) * riemannZeta (x : ℂ) := by
  have hxne : (x : ℂ) ≠ 1 := by
    norm_cast
    exact ne_of_lt hx1
  rw [g8EtaModTwoLFunctionProductIdentityOnPuncturedPlane hxne]
  rw [g8EtaModTwo_complexDenominator_eq x]

/-- The only product-continuation residue after analytic continuation is the
    real-valued zeta readout on the open unit interval. -/
abbrev G8RiemannZetaRealOnOpenUnit : Prop :=
  ∀ (x : ℝ), 0 < x → x < 1 →
    (riemannZeta (x : ℂ)).im = 0

/-- Real-valued zeta readout is now exactly sufficient for the product
    continuation object: the product identity itself is theorem-backed above. -/
def g8EtaModTwoProductContinuationToOpenUnit_of_zetaReal
    (hZetaReal : G8RiemannZetaRealOnOpenUnit) :
    G8EtaModTwoProductContinuationToOpenUnit
      g8EtaModTwoLFunctionProductIdentityOnRightHalfPlane_theorem where
  zetaReal := hZetaReal
  openUnitProduct := g8EtaModTwoLFunction_openUnitProductIdentity

-- ============================================================
-- OPEN-UNIT CONTINUATION DATA
-- ============================================================

/-- The exact remaining open-unit analytic data after the safe-half-plane
    product theorem is closed. -/
structure G8EtaModTwoOpenUnitContinuationData where
  productContinuation :
    G8EtaModTwoProductContinuationToOpenUnit
      g8EtaModTwoLFunctionProductIdentityOnRightHalfPlane_theorem
  lFunctionConcreteEta :
    G8EtaModTwoLFunctionEqualsConcreteEtaOnOpenUnit

/-- The product-continuation field supplies the existing open-unit product
    target. -/
theorem G8EtaModTwoOpenUnitContinuationData.openUnitProduct
    (data : G8EtaModTwoOpenUnitContinuationData) :
    G8EtaModTwoLFunctionProductIdentityOnOpenUnit :=
  data.productContinuation.toOpenUnitProduct

/-- The two open-unit analytic inputs imply the existing eta-zeta identity on
    the real open unit interval. -/
theorem G8EtaModTwoOpenUnitContinuationData.etaZetaIdentity
    (data : G8EtaModTwoOpenUnitContinuationData) :
    G8DirichletEtaZetaIdentityOnOpenUnit :=
  g8DirichletEtaZetaIdentityOnOpenUnit_of_etaModTwoContinuation
    data.productContinuation data.lFunctionConcreteEta

/-- The open-unit continuation package implies real zeta nonvanishing on
    `0 < x < 1`. -/
theorem G8EtaModTwoOpenUnitContinuationData.riemannZetaOpenUnitNonvanishing
    (data : G8EtaModTwoOpenUnitContinuationData) :
    G8RiemannZetaOpenUnitIntervalNonvanishing :=
  g8RiemannZetaOpenUnitIntervalNonvanishing_of_etaIdentity
    data.etaZetaIdentity

/-- The open-unit continuation package discharges the zero-height axis guard. -/
def G8EtaModTwoOpenUnitContinuationData.zeroHeightDischarge
    (data : G8EtaModTwoOpenUnitContinuationData) :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  G8ActualXiZeroHeightAxisGuardDischarge.ofDirichletEtaIdentity
    data.etaZetaIdentity

-- ============================================================
-- RESIDUAL TARGET AND FALSIFIER SURFACES
-- ============================================================

/-- Product continuation from the safe half-plane remains one explicit
    analytic target. -/
abbrev G8EtaModTwoOpenUnitProductContinuationTarget : Prop :=
  G8EtaModTwoProductContinuationToOpenUnit
    g8EtaModTwoLFunctionProductIdentityOnRightHalfPlane_theorem

/-- Concrete open-unit identification of the mod-two `LFunction` with the eta
    conditional-series value remains the second explicit analytic target. -/
abbrev G8EtaModTwoOpenUnitConcreteSeriesTarget : Prop :=
  G8EtaModTwoLFunctionEqualsConcreteEtaOnOpenUnit

/-- A missing product-continuation theorem refutes any full open-unit
    continuation package. -/
structure G8EtaModTwoMissingOpenUnitProductContinuation where
  missing : ¬ G8EtaModTwoOpenUnitProductContinuationTarget

/-- A missing product-continuation theorem refutes continuation data. -/
theorem G8EtaModTwoMissingOpenUnitProductContinuation.refutes
    (w : G8EtaModTwoMissingOpenUnitProductContinuation)
    (data : G8EtaModTwoOpenUnitContinuationData) :
    False :=
  w.missing data.productContinuation

/-- A missing concrete-series identification refutes any full open-unit
    continuation package. -/
structure G8EtaModTwoMissingOpenUnitConcreteSeriesIdentity where
  missing : ¬ G8EtaModTwoOpenUnitConcreteSeriesTarget

/-- A missing concrete-series identification refutes continuation data. -/
theorem G8EtaModTwoMissingOpenUnitConcreteSeriesIdentity.refutes
    (w : G8EtaModTwoMissingOpenUnitConcreteSeriesIdentity)
    (data : G8EtaModTwoOpenUnitContinuationData) :
    False :=
  w.missing data.lFunctionConcreteEta

/-- A concrete open-unit product mismatch refutes the product-continuation
    field of the package. -/
theorem G8EtaModTwoProductContinuationOpenUnitMismatch.refutesTheorem
    (w : G8EtaModTwoProductContinuationOpenUnitMismatch
      g8EtaModTwoLFunctionProductIdentityOnRightHalfPlane_theorem)
    (data : G8EtaModTwoOpenUnitContinuationData) :
    False :=
  w.refutes data.productContinuation

end Tau.BookIII.Bridge
