import TauLib.BookIII.Bridge.G8EtaModTwoPairedLocalUniformConvergence

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoPairedPositiveHalfPlaneClosure

Positive-half-plane closure for the paired eta route.

The previous wave made paired eta convergence local-uniform on `0 < re s`.
This module threads that convergence into the analytic continuation argument:
termwise holomorphy, safe-half-plane agreement with the Mathlib mod-two
`LFunction` / `-expZeta` object, and the identity-theorem extension across the
positive half-plane.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, pullback machinery, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped BigOperators Topology

-- ============================================================
-- TERMWISE HOLOMORPHY
-- ============================================================

/-- Each paired eta term is complex differentiable in the spectral variable. -/
theorem g8EtaModTwoPairedEtaTerm_differentiableAt
    (n : ℕ) (s : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => g8EtaModTwoPairedEtaTerm z n) s := by
  unfold g8EtaModTwoPairedEtaTerm
  have hOddNe : (((2 * n + 1 : ℕ) : ℂ) ≠ 0) := by
    exact_mod_cast (by omega : 2 * n + 1 ≠ 0)
  have hEvenNe : (((2 * n + 2 : ℕ) : ℂ) ≠ 0) := by
    exact_mod_cast (by omega : 2 * n + 2 ≠ 0)
  exact
    ((differentiableAt_id.neg).const_cpow (Or.inl hOddNe)).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl hEvenNe))

/-- The paired eta series is analytic on the positive half-plane, by local
    uniform summability of holomorphic terms. -/
theorem g8EtaModTwoPairedEtaSeries_analyticOn_posHalfPlane_from_mvt :
    AnalyticOnNhd ℂ g8EtaModTwoPairedEtaSeries
      G8EtaModTwoPositiveHalfPlane := by
  have hdiff :
      DifferentiableOn ℂ g8EtaModTwoPairedEtaSeries
        G8EtaModTwoPositiveHalfPlane := by
    simpa [g8EtaModTwoPairedEtaSeries] using
      SummableLocallyUniformlyOn.differentiableOn
        g8EtaModTwoPositiveHalfPlane_isOpen
        g8EtaModTwoPairedPositiveHalfPlane_locallyUniform_from_mvt
        (fun n r _hr =>
          g8EtaModTwoPairedEtaTerm_differentiableAt n r)
  exact hdiff.analyticOnNhd g8EtaModTwoPositiveHalfPlane_isOpen

/-- The target `-expZeta` readout is analytic on the positive half-plane via
    the theorem-backed mod-two `LFunction` coefficient bridge. -/
theorem g8EtaModTwo_negExpZeta_analyticOn_posHalfPlane :
    AnalyticOnNhd ℂ
      (fun s : ℂ =>
        - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s)
      G8EtaModTwoPositiveHalfPlane := by
  let F : ℂ → ℂ :=
    fun s : ℂ =>
      - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s
  have hF_eq : F = g8EtaModTwoLFunction := by
    funext s
    exact (g8EtaModTwoLFunction_eq_neg_expZeta s).symm
  have hdiff : Differentiable ℂ F := by
    rw [hF_eq]
    exact g8EtaModTwoLFunction_differentiable
  have hdiffOn :
      DifferentiableOn ℂ F G8EtaModTwoPositiveHalfPlane :=
    fun z _hz => (hdiff z).differentiableWithinAt
  simpa [F] using
    hdiffOn.analyticOnNhd g8EtaModTwoPositiveHalfPlane_isOpen

/-- The MVT/local-uniform result supplies the analytic fields of the
    positive-half-plane package. -/
def g8EtaModTwoPairedPositiveHalfPlaneAnalyticity_from_mvt :
    G8EtaModTwoPairedPositiveHalfPlaneAnalyticity where
  convergence := g8EtaModTwoPairedPositiveHalfPlaneConvergence_from_mvt
  pairedAnalytic :=
    g8EtaModTwoPairedEtaSeries_analyticOn_posHalfPlane_from_mvt
  negExpZetaAnalytic :=
    g8EtaModTwo_negExpZeta_analyticOn_posHalfPlane

-- ============================================================
-- SAFE-HALF-PLANE GROUPING
-- ============================================================

/-- One paired eta term is the sum of the two corresponding positive-index
    `LSeries.term`s. -/
theorem g8EtaModTwoPairedEtaTerm_eq_LSeries_term_pair
    (s : ℂ) (n : ℕ) :
    g8EtaModTwoPairedEtaTerm s n =
      LSeries.term g8EtaModTwoNatCoeff s (2 * n + 1) +
        LSeries.term g8EtaModTwoNatCoeff s (2 * n + 2) := by
  unfold g8EtaModTwoPairedEtaTerm
  have hOddNe : 2 * n + 1 ≠ 0 := by omega
  have hEvenNe : 2 * n + 2 ≠ 0 := by omega
  rw [LSeries.term_of_ne_zero hOddNe, LSeries.term_of_ne_zero hEvenNe]
  have hOdd := (g8EtaModTwoNatCoeff_odd_even_pair n).1
  have hEven := (g8EtaModTwoNatCoeff_odd_even_pair n).2
  rw [hOdd, hEven]
  simp [div_eq_mul_inv, cpow_neg]
  ring

/-- Safe-half-plane absolute convergence lets the ordinary mod-two `LSeries`
    be grouped into the odd/even paired eta series. -/
theorem g8EtaModTwoPairedEtaSeries_eq_LSeries_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    g8EtaModTwoPairedEtaSeries s =
      LSeries g8EtaModTwoNatCoeff s := by
  let a : ℕ → ℂ := fun n => LSeries.term g8EtaModTwoNatCoeff s n
  have hSumm : Summable a :=
    g8EtaModTwoNatCoeff_LSeriesSummable_of_one_lt_re hs
  have hA : HasSum a (LSeries g8EtaModTwoNatCoeff s) := by
    simpa [a, LSeries] using hSumm.hasSum
  have hTail :
      HasSum (fun n : ℕ => a (n + 1))
        (LSeries g8EtaModTwoNatCoeff s) := by
    have hTail' :
        HasSum (fun n : ℕ => a (n + 1))
          (LSeries g8EtaModTwoNatCoeff s -
            ∑ i ∈ Finset.range 1, a i) := by
      exact (hasSum_nat_add_iff' (f := a) (k := 1)).mpr hA
    simpa [a, LSeries.term_zero] using hTail'
  have hReindexed :=
    (Nat.divModEquiv 2).symm.hasSum_iff.mpr hTail
  dsimp [Function.comp_def, a] at hReindexed
  simp_rw [← mul_comm 2 _] at hReindexed
  have hGrouped :
      HasSum
        (fun n : ℕ =>
          LSeries.term g8EtaModTwoNatCoeff s (2 * n + 1) +
            LSeries.term g8EtaModTwoNatCoeff s (2 * n + 2))
        (LSeries g8EtaModTwoNatCoeff s) := by
    refine hReindexed.prod_fiberwise fun n => ?_
    dsimp only
    convert hasSum_fintype
      (fun j : Fin 2 =>
        LSeries.term g8EtaModTwoNatCoeff s (2 * n + (j : ℕ) + 1)) using 1
    rw [Fin.sum_univ_two]
    simp [Nat.add_assoc]
  have hPaired :
      HasSum (fun n : ℕ => g8EtaModTwoPairedEtaTerm s n)
        (LSeries g8EtaModTwoNatCoeff s) :=
    hGrouped.congr_fun fun n =>
      g8EtaModTwoPairedEtaTerm_eq_LSeries_term_pair s n
  simpa [g8EtaModTwoPairedEtaSeries] using hPaired.tsum_eq

/-- The safe-half-plane paired eta series agrees with Mathlib's continued
    mod-two `-expZeta` object. -/
theorem g8EtaModTwoPairedSafeHalfPlaneAgreement_theorem :
    G8EtaModTwoPairedSafeHalfPlaneAgreement where
  agreement := by
    intro s hs
    calc
      g8EtaModTwoPairedEtaSeries s =
          LSeries g8EtaModTwoNatCoeff s :=
        g8EtaModTwoPairedEtaSeries_eq_LSeries_of_one_lt_re hs
      _ = g8EtaModTwoLFunction s :=
        (g8EtaModTwoLFunction_eq_LSeries_of_one_lt_re hs).symm
      _ = - HurwitzZeta.expZeta
          (ZMod.toAddCircle (1 : ZMod 2)) s :=
        g8EtaModTwoLFunction_eq_neg_expZeta s

-- ============================================================
-- IDENTITY-THEOREM CONTINUATION
-- ============================================================

/-- The positive half-plane is convex. -/
theorem g8EtaModTwoPositiveHalfPlane_convex :
    Convex ℝ G8EtaModTwoPositiveHalfPlane := by
  intro x hx y hy a b ha hb hab
  dsimp [G8EtaModTwoPositiveHalfPlane] at hx hy ⊢
  have hsum_pos : 0 < a * x.re + b * y.re := by
    by_cases ha_zero : a = 0
    · have hb_one : b = 1 := by nlinarith
      nlinarith
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
      have hax_pos : 0 < a * x.re := mul_pos ha_pos hx
      have hby_nonneg : 0 ≤ b * y.re := mul_nonneg hb hy.le
      nlinarith
  simpa using hsum_pos

/-- The positive half-plane is preconnected. -/
theorem g8EtaModTwoPositiveHalfPlane_isPreconnected :
    IsPreconnected G8EtaModTwoPositiveHalfPlane :=
  g8EtaModTwoPositiveHalfPlane_convex.isPreconnected

/-- Analyticity plus safe-half-plane agreement extends the paired eta /
    `-expZeta` equality to all of `0 < re s`. -/
theorem g8EtaModTwoPairedPositiveHalfPlaneContinuation_theorem :
    G8EtaModTwoPairedPositiveHalfPlaneContinuation where
  analyticity := g8EtaModTwoPairedPositiveHalfPlaneAnalyticity_from_mvt
  safeAgreement := g8EtaModTwoPairedSafeHalfPlaneAgreement_theorem
  continuedAgreement := by
    intro s hs
    let F : ℂ → ℂ := g8EtaModTwoPairedEtaSeries
    let G : ℂ → ℂ :=
      fun z : ℂ =>
        - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) z
    have hbase : (2 : ℂ) ∈ G8EtaModTwoPositiveHalfPlane := by
      norm_num [G8EtaModTwoPositiveHalfPlane]
    have heqNhds : F =ᶠ[𝓝 (2 : ℂ)] G := by
      have hopen : IsOpen G8EtaModTwoSafeHalfPlane := by
        simpa [G8EtaModTwoSafeHalfPlane] using
          isOpen_lt continuous_const continuous_re
      have hmem : G8EtaModTwoSafeHalfPlane ∈ 𝓝 (2 : ℂ) :=
        hopen.mem_nhds (by norm_num [G8EtaModTwoSafeHalfPlane])
      filter_upwards [hmem] with z hz
      dsimp [F, G]
      exact
        g8EtaModTwoPairedSafeHalfPlaneAgreement_theorem.agreement z hz
    exact
      AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
        g8EtaModTwoPairedPositiveHalfPlaneAnalyticity_from_mvt.pairedAnalytic
        g8EtaModTwoPairedPositiveHalfPlaneAnalyticity_from_mvt.negExpZetaAnalytic
        g8EtaModTwoPositiveHalfPlane_isPreconnected
        hbase heqNhds hs

/-- The theorem-backed positive-half-plane analytic package. -/
def g8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage_theorem :
    G8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage where
  continuation := g8EtaModTwoPairedPositiveHalfPlaneContinuation_theorem

-- ============================================================
-- DOWNSTREAM ZERO-HEIGHT CONSEQUENCES
-- ============================================================

/-- The paired positive-half-plane theorem supplies the paired-series core. -/
def g8EtaModTwoPairedEtaSeriesEqNegExpZetaOnPositiveHalfPlane_theorem :
    G8EtaModTwoPairedEtaSeriesEqNegExpZetaOnPositiveHalfPlane :=
  g8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage_theorem.toPositiveHalfPlaneCore

/-- The paired positive-half-plane theorem gives the real open-unit ExpZeta
    boundary theorem. -/
theorem g8EtaModTwoPairedExpZetaBoundaryOnOpenUnit_theorem :
    G8EtaModTwoPairedExpZetaBoundaryOnOpenUnit :=
  g8EtaModTwoPairedExpZetaBoundaryOnOpenUnit_of_positiveHalfPlaneAnalyticPackage
    g8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage_theorem

/-- The paired positive-half-plane theorem gives the concrete eta /
    `-expZeta` equality on the real open unit interval. -/
theorem g8EtaModTwoExpZetaConcreteEtaOnOpenUnit_theorem :
    G8EtaModTwoExpZetaConcreteEtaOnOpenUnit :=
  g8EtaModTwoExpZetaConcreteEtaOnOpenUnit_of_positiveHalfPlaneAnalyticPackage
    g8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage_theorem

/-- The paired positive-half-plane theorem gives the eta-zeta identity on the
    real open unit interval. -/
theorem g8DirichletEtaZetaIdentityOnOpenUnit_from_pairedPositiveHalfPlane :
    G8DirichletEtaZetaIdentityOnOpenUnit :=
  g8DirichletEtaZetaIdentityOnOpenUnit_of_expZetaConcreteEta
    g8EtaModTwoExpZetaConcreteEtaOnOpenUnit_theorem

/-- The paired positive-half-plane theorem gives zeta nonvanishing on the real
    open unit interval. -/
theorem g8RiemannZetaOpenUnitIntervalNonvanishing_from_pairedPositiveHalfPlane :
    G8RiemannZetaOpenUnitIntervalNonvanishing :=
  g8RiemannZetaOpenUnitIntervalNonvanishing_of_etaIdentity
    g8DirichletEtaZetaIdentityOnOpenUnit_from_pairedPositiveHalfPlane

/-- The paired positive-half-plane theorem discharges the zero-height axis
    guard. -/
def g8ActualXiZeroHeightAxisGuardDischarge_from_pairedPositiveHalfPlane :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoPairedPositiveHalfPlaneAnalyticPackage
    g8EtaModTwoPairedPositiveHalfPlaneAnalyticPackage_theorem

end Tau.BookIII.Bridge
