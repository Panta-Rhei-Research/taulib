import TauLib.BookIII.Bridge.G8OrthodoxTauUnitWitnessSupply

/-!
# TauLib.BookIII.Bridge.G8OrthodoxTauNormalFormWitnessSource

First normal-form source for the G8f tau-witness supply problem.

The preceding module showed that the normalized off-axis corridor only needs
pointwise tau witnesses whose boundary normal forms carry B/C imbalance.  This
module starts the next proof stone: separate what is already tau-normal-form
geometry from what is still a realization bridge into the abstract
`tauWitness` type of the local pullback context.

The tau-normal-form side is concrete: B/C imbalance is theorem-backed on
`BoundaryNF`, and small off-axis normal forms can be computed inside TauLib.
The remaining nontrivial bridge is explicit: a declared tau witness must
realize the chosen imbalanced normal form under `ctx.test.tauNormalForm`.

This module does not prove the analytic xi chart, O3, divisor transfer, global
RH, or the final tau preimage theorem.  It proves the adapter algebra needed
once a genuine normal-form witness source is supplied.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- A CONCRETE OFF-AXIS BOUNDARY NORMAL FORM
-- ============================================================

/-- A small computed tau boundary normal form with B/C imbalance.

This is not yet a pullback from an orthodox zero.  It is a concrete
tau-normal-form test object showing that the tau side has theorem-backed
off-axis normal forms. -/
def g8TauSampleOffAxisBoundaryNF : BoundaryNF :=
  boundary_normal_form 42 3

/-- The computed sample off-axis normal form. -/
theorem g8TauSampleOffAxisBoundaryNF_eval :
    g8TauSampleOffAxisBoundaryNF =
      { b_part := 0, c_part := 12, x_part := 0, depth := 3 } := by
  native_decide

/-- The sample normal form is B/C-imbalanced. -/
theorem g8TauSampleOffAxisBoundaryNF_bcImbalance :
    TauBCImbalance g8TauSampleOffAxisBoundaryNF := by
  unfold g8TauSampleOffAxisBoundaryNF TauBCImbalance BCBalanced
  native_decide

/-- The sample normal form is tau-critical-imbalanced. -/
theorem g8TauSampleOffAxisBoundaryNF_criticalImbalance :
    TauCriticalImbalance g8TauSampleOffAxisBoundaryNF :=
  (tauCriticalImbalance_iff_bcImbalance
    g8TauSampleOffAxisBoundaryNF).mpr
    g8TauSampleOffAxisBoundaryNF_bcImbalance

/-- The sample normal form has unit prime-polarity axis offset. -/
theorem g8TauSampleOffAxisBoundaryNF_unitAxis :
    primePolarityAxisOffset g8TauSampleOffAxisBoundaryNF = 1 :=
  (primePolarityAxisOffset_eq_one_iff_bcImbalance
    g8TauSampleOffAxisBoundaryNF).mpr
    g8TauSampleOffAxisBoundaryNF_bcImbalance

-- ============================================================
-- POINTWISE NORMAL-FORM WITNESS SOURCE
-- ============================================================

/-- Pointwise normal-form witness source for off-axis orthodox shadows.

For each readable off-axis receiving shadow, this package chooses a tau
boundary normal form, proves that it is B/C-imbalanced, and realizes it as a
declared tau witness in the current pullback context.

This is the precise proof-facing place where future tau geometry must provide
the preimage construction. -/
structure G8TauOffAxisNormalFormWitnessSource
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  normalFormForOffAxis :
    ∀ z : ctx.test.base.orthodoxZero,
      G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z →
        BoundaryNF
  normalFormBCImbalance :
    ∀ (z : ctx.test.base.orthodoxZero)
      (hOffAxis :
        G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z),
      TauBCImbalance (normalFormForOffAxis z hOffAxis)
  realize :
    ∀ (z : ctx.test.base.orthodoxZero)
      (_hOffAxis :
        G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z),
      ctx.test.base.tauWitness
  realize_normalForm :
    ∀ (z : ctx.test.base.orthodoxZero)
      (hOffAxis :
        G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z),
      ctx.test.tauNormalForm (realize z hOffAxis) =
        normalFormForOffAxis z hOffAxis

/-- A normal-form witness source supplies pointwise B/C-imbalance witnesses. -/
theorem g8TauOffAxisNormalFormWitnessSource_to_bcImbalanceWitnesses
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (nfSource : G8TauOffAxisNormalFormWitnessSource source) :
    G8OrthodoxTauBCImbalanceWitnessesExist source := by
  intro z hOffAxis
  refine ⟨nfSource.realize z hOffAxis, ?_⟩
  rw [nfSource.realize_normalForm z hOffAxis]
  exact nfSource.normalFormBCImbalance z hOffAxis

/-- A normal-form witness source supplies pointwise critical-imbalance
    witnesses. -/
theorem g8TauOffAxisNormalFormWitnessSource_to_criticalImbalanceWitnesses
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (nfSource : G8TauOffAxisNormalFormWitnessSource source) :
    G8OrthodoxTauCriticalImbalanceWitnessesExist source := by
  intro z hOffAxis
  refine ⟨nfSource.realize z hOffAxis, ?_⟩
  rw [nfSource.realize_normalForm z hOffAxis]
  exact
    (tauCriticalImbalance_iff_bcImbalance
      (nfSource.normalFormForOffAxis z hOffAxis)).mpr
      (nfSource.normalFormBCImbalance z hOffAxis)

/-- A normal-form witness source supplies pointwise unit tau preimages. -/
theorem g8TauOffAxisNormalFormWitnessSource_to_unitPreimages
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (nfSource : G8TauOffAxisNormalFormWitnessSource source) :
    G8OrthodoxTauUnitAxisPreimagesExist source :=
  g8OrthodoxTauBCImbalanceWitnesses_to_unitAxisPreimages
    source
    (g8TauOffAxisNormalFormWitnessSource_to_bcImbalanceWitnesses
      nfSource)

-- ============================================================
-- CONTEXT ADAPTER
-- ============================================================

/-- Normal-form witness-source context for the normalized off-axis corridor. -/
structure G8OrthodoxTauNormalFormWitnessSourceContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  source : G8OrthodoxShadowAxisSource ctx
  normalFormWitnessSource :
    G8TauOffAxisNormalFormWitnessSource source
  tauWitness :
    G8OffAxisTauWitnessRealization
      (g8OrthodoxShadowAxisSource_to_chart source)
  offAxisGuard :
    G8OffAxisChartOnlyGhostGuard
      (g8OrthodoxShadowAxisSource_to_chart source)

/-- A normal-form witness-source context feeds the B/C witness-supply context. -/
def g8OrthodoxTauNormalFormWitnessSource_to_unitWitnessSupply
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (nfCtx : G8OrthodoxTauNormalFormWitnessSourceContext ctx) :
    G8OrthodoxTauUnitWitnessSupplyContext ctx where
  source := nfCtx.source
  bcImbalanceWitnesses :=
    g8TauOffAxisNormalFormWitnessSource_to_bcImbalanceWitnesses
      nfCtx.normalFormWitnessSource
  tauWitness := nfCtx.tauWitness
  offAxisGuard := nfCtx.offAxisGuard

/-- A normal-form witness-source context feeds the normalized preimage context. -/
def g8OrthodoxTauNormalFormWitnessSource_to_normalizedPreimageContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (nfCtx : G8OrthodoxTauNormalFormWitnessSourceContext ctx) :
    G8OrthodoxNormalizedAxisPreimageContext ctx :=
  g8OrthodoxTauUnitWitnessSupply_to_normalizedPreimageContext
    (g8OrthodoxTauNormalFormWitnessSource_to_unitWitnessSupply nfCtx)

/-- A normal-form witness-source context yields the local one-sided pullback. -/
theorem g8OrthodoxTauNormalFormWitnessSource_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (nfCtx : G8OrthodoxTauNormalFormWitnessSourceContext ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8OrthodoxTauUnitWitnessSupply_yields_pullback ctx
    (g8OrthodoxTauNormalFormWitnessSource_to_unitWitnessSupply nfCtx)

/-- A normal-form witness-source context plus tau-side purity yields local
    no-off-critical orthodox zeros. -/
theorem g8OrthodoxTauNormalFormWitnessSource_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (nfCtx : G8OrthodoxTauNormalFormWitnessSourceContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OrthodoxTauUnitWitnessSupply_noOffCriticalZeros ctx
    (g8OrthodoxTauNormalFormWitnessSource_to_unitWitnessSupply nfCtx)
    tauPurity

-- ============================================================
-- SAMPLE NORMAL-FORM REALIZATION
-- ============================================================

/-- A declared tau witness realizes the concrete sample off-axis normal form. -/
structure G8TauSampleOffAxisNormalFormRealized
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  witness : ctx.test.base.tauWitness
  normalForm_eq :
    ctx.test.tauNormalForm witness = g8TauSampleOffAxisBoundaryNF

/-- Realizing the sample off-axis normal form gives a global B/C-imbalance
    witness. -/
def g8TauSampleOffAxisNormalFormRealized_to_bcImbalanceWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (realized : G8TauSampleOffAxisNormalFormRealized ctx) :
    G8TauBCImbalanceWitness ctx where
  witness := realized.witness
  imbalance := by
    rw [realized.normalForm_eq]
    exact g8TauSampleOffAxisBoundaryNF_bcImbalance

/-- Realizing the sample off-axis normal form supplies pointwise B/C witnesses
    for any orthodox shadow-axis source.  This is diagnostic: the final proof
    route should replace the sample by the real off-axis preimage geometry. -/
theorem g8TauSampleOffAxisNormalFormRealized_to_bcImbalanceWitnesses
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (realized : G8TauSampleOffAxisNormalFormRealized ctx) :
    G8OrthodoxTauBCImbalanceWitnessesExist source :=
  g8TauBCImbalanceWitness_to_bcImbalanceWitnesses source
    (g8TauSampleOffAxisNormalFormRealized_to_bcImbalanceWitness
      realized)

-- ============================================================
-- FALSIFIERS
-- ============================================================

/-- At a readable off-axis orthodox shadow, all declared tau witnesses have
    B/C-balanced normal forms. -/
structure G8TauAllDeclaredNormalFormsBalancedAtOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  offAxis :
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z
  allBalanced :
    ∀ w : ctx.test.base.tauWitness,
      BCBalanced (ctx.test.tauNormalForm w)

/-- If all declared tau witnesses are B/C-balanced at an off-axis shadow, then
    B/C-imbalance witness supply fails. -/
theorem
    g8TauAllDeclaredNormalFormsBalancedAtOffAxis_refutes_bcWitnessSupply
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8TauAllDeclaredNormalFormsBalancedAtOffAxis source) :
    ¬ G8OrthodoxTauBCImbalanceWitnessesExist source := by
  intro hSupply
  obtain ⟨tauW, hBC⟩ := hSupply w.z w.offAxis
  exact hBC (w.allBalanced tauW)

/-- A chosen off-axis normal form is not realized by any declared tau witness. -/
structure G8TauOffAxisNormalFormUnrealized
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (nfSource : G8TauOffAxisNormalFormWitnessSource source) where
  z : ctx.test.base.orthodoxZero
  offAxis :
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z
  noRealization :
    ∀ w : ctx.test.base.tauWitness,
      ctx.test.tauNormalForm w ≠
        nfSource.normalFormForOffAxis z offAxis

/-- An unrealized chosen normal form refutes a normal-form witness source. -/
theorem g8TauOffAxisNormalFormUnrealized_refutes_nfSource
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    {nfSource : G8TauOffAxisNormalFormWitnessSource source}
    (w : G8TauOffAxisNormalFormUnrealized nfSource) :
    False :=
  w.noRealization
    (nfSource.realize w.z w.offAxis)
    (nfSource.realize_normalForm w.z w.offAxis)

end Tau.BookIII.Bridge
