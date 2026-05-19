import TauLib.BookIII.Bridge.G8OrthodoxTauNormalFormWitnessSource

/-!
# TauLib.BookIII.Bridge.G8OrthodoxTauShadowNormalFormSource

Chart-shadow indexed tau normal-form source for the G8f corridor.

The previous normal-form witness module still allowed an arbitrary
`normalFormForOffAxis` field.  This module makes the first real construction
step: the tau normal form is selected from the centered receiving shadow
itself.

The selector is intentionally local and binary:

* centered on-axis shadows map to a theorem-backed B/C-balanced normal form;
* centered off-axis shadows map to a theorem-backed B/C-imbalanced normal
  form;
* realization into the abstract `tauWitness` type remains an explicit bridge
  field, because the current pullback context does not define `tauWitness` as
  `BoundaryNF`.

Thus the remaining hard target is no longer "choose a normal form"; it is
"realize the chart-selected tau normal form as the declared tau witness of the
pullback context."  No global RH, O3, divisor-transfer, or analytic xi theorem
is proved here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- SHADOW-INDEXED NORMAL FORM
-- ============================================================

/-- A small computed tau boundary normal form on the protected B/C-balanced
    axis. -/
def g8TauSampleOnAxisBoundaryNF : BoundaryNF :=
  boundary_normal_form 0 3

/-- The computed sample on-axis normal form. -/
theorem g8TauSampleOnAxisBoundaryNF_eval :
    g8TauSampleOnAxisBoundaryNF =
      { b_part := 0, c_part := 0, x_part := 0, depth := 3 } := by
  native_decide

/-- The sample on-axis normal form is B/C-balanced. -/
theorem g8TauSampleOnAxisBoundaryNF_bcBalanced :
    BCBalanced g8TauSampleOnAxisBoundaryNF := by
  unfold g8TauSampleOnAxisBoundaryNF BCBalanced
  native_decide

/-- The sample on-axis normal form lies on the tau critical locus. -/
theorem g8TauSampleOnAxisBoundaryNF_tauCritical :
    TauCriticalLocus g8TauSampleOnAxisBoundaryNF :=
  (tauCriticalLocus_iff_bcBalanced
    g8TauSampleOnAxisBoundaryNF).mpr
    g8TauSampleOnAxisBoundaryNF_bcBalanced

/-- Tau normal form selected by the centered receiving shadow.

Only the localization-bearing axis coordinate is used.  Height/provenance data
remain analytic bookkeeping for later divisor work. -/
def g8TauShadowSelectedNormalForm
    (p : CriticalAxisShadow) : BoundaryNF :=
  if p.axisOffset = 0 then
    g8TauSampleOnAxisBoundaryNF
  else
    g8TauSampleOffAxisBoundaryNF

/-- On-axis shadows select a B/C-balanced tau normal form. -/
theorem g8TauShadowSelectedNormalForm_onAxis_bcBalanced
    (p : CriticalAxisShadow)
    (hAxis : OnCriticalAxis p) :
    BCBalanced (g8TauShadowSelectedNormalForm p) := by
  unfold OnCriticalAxis at hAxis
  unfold g8TauShadowSelectedNormalForm
  simp [hAxis, g8TauSampleOnAxisBoundaryNF_bcBalanced]

/-- Off-axis shadows select a B/C-imbalanced tau normal form. -/
theorem g8TauShadowSelectedNormalForm_offAxis_bcImbalance
    (p : CriticalAxisShadow)
    (hOffAxis : ShadowOffAxis p) :
    TauBCImbalance (g8TauShadowSelectedNormalForm p) := by
  unfold ShadowOffAxis OnCriticalAxis at hOffAxis
  unfold g8TauShadowSelectedNormalForm
  simp [hOffAxis, g8TauSampleOffAxisBoundaryNF_bcImbalance]

/-- Off-axis shadows select a tau-critical-imbalanced tau normal form. -/
theorem g8TauShadowSelectedNormalForm_offAxis_criticalImbalance
    (p : CriticalAxisShadow)
    (hOffAxis : ShadowOffAxis p) :
    TauCriticalImbalance (g8TauShadowSelectedNormalForm p) :=
  (tauCriticalImbalance_iff_bcImbalance
    (g8TauShadowSelectedNormalForm p)).mpr
    (g8TauShadowSelectedNormalForm_offAxis_bcImbalance p hOffAxis)

/-- The shadow-axis source chart has the same off-axis predicate as its
    source shadow. -/
theorem g8OrthodoxShadowAxisSource_chartOffAxis_iff_sourceOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero) :
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z ↔
      ShadowOffAxis (source.centeredShadow z) := by
  rfl

/-- Chart off-axis data for a shadow-axis source exposes source-shadow
    off-axis data. -/
theorem g8OrthodoxShadowAxisSource_chartOffAxis_to_sourceOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (hOffAxis :
      G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z) :
    ShadowOffAxis (source.centeredShadow z) :=
  (g8OrthodoxShadowAxisSource_chartOffAxis_iff_sourceOffAxis
    source z).mp hOffAxis

-- ============================================================
-- REALIZATION BRIDGE FOR THE SELECTED NORMAL FORM
-- ============================================================

/-- Realization bridge from the chart-selected tau normal form into the
    abstract tau-witness type of the local pullback context. -/
structure G8TauShadowSelectedNormalFormRealization
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  realize :
    ∀ (z : ctx.test.base.orthodoxZero)
      (_hOffAxis :
        G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z),
      ctx.test.base.tauWitness
  realize_selected :
    ∀ (z : ctx.test.base.orthodoxZero)
      (hOffAxis :
        G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z),
      ctx.test.tauNormalForm (realize z hOffAxis) =
        g8TauShadowSelectedNormalForm (source.centeredShadow z)

/-- The chart-selected realization bridge supplies the generic normal-form
    witness source. -/
def g8TauShadowSelectedRealization_to_nfWitnessSource
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (realization : G8TauShadowSelectedNormalFormRealization source) :
    G8TauOffAxisNormalFormWitnessSource source where
  normalFormForOffAxis :=
    fun z _hOffAxis =>
      g8TauShadowSelectedNormalForm (source.centeredShadow z)
  normalFormBCImbalance := by
    intro z hOffAxis
    exact
      g8TauShadowSelectedNormalForm_offAxis_bcImbalance
        (source.centeredShadow z)
        (g8OrthodoxShadowAxisSource_chartOffAxis_to_sourceOffAxis
          source z hOffAxis)
  realize := realization.realize
  realize_normalForm := realization.realize_selected

/-- The chart-selected realization bridge supplies pointwise B/C-imbalance
    tau witnesses. -/
theorem g8TauShadowSelectedRealization_to_bcImbalanceWitnesses
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (realization : G8TauShadowSelectedNormalFormRealization source) :
    G8OrthodoxTauBCImbalanceWitnessesExist source :=
  g8TauOffAxisNormalFormWitnessSource_to_bcImbalanceWitnesses
    (g8TauShadowSelectedRealization_to_nfWitnessSource realization)

/-- The chart-selected realization bridge supplies pointwise critical
    imbalance tau witnesses. -/
theorem g8TauShadowSelectedRealization_to_criticalImbalanceWitnesses
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (realization : G8TauShadowSelectedNormalFormRealization source) :
    G8OrthodoxTauCriticalImbalanceWitnessesExist source :=
  g8TauOffAxisNormalFormWitnessSource_to_criticalImbalanceWitnesses
    (g8TauShadowSelectedRealization_to_nfWitnessSource realization)

-- ============================================================
-- CONTEXT ADAPTER
-- ============================================================

/-- Chart-shadow selected normal-form source context for the normalized
    off-axis corridor. -/
structure G8OrthodoxTauShadowNormalFormSourceContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  source : G8OrthodoxShadowAxisSource ctx
  realization :
    G8TauShadowSelectedNormalFormRealization source
  tauWitness :
    G8OffAxisTauWitnessRealization
      (g8OrthodoxShadowAxisSource_to_chart source)
  offAxisGuard :
    G8OffAxisChartOnlyGhostGuard
      (g8OrthodoxShadowAxisSource_to_chart source)

/-- The chart-shadow selected source feeds the generic normal-form
    witness-source context. -/
def g8OrthodoxTauShadowNormalFormSource_to_nfWitnessSourceContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (shadowCtx : G8OrthodoxTauShadowNormalFormSourceContext ctx) :
    G8OrthodoxTauNormalFormWitnessSourceContext ctx where
  source := shadowCtx.source
  normalFormWitnessSource :=
    g8TauShadowSelectedRealization_to_nfWitnessSource
      shadowCtx.realization
  tauWitness := shadowCtx.tauWitness
  offAxisGuard := shadowCtx.offAxisGuard

/-- The chart-shadow selected source yields the local one-sided pullback. -/
theorem g8OrthodoxTauShadowNormalFormSource_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (shadowCtx : G8OrthodoxTauShadowNormalFormSourceContext ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8OrthodoxTauNormalFormWitnessSource_yields_pullback ctx
    (g8OrthodoxTauShadowNormalFormSource_to_nfWitnessSourceContext
      shadowCtx)

/-- The chart-shadow selected source plus tau-side purity yields local
    no-off-critical orthodox zeros. -/
theorem g8OrthodoxTauShadowNormalFormSource_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (shadowCtx : G8OrthodoxTauShadowNormalFormSourceContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OrthodoxTauNormalFormWitnessSource_noOffCriticalZeros ctx
    (g8OrthodoxTauShadowNormalFormSource_to_nfWitnessSourceContext
      shadowCtx)
    tauPurity

-- ============================================================
-- FALSIFIERS
-- ============================================================

/-- The chart-selected normal form at an off-axis shadow is not realized by
    any declared tau witness. -/
structure G8TauShadowSelectedNormalFormUnrealized
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  offAxis :
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z
  noRealization :
    ∀ w : ctx.test.base.tauWitness,
      ctx.test.tauNormalForm w ≠
        g8TauShadowSelectedNormalForm (source.centeredShadow z)

/-- Unrealized chart-selected normal forms refute the realization bridge. -/
theorem g8TauShadowSelectedNormalFormUnrealized_refutes_realization
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8TauShadowSelectedNormalFormUnrealized source)
    (realization : G8TauShadowSelectedNormalFormRealization source) :
    False :=
  w.noRealization
    (realization.realize w.z w.offAxis)
    (realization.realize_selected w.z w.offAxis)

/-- Unrealized chart-selected normal forms refute the selected-source
    context. -/
theorem g8TauShadowSelectedNormalFormUnrealized_refutes_context
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {shadowCtx : G8OrthodoxTauShadowNormalFormSourceContext ctx}
    (w : G8TauShadowSelectedNormalFormUnrealized shadowCtx.source) :
    False :=
  g8TauShadowSelectedNormalFormUnrealized_refutes_realization w
    shadowCtx.realization

end Tau.BookIII.Bridge
