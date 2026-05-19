import TauLib.BookIII.Bridge.G8OrthodoxTauShadowNormalFormSource

/-!
# TauLib.BookIII.Bridge.G8OrthodoxTauWitnessRealization

Realization of chart-selected tau normal forms in the abstract tau-witness
layer.

The shadow-normal-form selector makes the tau-side normal form concrete:
off-axis receiving shadows select a theorem-backed B/C-imbalanced
`BoundaryNF`.  The remaining bridge is that this selected normal form is
represented by the abstract `tauWitness` type of the local pullback context.

This module isolates that bridge as a section of `ctx.test.tauNormalForm`.
When such a section is available, the existing G8f corridor receives a genuine
selected-normal-form realization.  When it is not available, the failure is
recorded as an explicit image/realization falsifier.

No analytic xi theorem, O3 correspondence, divisor transfer, global RH, or
tau purity theorem is proved here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- ABSTRACT WITNESS-LAYER SECTION
-- ============================================================

/-- A section of the abstract tau-witness normal-form projection.

This is the exact place where the current abstract pullback context must be
connected to tau boundary normal forms.  It says that every `BoundaryNF` has a
declared tau witness whose normal form is exactly that boundary normal form. -/
structure G8TauNormalFormSection
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  realizeBoundaryNF : BoundaryNF → ctx.test.base.tauWitness
  realizeBoundaryNF_normalForm :
    ∀ nf : BoundaryNF,
      ctx.test.tauNormalForm (realizeBoundaryNF nf) = nf

/-- The selected off-axis normal forms lie in the image of the tau-witness
    normal-form projection. -/
def G8TauSelectedNormalFormsInWitnessImage
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) : Prop :=
  ∀ z : ctx.test.base.orthodoxZero,
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z →
      ∃ w : ctx.test.base.tauWitness,
        ctx.test.tauNormalForm w =
          g8TauShadowSelectedNormalForm (source.centeredShadow z)

/-- A total normal-form section puts every selected off-axis normal form in
    the witness image. -/
theorem g8TauNormalFormSection_selectedNormalFormsInWitnessImage
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (sec : G8TauNormalFormSection ctx) :
    G8TauSelectedNormalFormsInWitnessImage source := by
  intro z _hOffAxis
  refine ⟨
    sec.realizeBoundaryNF
      (g8TauShadowSelectedNormalForm (source.centeredShadow z)),
    ?_⟩
  exact
    sec.realizeBoundaryNF_normalForm
      (g8TauShadowSelectedNormalForm (source.centeredShadow z))

/-- A total normal-form section realizes the chart-selected normal form for
    every off-axis shadow. -/
def g8TauNormalFormSection_to_shadowSelectedRealization
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (sec : G8TauNormalFormSection ctx) :
    G8TauShadowSelectedNormalFormRealization source where
  realize :=
    fun z _hOffAxis =>
      sec.realizeBoundaryNF
        (g8TauShadowSelectedNormalForm (source.centeredShadow z))
  realize_selected := by
    intro z _hOffAxis
    exact
      sec.realizeBoundaryNF_normalForm
        (g8TauShadowSelectedNormalForm (source.centeredShadow z))

/-- A total normal-form section supplies the generic normal-form witness
    source used by the previous adapter layer. -/
def g8TauNormalFormSection_to_nfWitnessSource
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (sec : G8TauNormalFormSection ctx) :
    G8TauOffAxisNormalFormWitnessSource source :=
  g8TauShadowSelectedRealization_to_nfWitnessSource
    (g8TauNormalFormSection_to_shadowSelectedRealization source sec)

/-- A total normal-form section supplies pointwise B/C-imbalance witnesses for
    off-axis shadows. -/
theorem g8TauNormalFormSection_to_bcImbalanceWitnesses
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (sec : G8TauNormalFormSection ctx) :
    G8OrthodoxTauBCImbalanceWitnessesExist source :=
  g8TauOffAxisNormalFormWitnessSource_to_bcImbalanceWitnesses
    (g8TauNormalFormSection_to_nfWitnessSource source sec)

/-- A total normal-form section supplies pointwise unit-axis tau preimages. -/
theorem g8TauNormalFormSection_to_unitPreimages
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (sec : G8TauNormalFormSection ctx) :
    G8OrthodoxTauUnitAxisPreimagesExist source :=
  g8TauOffAxisNormalFormWitnessSource_to_unitPreimages
    (g8TauNormalFormSection_to_nfWitnessSource source sec)

-- ============================================================
-- CORRIDOR CONTEXT
-- ============================================================

/-- Witness-realization context for the chart-selected normal-form route. -/
structure G8OrthodoxTauWitnessRealizationContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  source : G8OrthodoxShadowAxisSource ctx
  normalFormSection : G8TauNormalFormSection ctx
  tauWitness :
    G8OffAxisTauWitnessRealization
      (g8OrthodoxShadowAxisSource_to_chart source)
  offAxisGuard :
    G8OffAxisChartOnlyGhostGuard
      (g8OrthodoxShadowAxisSource_to_chart source)

/-- The witness-realization context supplies the chart-shadow selected source
    context. -/
def g8OrthodoxTauWitnessRealization_to_shadowSourceContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (realCtx : G8OrthodoxTauWitnessRealizationContext ctx) :
    G8OrthodoxTauShadowNormalFormSourceContext ctx where
  source := realCtx.source
  realization :=
    g8TauNormalFormSection_to_shadowSelectedRealization
      realCtx.source realCtx.normalFormSection
  tauWitness := realCtx.tauWitness
  offAxisGuard := realCtx.offAxisGuard

/-- The witness-realization context supplies the local one-sided pullback. -/
theorem g8OrthodoxTauWitnessRealization_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (realCtx : G8OrthodoxTauWitnessRealizationContext ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8OrthodoxTauShadowNormalFormSource_yields_pullback ctx
    (g8OrthodoxTauWitnessRealization_to_shadowSourceContext realCtx)

/-- The witness-realization context plus tau-side purity yields local
    no-off-critical orthodox zeros. -/
theorem g8OrthodoxTauWitnessRealization_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (realCtx : G8OrthodoxTauWitnessRealizationContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OrthodoxTauShadowNormalFormSource_noOffCriticalZeros ctx
    (g8OrthodoxTauWitnessRealization_to_shadowSourceContext realCtx)
    tauPurity

-- ============================================================
-- FALSIFIERS
-- ============================================================

/-- A boundary normal form outside the image of the abstract tau-witness
    normal-form projection. -/
structure G8TauNormalFormOutsideWitnessImage
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  nf : BoundaryNF
  noWitness :
    ∀ w : ctx.test.base.tauWitness,
      ctx.test.tauNormalForm w ≠ nf

/-- A boundary normal form outside the witness image refutes a total
    normal-form section. -/
theorem g8TauNormalFormOutsideWitnessImage_refutes_section
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (w : G8TauNormalFormOutsideWitnessImage ctx)
    (sec : G8TauNormalFormSection ctx) :
    False :=
  w.noWitness
    (sec.realizeBoundaryNF w.nf)
    (sec.realizeBoundaryNF_normalForm w.nf)

/-- An unrealized selected normal form refutes selected-image membership. -/
theorem g8TauShadowSelectedNormalFormUnrealized_refutes_selectedImage
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8TauShadowSelectedNormalFormUnrealized source) :
    ¬ G8TauSelectedNormalFormsInWitnessImage source := by
  intro hImage
  obtain ⟨tauW, hEq⟩ := hImage w.z w.offAxis
  exact w.noRealization tauW hEq

/-- An unrealized selected normal form refutes a total normal-form section. -/
theorem g8TauShadowSelectedNormalFormUnrealized_refutes_section
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8TauShadowSelectedNormalFormUnrealized source)
    (sec : G8TauNormalFormSection ctx) :
    False :=
  g8TauShadowSelectedNormalFormUnrealized_refutes_realization w
    (g8TauNormalFormSection_to_shadowSelectedRealization source sec)

/-- An unrealized selected normal form refutes the witness-realization
    context. -/
theorem g8TauShadowSelectedNormalFormUnrealized_refutes_realizationContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {realCtx : G8OrthodoxTauWitnessRealizationContext ctx}
    (w : G8TauShadowSelectedNormalFormUnrealized realCtx.source) :
    False :=
  g8TauShadowSelectedNormalFormUnrealized_refutes_section w
    realCtx.normalFormSection

end Tau.BookIII.Bridge
