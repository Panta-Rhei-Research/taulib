import TauLib.BookIII.Bridge.G8OrthodoxTauWitnessRealization

/-!
# TauLib.BookIII.Bridge.G8CanonicalBoundaryWitnessRealization

Canonical boundary-witness realization for the G8f corridor.

The preceding witness-realization module exposed a deliberately strong
section `BoundaryNF -> tauWitness`.  This module tightens that proof shape:
the G8f corridor should realize boundary normal forms with provenance, namely
normal forms known to arise from a finite primorial-stage boundary projection.

The module therefore separates three layers:

* `BoundaryNFRealizable`: a boundary normal form is in the image of
  `boundary_normal_form x k`;
* `G8CanonicalBoundaryWitness`: a witness object carrying the normal form and
  its finite-stage provenance;
* `G8CanonicalBoundaryWitnessModel`: an embedding of such canonical boundary
  witnesses into the abstract `tauWitness` carrier of the local pullback
  context.

This is still local proof engineering.  No analytic xi chart, O3
correspondence, divisor transfer, global RH, or tau-side purity theorem is
completed here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- CANONICAL BOUNDARY NORMAL-FORM PROVENANCE
-- ============================================================

/-- A boundary normal form is realizable when it is actually produced by the
    finite primorial-stage boundary normal-form map. -/
def BoundaryNFRealizable (nf : BoundaryNF) : Prop :=
  ∃ x k : Nat, boundary_normal_form x k = nf

/-- A canonical boundary witness packages a boundary normal form together with
    the finite primorial-stage data that produced it. -/
structure G8CanonicalBoundaryWitness where
  nf : BoundaryNF
  sourceValue : Nat
  stage : Nat
  normalForm_eq :
    boundary_normal_form sourceValue stage = nf

/-- Every canonical boundary witness gives a realizable boundary normal form. -/
theorem g8CanonicalBoundaryWitness_realizable
    (w : G8CanonicalBoundaryWitness) :
    BoundaryNFRealizable w.nf := by
  exact ⟨w.sourceValue, w.stage, w.normalForm_eq⟩

/-- Constructor for the canonical witness associated to one finite
    primorial-stage boundary projection. -/
def g8CanonicalBoundaryWitnessOfStage
    (x k : Nat) : G8CanonicalBoundaryWitness where
  nf := boundary_normal_form x k
  sourceValue := x
  stage := k
  normalForm_eq := rfl

/-- The computed on-axis sample has finite-stage provenance. -/
def g8TauSampleOnAxisCanonicalBoundaryWitness :
    G8CanonicalBoundaryWitness :=
  { nf := g8TauSampleOnAxisBoundaryNF
    sourceValue := 0
    stage := 3
    normalForm_eq := rfl }

/-- The computed off-axis sample has finite-stage provenance. -/
def g8TauSampleOffAxisCanonicalBoundaryWitness :
    G8CanonicalBoundaryWitness :=
  { nf := g8TauSampleOffAxisBoundaryNF
    sourceValue := 42
    stage := 3
    normalForm_eq := rfl }

/-- The on-axis sample boundary normal form is realizable. -/
theorem g8TauSampleOnAxisBoundaryNF_realizable :
    BoundaryNFRealizable g8TauSampleOnAxisBoundaryNF := by
  exact ⟨0, 3, rfl⟩

/-- The off-axis sample boundary normal form is realizable. -/
theorem g8TauSampleOffAxisBoundaryNF_realizable :
    BoundaryNFRealizable g8TauSampleOffAxisBoundaryNF := by
  exact ⟨42, 3, rfl⟩

-- ============================================================
-- SELECTED NORMAL-FORM PROVENANCE
-- ============================================================

/-- On-axis centered shadows select exactly the on-axis sample normal form. -/
theorem g8TauShadowSelectedNormalForm_onAxis_eq_sample
    (p : CriticalAxisShadow)
    (hAxis : OnCriticalAxis p) :
    g8TauShadowSelectedNormalForm p = g8TauSampleOnAxisBoundaryNF := by
  unfold g8TauShadowSelectedNormalForm OnCriticalAxis at *
  simp [hAxis]

/-- Off-axis centered shadows select exactly the off-axis sample normal form. -/
theorem g8TauShadowSelectedNormalForm_offAxis_eq_sample
    (p : CriticalAxisShadow)
    (hOffAxis : ShadowOffAxis p) :
    g8TauShadowSelectedNormalForm p = g8TauSampleOffAxisBoundaryNF := by
  unfold g8TauShadowSelectedNormalForm ShadowOffAxis OnCriticalAxis at *
  simp [hOffAxis]

/-- The chart-selected normal forms for readable off-axis shadows are
    finite-stage realizable. -/
def G8TauSelectedBoundaryNormalFormsRealizable
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) : Prop :=
  ∀ z : ctx.test.base.orthodoxZero,
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z →
      BoundaryNFRealizable
        (g8TauShadowSelectedNormalForm (source.centeredShadow z))

/-- The concrete shadow selector always chooses a finite-stage realizable
    normal form for readable off-axis shadows. -/
theorem g8TauShadowSelectedNormalForms_realizable
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    G8TauSelectedBoundaryNormalFormsRealizable source := by
  intro z hOffAxis
  rw [
    g8TauShadowSelectedNormalForm_offAxis_eq_sample
      (source.centeredShadow z)
      (g8OrthodoxShadowAxisSource_chartOffAxis_to_sourceOffAxis
        source z hOffAxis)]
  exact g8TauSampleOffAxisBoundaryNF_realizable

/-- Canonical boundary realization of the chart-selected normal form for each
    readable off-axis shadow. -/
structure G8TauSelectedCanonicalBoundaryRealization
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  realize :
    ∀ (z : ctx.test.base.orthodoxZero)
      (_hOffAxis :
        G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z),
      G8CanonicalBoundaryWitness
  realize_selected :
    ∀ (z : ctx.test.base.orthodoxZero)
      (hOffAxis :
        G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z),
      (realize z hOffAxis).nf =
        g8TauShadowSelectedNormalForm (source.centeredShadow z)

/-- The concrete selector gives a canonical boundary witness for every
    readable off-axis shadow. -/
def g8TauShadowSelectedCanonicalBoundaryRealization
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    G8TauSelectedCanonicalBoundaryRealization source where
  realize := fun _z _hOffAxis =>
    g8TauSampleOffAxisCanonicalBoundaryWitness
  realize_selected := by
    intro z hOffAxis
    exact
      (g8TauShadowSelectedNormalForm_offAxis_eq_sample
        (source.centeredShadow z)
        (g8OrthodoxShadowAxisSource_chartOffAxis_to_sourceOffAxis
          source z hOffAxis)).symm

-- ============================================================
-- EMBEDDING INTO THE ABSTRACT TAU-WITNESS CARRIER
-- ============================================================

/-- A model embedding canonical boundary witnesses into the abstract
    tau-witness carrier of the local pullback context. -/
structure G8CanonicalBoundaryWitnessModel
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  realizeCanonical :
    G8CanonicalBoundaryWitness → ctx.test.base.tauWitness
  realizeCanonical_normalForm :
    ∀ w : G8CanonicalBoundaryWitness,
      ctx.test.tauNormalForm (realizeCanonical w) = w.nf

/-- A canonical boundary-witness model realizes the selected canonical
    boundary witnesses in the abstract tau-witness carrier. -/
def g8CanonicalBoundaryWitnessModel_to_shadowSelectedRealization
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (model : G8CanonicalBoundaryWitnessModel ctx)
    (selected : G8TauSelectedCanonicalBoundaryRealization source) :
    G8TauShadowSelectedNormalFormRealization source where
  realize := fun z hOffAxis =>
    model.realizeCanonical (selected.realize z hOffAxis)
  realize_selected := by
    intro z hOffAxis
    rw [model.realizeCanonical_normalForm]
    exact selected.realize_selected z hOffAxis

/-- A canonical boundary-witness model puts selected off-axis normal forms in
    the abstract witness image. -/
theorem
    g8CanonicalBoundaryWitnessModel_selectedNormalFormsInWitnessImage
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (model : G8CanonicalBoundaryWitnessModel ctx)
    (selected : G8TauSelectedCanonicalBoundaryRealization source) :
    G8TauSelectedNormalFormsInWitnessImage source := by
  intro z hOffAxis
  exact
    ⟨model.realizeCanonical (selected.realize z hOffAxis), by
      rw [model.realizeCanonical_normalForm]
      exact selected.realize_selected z hOffAxis⟩

/-- A canonical boundary-witness model supplies the generic normal-form
    witness source for the selected off-axis normal forms. -/
def g8CanonicalBoundaryWitnessModel_to_nfWitnessSource
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (model : G8CanonicalBoundaryWitnessModel ctx)
    (selected : G8TauSelectedCanonicalBoundaryRealization source) :
    G8TauOffAxisNormalFormWitnessSource source :=
  g8TauShadowSelectedRealization_to_nfWitnessSource
    (g8CanonicalBoundaryWitnessModel_to_shadowSelectedRealization
      model selected)

/-- A canonical boundary-witness model supplies B/C-imbalance witnesses for
    readable off-axis shadows. -/
theorem g8CanonicalBoundaryWitnessModel_to_bcImbalanceWitnesses
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (model : G8CanonicalBoundaryWitnessModel ctx)
    (selected : G8TauSelectedCanonicalBoundaryRealization source) :
    G8OrthodoxTauBCImbalanceWitnessesExist source :=
  g8TauOffAxisNormalFormWitnessSource_to_bcImbalanceWitnesses
    (g8CanonicalBoundaryWitnessModel_to_nfWitnessSource model selected)

-- ============================================================
-- CORRIDOR CONTEXT
-- ============================================================

/-- Canonical boundary-witness realization context for the selected
    normal-form corridor. -/
structure G8CanonicalBoundaryWitnessRealizationContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  source : G8OrthodoxShadowAxisSource ctx
  witnessModel : G8CanonicalBoundaryWitnessModel ctx
  selected :
    G8TauSelectedCanonicalBoundaryRealization source :=
      g8TauShadowSelectedCanonicalBoundaryRealization source
  tauWitness :
    G8OffAxisTauWitnessRealization
      (g8OrthodoxShadowAxisSource_to_chart source)
  offAxisGuard :
    G8OffAxisChartOnlyGhostGuard
      (g8OrthodoxShadowAxisSource_to_chart source)

/-- The canonical boundary-witness context supplies the chart-shadow selected
    normal-form source context. -/
def g8CanonicalBoundaryWitnessRealization_to_shadowSourceContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (realCtx : G8CanonicalBoundaryWitnessRealizationContext ctx) :
    G8OrthodoxTauShadowNormalFormSourceContext ctx where
  source := realCtx.source
  realization :=
    g8CanonicalBoundaryWitnessModel_to_shadowSelectedRealization
      realCtx.witnessModel realCtx.selected
  tauWitness := realCtx.tauWitness
  offAxisGuard := realCtx.offAxisGuard

/-- The canonical boundary-witness context yields the local one-sided
    pullback. -/
theorem g8CanonicalBoundaryWitnessRealization_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (realCtx : G8CanonicalBoundaryWitnessRealizationContext ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8OrthodoxTauShadowNormalFormSource_yields_pullback ctx
    (g8CanonicalBoundaryWitnessRealization_to_shadowSourceContext
      realCtx)

/-- The canonical boundary-witness context plus tau-side purity yields local
    no-off-critical orthodox zeros. -/
theorem g8CanonicalBoundaryWitnessRealization_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (realCtx : G8CanonicalBoundaryWitnessRealizationContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OrthodoxTauShadowNormalFormSource_noOffCriticalZeros ctx
    (g8CanonicalBoundaryWitnessRealization_to_shadowSourceContext
      realCtx)
    tauPurity

-- ============================================================
-- FALSIFIERS
-- ============================================================

/-- A chart-selected off-axis boundary normal form without finite-stage
    provenance. -/
structure G8SelectedBoundaryNormalFormNotRealizable
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  offAxis :
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z
  notRealizable :
    ¬ BoundaryNFRealizable
      (g8TauShadowSelectedNormalForm (source.centeredShadow z))

/-- A non-realizable selected normal form refutes selected realizability. -/
theorem
    g8SelectedBoundaryNormalFormNotRealizable_refutes_realizability
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8SelectedBoundaryNormalFormNotRealizable source) :
    ¬ G8TauSelectedBoundaryNormalFormsRealizable source := by
  intro hRealizable
  exact w.notRealizable (hRealizable w.z w.offAxis)

/-- A non-realizable selected normal form refutes canonical selected
    realization. -/
theorem
    g8SelectedBoundaryNormalFormNotRealizable_refutes_selectedCanonical
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8SelectedBoundaryNormalFormNotRealizable source)
    (selected : G8TauSelectedCanonicalBoundaryRealization source) :
    False := by
  exact
    w.notRealizable
      (by
        rw [← selected.realize_selected w.z w.offAxis]
        exact
          g8CanonicalBoundaryWitness_realizable
            (selected.realize w.z w.offAxis))

/-- A canonical boundary witness whose normal form is outside the abstract
    tau-witness image. -/
structure G8CanonicalBoundaryWitnessOutsideAbstractImage
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  witness : G8CanonicalBoundaryWitness
  noAbstractWitness :
    ∀ w : ctx.test.base.tauWitness,
      ctx.test.tauNormalForm w ≠ witness.nf

/-- A canonical boundary witness outside the abstract witness image refutes an
    embedding model. -/
theorem
    g8CanonicalBoundaryWitnessOutsideAbstractImage_refutes_model
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (w : G8CanonicalBoundaryWitnessOutsideAbstractImage ctx)
    (model : G8CanonicalBoundaryWitnessModel ctx) :
    False :=
  w.noAbstractWitness
    (model.realizeCanonical w.witness)
    (model.realizeCanonical_normalForm w.witness)

/-- An unrealized selected normal form refutes the canonical boundary-witness
    realization context. -/
theorem
    g8TauShadowSelectedNormalFormUnrealized_refutes_canonicalContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {realCtx : G8CanonicalBoundaryWitnessRealizationContext ctx}
    (w : G8TauShadowSelectedNormalFormUnrealized realCtx.source) :
    False :=
  g8TauShadowSelectedNormalFormUnrealized_refutes_realization w
    (g8CanonicalBoundaryWitnessModel_to_shadowSelectedRealization
      realCtx.witnessModel realCtx.selected)

end Tau.BookIII.Bridge
