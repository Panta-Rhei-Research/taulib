import TauLib.BookIII.Bridge.G8OrthodoxTauPreimageExistence

/-!
# TauLib.BookIII.Bridge.G8OrthodoxNormalizedAxisClass

Binary normalized axis class for the G8f orthodox/tau pullback corridor.

The exact axis-offset relation taught us a load-bearing lesson: tau
prime-polarity sees only the protected localization class (`0` for on-axis /
B-C balance, `1` for off-axis / B-C imbalance), not a metric magnitude of
receiving-side displacement.  This module gives the orthodox shadow the same
binary language.

The normalized relation compares:

* `0` if the receiving shadow is on the centered critical axis;
* `1` if the receiving shadow is off-axis;
* the tau prime-polarity axis offset.

Thus raw height/provenance and raw off-axis magnitude are diagnostic only.
The local contradiction corridor needs only the binary localization class.
This module does not prove the analytic xi chart, O3, divisor transfer, or the
global RH target.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- NORMALIZED AXIS CLASS
-- ============================================================

/-- Binary receiving-side axis class: `0` on the centered critical axis and
    `1` off-axis. -/
def normalizedAxisOffset (p : CriticalAxisShadow) : Nat :=
  if p.axisOffset = 0 then 0 else 1

/-- The normalized axis class is binary. -/
theorem normalizedAxisOffset_binary
    (p : CriticalAxisShadow) :
    normalizedAxisOffset p = 0 ∨
      normalizedAxisOffset p = 1 := by
  unfold normalizedAxisOffset
  by_cases h : p.axisOffset = 0
  · simp [h]
  · simp [h]

/-- The normalized axis class is zero exactly on the centered critical axis. -/
theorem normalizedAxisOffset_eq_zero_iff_onAxis
    (p : CriticalAxisShadow) :
    normalizedAxisOffset p = 0 ↔ OnCriticalAxis p := by
  unfold normalizedAxisOffset OnCriticalAxis
  by_cases h : p.axisOffset = 0
  · simp [h]
  · simp [h]

/-- The normalized axis class is one exactly off the centered critical axis. -/
theorem normalizedAxisOffset_eq_one_iff_offAxis
    (p : CriticalAxisShadow) :
    normalizedAxisOffset p = 1 ↔ ShadowOffAxis p := by
  unfold normalizedAxisOffset ShadowOffAxis OnCriticalAxis
  by_cases h : p.axisOffset = 0
  · simp [h]
  · simp [h]

/-- Off-axis receiving shadows normalize to class `1`. -/
theorem normalizedAxisOffset_eq_one_of_offAxis
    {p : CriticalAxisShadow}
    (hOffAxis : ShadowOffAxis p) :
    normalizedAxisOffset p = 1 :=
  (normalizedAxisOffset_eq_one_iff_offAxis p).mpr hOffAxis

/-- On-axis receiving shadows normalize to class `0`. -/
theorem normalizedAxisOffset_eq_zero_of_onAxis
    {p : CriticalAxisShadow}
    (hAxis : OnCriticalAxis p) :
    normalizedAxisOffset p = 0 :=
  (normalizedAxisOffset_eq_zero_iff_onAxis p).mpr hAxis

/-- Normalization forgets off-axis magnitude but preserves localization. -/
theorem normalizedAxisOffset_preserves_offAxis
    (p : CriticalAxisShadow) :
    ShadowOffAxis p ↔ normalizedAxisOffset p = 1 :=
  (normalizedAxisOffset_eq_one_iff_offAxis p).symm

-- ============================================================
-- NORMALIZED ORTHODOX/TAU RELATION
-- ============================================================

/-- Concrete orthodox/tau relation comparing only the binary localization
    class of the receiving shadow to the tau prime-polarity axis offset. -/
def G8OrthodoxTauNormalizedAxisRelated
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness) : Prop :=
  normalizedAxisOffset (source.centeredShadow z) =
    primePolarityAxisOffset (ctx.test.tauNormalForm w)

/-- The normalized axis relation as a `G8OffAxisChartRelation`. -/
def G8OrthodoxTauNormalizedAxisRelation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    G8OffAxisChartRelation
      (g8OrthodoxShadowAxisSource_to_chart source) :=
  fun z w => G8OrthodoxTauNormalizedAxisRelated source z w

/-- Related receiving/tau witnesses expose normalized axis-class equality. -/
theorem g8OrthodoxTauNormalizedAxisRelation_eq
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hRel : G8OrthodoxTauNormalizedAxisRelation source z w) :
    normalizedAxisOffset (source.centeredShadow z) =
      primePolarityAxisOffset (ctx.test.tauNormalForm w) :=
  hRel

/-- For normalized-related pairs, receiving on-axis status is equivalent to
    tau B/C balance. -/
theorem g8OrthodoxTauNormalizedAxisRelation_onAxis_iff_bcBalanced
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hRel : G8OrthodoxTauNormalizedAxisRelation source z w) :
    G8ChartCriticalAxis
      (g8OrthodoxShadowAxisSource_to_chart source) z ↔
      BCBalanced (ctx.test.tauNormalForm w) := by
  unfold G8ChartCriticalAxis OnCriticalAxis
  constructor
  · intro hAxis
    have hNorm :
        normalizedAxisOffset (source.centeredShadow z) = 0 :=
      normalizedAxisOffset_eq_zero_of_onAxis hAxis
    have hTau :
        primePolarityAxisOffset (ctx.test.tauNormalForm w) = 0 := by
      exact hRel ▸ hNorm
    exact
      (primePolarityAxisOffset_eq_zero_iff_bcBalanced
        (ctx.test.tauNormalForm w)).mp hTau
  · intro hBalanced
    have hTau :
        primePolarityAxisOffset (ctx.test.tauNormalForm w) = 0 :=
      (primePolarityAxisOffset_eq_zero_iff_bcBalanced
        (ctx.test.tauNormalForm w)).mpr hBalanced
    have hNorm :
        normalizedAxisOffset (source.centeredShadow z) = 0 := by
      exact hRel.trans hTau
    exact
      (normalizedAxisOffset_eq_zero_iff_onAxis
        (source.centeredShadow z)).mp hNorm

/-- Normalized-related off-axis preimages carry tau B/C imbalance. -/
theorem
    g8OrthodoxTauNormalizedAxisRelation_offAxis_relatedPreimage_bcImbalance
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hOffAxis :
      G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z)
    (hRel : G8OrthodoxTauNormalizedAxisRelation source z w) :
    TauBCImbalance (ctx.test.tauNormalForm w) := by
  have hNorm :
      normalizedAxisOffset (source.centeredShadow z) = 1 :=
    normalizedAxisOffset_eq_one_of_offAxis hOffAxis
  have hTau :
      primePolarityAxisOffset (ctx.test.tauNormalForm w) = 1 := by
    exact hRel ▸ hNorm
  exact
    (primePolarityAxisOffset_eq_one_iff_bcImbalance
      (ctx.test.tauNormalForm w)).mp hTau

/-- Normalized-related off-critical preimages carry tau critical imbalance. -/
theorem
    g8OrthodoxTauNormalizedAxisRelation_offCritical_relatedPreimage_tauCritical
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hz : ClassicalOffCriticalZero ctx.test.base z)
    (hRel : G8OrthodoxTauNormalizedAxisRelation source z w) :
    TauCriticalImbalance (ctx.test.tauNormalForm w) :=
  (tauCriticalImbalance_iff_bcImbalance
    (ctx.test.tauNormalForm w)).mpr
    (g8OrthodoxTauNormalizedAxisRelation_offAxis_relatedPreimage_bcImbalance
      source z w
      (g8OrthodoxShadowAxisSource_offCritical_to_chartOffAxis
        source z hz)
      hRel)

-- ============================================================
-- NORMALIZED PREIMAGE EXISTENCE
-- ============================================================

/-- Off-axis shadows have tau preimages for the normalized axis relation. -/
def G8OrthodoxTauNormalizedAxisPreimagesExist
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) : Prop :=
  ∀ z : ctx.test.base.orthodoxZero,
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z →
      ∃ w : ctx.test.base.tauWitness,
        G8OrthodoxTauNormalizedAxisRelated source z w

/-- Pointwise unit tau witnesses are enough for normalized preimage
    existence.  No raw off-axis unit-normalization is required. -/
theorem g8OrthodoxTauUnitPreimages_to_normalizedPreimages
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (hTau : G8OrthodoxTauUnitAxisPreimagesExist source) :
    G8OrthodoxTauNormalizedAxisPreimagesExist source := by
  intro z hOffAxis
  obtain ⟨w, hTauUnit⟩ := hTau z hOffAxis
  exact ⟨w, by
    unfold G8OrthodoxTauNormalizedAxisRelated
    exact
      (normalizedAxisOffset_eq_one_of_offAxis hOffAxis).trans
        hTauUnit.symm⟩

/-- Unit tau witnesses supply the existing preimage field for the normalized
    axis relation. -/
theorem g8OrthodoxTauUnitPreimages_to_normalizedOffAxisPreimageExists
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (hTau : G8OrthodoxTauUnitAxisPreimagesExist source) :
    G8OffAxisTauPreimageExists
      (g8OrthodoxShadowAxisSource_to_chart source)
      (G8OrthodoxTauNormalizedAxisRelation source) := by
  intro z hOffAxis
  exact g8OrthodoxTauUnitPreimages_to_normalizedPreimages
    source hTau z hOffAxis

/-- Normalized preimage-existence context.

Compared with `G8OrthodoxTauPreimageExistenceContext`, the raw receiving
offset no longer needs to be unit-normalized.  Only the binary class is used. -/
structure G8OrthodoxNormalizedAxisPreimageContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  source : G8OrthodoxShadowAxisSource ctx
  unitTauPreimages :
    G8OrthodoxTauUnitAxisPreimagesExist source
  tauWitness :
    G8OffAxisTauWitnessRealization
      (g8OrthodoxShadowAxisSource_to_chart source)
  offAxisGuard :
    G8OffAxisChartOnlyGhostGuard
      (g8OrthodoxShadowAxisSource_to_chart source)

/-- The normalized preimage context supplies decomposed chart faithfulness. -/
def g8OrthodoxNormalizedAxisPreimage_to_decomposition
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (normCtx : G8OrthodoxNormalizedAxisPreimageContext ctx) :
    G8OffAxisChartFaithfulnessDecomposition
      (g8OrthodoxShadowAxisSource_to_chart normCtx.source) where
  shadowTauRelated :=
    G8OrthodoxTauNormalizedAxisRelation normCtx.source
  chartReadable := by
    intro z hz
    exact
      g8OrthodoxShadowAxisSource_offCritical_to_chartOffAxis
        normCtx.source z hz
  tauPreimageExists :=
    g8OrthodoxTauUnitPreimages_to_normalizedOffAxisPreimageExists
      normCtx.source normCtx.unitTauPreimages
  relationPreservesBCImbalance := by
    intro z w hOffAxis hRel
    exact
      g8OrthodoxTauNormalizedAxisRelation_offAxis_relatedPreimage_bcImbalance
        normCtx.source z w hOffAxis hRel
  tauWitness := normCtx.tauWitness
  offAxisGuard := normCtx.offAxisGuard

/-- The normalized preimage context yields the local one-sided pullback. -/
theorem g8OrthodoxNormalizedAxisPreimage_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (normCtx : G8OrthodoxNormalizedAxisPreimageContext ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8OffAxisChartFaithfulnessDecomposition_yields_pullback
    ctx (g8OrthodoxShadowAxisSource_to_chart normCtx.source)
    (g8OrthodoxNormalizedAxisPreimage_to_decomposition normCtx)

/-- The normalized preimage context plus tau-side purity yields the local
    no-off-critical-zero conclusion. -/
theorem g8OrthodoxNormalizedAxisPreimage_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (normCtx : G8OrthodoxNormalizedAxisPreimageContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OffAxisChartFaithfulnessDecomposition_noOffCriticalZeros
    ctx (g8OrthodoxShadowAxisSource_to_chart normCtx.source)
    (g8OrthodoxNormalizedAxisPreimage_to_decomposition normCtx)
    tauPurity

-- ============================================================
-- DIAGNOSTICS AND FALSIFIER PRESSURE
-- ============================================================

/-- A raw receiving offset greater than `1` is diagnostic only under the
    normalized axis relation. -/
structure G8OrthodoxNormalizedAxisMagnitudeDiagnostic
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  offAxis :
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z
  gtOne : 1 < (source.centeredShadow z).axisOffset

/-- Large raw off-axis magnitude is not a localization refutation for the
    normalized relation. -/
theorem g8OrthodoxNormalizedAxisMagnitudeDiagnostic_not_refutation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (_w : G8OrthodoxNormalizedAxisMagnitudeDiagnostic source) :
    True :=
  trivial

/-- Even with raw offset greater than `1`, a unit tau witness gives a
    normalized-axis relation. -/
theorem g8OrthodoxNormalizedAxis_related_of_largeOffset_and_unitTau
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8OrthodoxNormalizedAxisMagnitudeDiagnostic source)
    (tauW : ctx.test.base.tauWitness)
    (hTauUnit :
      primePolarityAxisOffset (ctx.test.tauNormalForm tauW) = 1) :
    G8OrthodoxTauNormalizedAxisRelated source w.z tauW := by
  unfold G8OrthodoxTauNormalizedAxisRelated
  exact
    (normalizedAxisOffset_eq_one_of_offAxis w.offAxis).trans
      hTauUnit.symm

/-- A pointwise unit tau preimage unavailable witness remains the decisive
    preimage falsifier for the normalized relation. -/
theorem
    g8OrthodoxTauUnitPreimageUnavailable_refutes_normalizedPreimages
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8OrthodoxTauUnitPreimageUnavailableWitness source) :
    ¬ G8OrthodoxTauNormalizedAxisPreimagesExist source := by
  intro h
  obtain ⟨tauW, hRel⟩ := h w.z w.offAxis
  have hNorm :
      normalizedAxisOffset (source.centeredShadow w.z) = 1 :=
    normalizedAxisOffset_eq_one_of_offAxis w.offAxis
  have hTauUnit :
      primePolarityAxisOffset (ctx.test.tauNormalForm tauW) = 1 := by
    exact hRel ▸ hNorm
  exact w.noUnitPreimage tauW hTauUnit

end Tau.BookIII.Bridge
