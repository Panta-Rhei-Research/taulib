import TauLib.BookIII.Bridge.G8OrthodoxTauAxisRelation

/-!
# TauLib.BookIII.Bridge.G8OrthodoxTauPreimageExistence

First proof-facing decomposition of the G8f tau-preimage existence hinge.

After `G8OrthodoxTauAxisRelation`, an orthodox shadow and a tau witness are
related exactly when their localization-bearing axis offsets agree.  This
module isolates what that now means:

* the tau prime-polarity axis offset is binary (`0` or `1`);
* therefore exact axis-offset preimages require the receiving off-axis shadow
  to be unit-normalized, not merely nonzero;
* under that unit-normalization, pointwise unit tau witnesses imply the
  existing `offAxisHasTauPreimage` field;
* if a receiving off-axis shadow has axis offset greater than `1`, the exact
  axis relation has no tau preimage.

This is local chart theory and falsifier pressure.  It does not prove the
actual analytic chart, O3, divisor transfer, or the global RH target.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- BINARY TAU AXIS-OFFSET FACTS
-- ============================================================

/-- The tau prime-polarity axis offset is binary. -/
theorem primePolarityAxisOffset_binary
    (nf : BoundaryNF) :
    primePolarityAxisOffset nf = 0 ∨
      primePolarityAxisOffset nf = 1 := by
  unfold primePolarityAxisOffset
  by_cases h : nf.b_part = nf.c_part
  · simp [h]
  · simp [h]

/-- The tau prime-polarity axis offset is always at most `1`. -/
theorem primePolarityAxisOffset_le_one
    (nf : BoundaryNF) :
    primePolarityAxisOffset nf ≤ 1 := by
  rcases primePolarityAxisOffset_binary nf with h | h
  · rw [h]
    exact Nat.zero_le 1
  · rw [h]

/-- The unit tau axis offset is exactly B/C imbalance. -/
theorem primePolarityAxisOffset_eq_one_iff_bcImbalance
    (nf : BoundaryNF) :
    primePolarityAxisOffset nf = 1 ↔ TauBCImbalance nf := by
  unfold primePolarityAxisOffset TauBCImbalance BCBalanced
  by_cases h : nf.b_part = nf.c_part
  · simp [h]
  · simp [h]

/-- The centered shadow off-axis predicate is exactly nonzero axis offset. -/
theorem criticalAxisShadow_offAxis_iff_axisOffset_ne_zero
    (p : CriticalAxisShadow) :
    ShadowOffAxis p ↔ p.axisOffset ≠ 0 := by
  rfl

-- ============================================================
-- PREIMAGE EXISTENCE AS AN AXIS-TARGET REALIZATION OBLIGATION
-- ============================================================

/-- A concrete axis target is realized by some tau witness. -/
def G8OrthodoxTauAxisTargetRealized
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero) : Prop :=
  ∃ w : ctx.test.base.tauWitness,
    G8OrthodoxTauAxisRelated source z w

/-- Off-axis shadows have concrete axis-related tau preimages. -/
def G8OrthodoxTauAxisTargetPreimagesExist
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) : Prop :=
  ∀ z : ctx.test.base.orthodoxZero,
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z →
      G8OrthodoxTauAxisTargetRealized source z

/-- Target-preimage existence is exactly the existing preimage field for the
    concrete axis relation. -/
theorem g8OrthodoxTauAxisTargetPreimages_to_offAxisPreimageExists
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (h : G8OrthodoxTauAxisTargetPreimagesExist source) :
    G8OffAxisTauPreimageExists
      (g8OrthodoxShadowAxisSource_to_chart source)
      (G8OrthodoxTauAxisRelation source) := by
  intro z hOffAxis
  exact h z hOffAxis

/-- The existing preimage field is also exactly target-preimage existence for
    the concrete axis relation. -/
theorem g8OrthodoxTauAxis_offAxisPreimageExists_to_targetPreimages
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (h :
      G8OffAxisTauPreimageExists
        (g8OrthodoxShadowAxisSource_to_chart source)
        (G8OrthodoxTauAxisRelation source)) :
    G8OrthodoxTauAxisTargetPreimagesExist source := by
  intro z hOffAxis
  exact h z hOffAxis

/-- The concrete preimage field and target-realization form are equivalent. -/
theorem g8OrthodoxTauAxisPreimageExists_iff_targetPreimages
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    G8OffAxisTauPreimageExists
      (g8OrthodoxShadowAxisSource_to_chart source)
      (G8OrthodoxTauAxisRelation source) ↔
      G8OrthodoxTauAxisTargetPreimagesExist source := by
  constructor
  · exact
      g8OrthodoxTauAxis_offAxisPreimageExists_to_targetPreimages
        source
  · exact
      g8OrthodoxTauAxisTargetPreimages_to_offAxisPreimageExists
        source

-- ============================================================
-- UNIT-NORMALIZED DECOMPOSITION
-- ============================================================

/-- The receiving off-axis shadow is binary-normalized: every off-axis
    receiving shadow has localization-bearing offset `1`.

This is the chart-normalization target exposed by the exact axis relation.
Without it, a receiving offset greater than `1` cannot be matched by the
tau prime-polarity offset. -/
def G8OrthodoxOffAxisUnitNormalized
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) : Prop :=
  ∀ z : ctx.test.base.orthodoxZero,
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z →
      (source.centeredShadow z).axisOffset = 1

/-- Pointwise unit tau preimages are available for off-axis receiving
    shadows.  The witness may still depend on the orthodox point. -/
def G8OrthodoxTauUnitAxisPreimagesExist
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) : Prop :=
  ∀ z : ctx.test.base.orthodoxZero,
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z →
      ∃ w : ctx.test.base.tauWitness,
        primePolarityAxisOffset (ctx.test.tauNormalForm w) = 1

/-- Unit normalization plus pointwise unit tau witnesses yields exact
    axis-target preimage existence. -/
theorem g8OrthodoxTauUnitPreimages_to_axisTargetPreimages
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (hUnit : G8OrthodoxOffAxisUnitNormalized source)
    (hTau : G8OrthodoxTauUnitAxisPreimagesExist source) :
    G8OrthodoxTauAxisTargetPreimagesExist source := by
  intro z hOffAxis
  obtain ⟨w, hTauUnit⟩ := hTau z hOffAxis
  exact ⟨w, by
    unfold G8OrthodoxTauAxisRelated
    exact (hUnit z hOffAxis).trans hTauUnit.symm⟩

/-- Unit normalization plus pointwise unit tau witnesses supplies the existing
    concrete preimage field. -/
theorem g8OrthodoxTauUnitPreimages_to_offAxisPreimageExists
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (hUnit : G8OrthodoxOffAxisUnitNormalized source)
    (hTau : G8OrthodoxTauUnitAxisPreimagesExist source) :
    G8OffAxisTauPreimageExists
      (g8OrthodoxShadowAxisSource_to_chart source)
      (G8OrthodoxTauAxisRelation source) :=
  g8OrthodoxTauAxisTargetPreimages_to_offAxisPreimageExists
    source
    (g8OrthodoxTauUnitPreimages_to_axisTargetPreimages
      source hUnit hTau)

/-- Preimage-existence context decomposed into the two new proof-facing
    obligations: unit chart normalization and pointwise unit tau witnesses. -/
structure G8OrthodoxTauPreimageExistenceContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  source : G8OrthodoxShadowAxisSource ctx
  offAxisUnitNormalized :
    G8OrthodoxOffAxisUnitNormalized source
  unitTauPreimages :
    G8OrthodoxTauUnitAxisPreimagesExist source
  tauWitness :
    G8OffAxisTauWitnessRealization
      (g8OrthodoxShadowAxisSource_to_chart source)
  offAxisGuard :
    G8OffAxisChartOnlyGhostGuard
      (g8OrthodoxShadowAxisSource_to_chart source)

/-- The decomposed preimage-existence context supplies the previous concrete
    axis-relation context. -/
def g8OrthodoxTauPreimageExistence_to_relationContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (preCtx : G8OrthodoxTauPreimageExistenceContext ctx) :
    G8OrthodoxTauAxisRelationContext ctx where
  source := preCtx.source
  offAxisHasTauPreimage :=
    g8OrthodoxTauUnitPreimages_to_offAxisPreimageExists
      preCtx.source preCtx.offAxisUnitNormalized
      preCtx.unitTauPreimages
  tauWitness := preCtx.tauWitness
  offAxisGuard := preCtx.offAxisGuard

/-- The decomposed preimage-existence context supplies the local one-sided
    pullback. -/
theorem g8OrthodoxTauPreimageExistence_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (preCtx : G8OrthodoxTauPreimageExistenceContext ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8OrthodoxTauAxisRelation_yields_pullback ctx
    (g8OrthodoxTauPreimageExistence_to_relationContext preCtx)

/-- The decomposed preimage-existence context plus tau-side purity yields the
    local no-off-critical-zero conclusion. -/
theorem g8OrthodoxTauPreimageExistence_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (preCtx : G8OrthodoxTauPreimageExistenceContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OrthodoxTauAxisRelation_noOffCriticalZeros ctx
    (g8OrthodoxTauPreimageExistence_to_relationContext preCtx)
    tauPurity

-- ============================================================
-- FALSIFIERS AND PRESSURE POINTS
-- ============================================================

/-- A receiving off-axis shadow whose axis offset is not unit-normalized. -/
structure G8OrthodoxOffAxisNonUnitShadowWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  offAxis :
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z
  notUnit : (source.centeredShadow z).axisOffset ≠ 1

/-- A non-unit off-axis shadow refutes unit normalization. -/
theorem g8OrthodoxOffAxisNonUnitShadow_refutes_unitNormalization
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8OrthodoxOffAxisNonUnitShadowWitness source) :
    ¬ G8OrthodoxOffAxisUnitNormalized source := by
  intro h
  exact w.notUnit (h w.z w.offAxis)

/-- An off-axis shadow with axis offset greater than `1` has no preimage under
    the exact tau prime-polarity axis relation. -/
theorem g8OrthodoxTauAxis_noPreimage_of_axisOffset_gt_one
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (hgt : 1 < (source.centeredShadow z).axisOffset) :
    ∀ w : ctx.test.base.tauWitness,
      ¬ G8OrthodoxTauAxisRelated source z w := by
  intro w hRel
  have hTauLe :
      primePolarityAxisOffset (ctx.test.tauNormalForm w) ≤ 1 :=
    primePolarityAxisOffset_le_one (ctx.test.tauNormalForm w)
  have hTauGt :
      1 < primePolarityAxisOffset (ctx.test.tauNormalForm w) := by
    rw [← hRel]
    exact hgt
  exact (Nat.not_lt_of_ge hTauLe) hTauGt

/-- A greater-than-one receiving offset refutes target-preimage existence. -/
structure G8OrthodoxTauAxisTooLargeOffsetWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  offAxis :
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z
  gtOne : 1 < (source.centeredShadow z).axisOffset

/-- Greater-than-one offset witnesses refute exact target-preimage existence. -/
theorem g8OrthodoxTauAxisTooLargeOffset_refutes_targetPreimages
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8OrthodoxTauAxisTooLargeOffsetWitness source) :
    ¬ G8OrthodoxTauAxisTargetPreimagesExist source := by
  intro h
  obtain ⟨tauW, hRel⟩ := h w.z w.offAxis
  exact
    (g8OrthodoxTauAxis_noPreimage_of_axisOffset_gt_one
      source w.z w.gtOne tauW) hRel

/-- Greater-than-one offset witnesses refute the decomposed preimage context. -/
theorem g8OrthodoxTauAxisTooLargeOffset_refutes_preimageContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {preCtx : G8OrthodoxTauPreimageExistenceContext ctx}
    (w : G8OrthodoxTauAxisTooLargeOffsetWitness preCtx.source) :
    False :=
  g8OrthodoxTauAxisTooLargeOffset_refutes_targetPreimages w
    (g8OrthodoxTauUnitPreimages_to_axisTargetPreimages
      preCtx.source preCtx.offAxisUnitNormalized
      preCtx.unitTauPreimages)

/-- A pointwise unit tau preimage is unavailable for an off-axis receiving
    shadow. -/
structure G8OrthodoxTauUnitPreimageUnavailableWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  offAxis :
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z
  noUnitPreimage :
    ∀ w : ctx.test.base.tauWitness,
      primePolarityAxisOffset (ctx.test.tauNormalForm w) ≠ 1

/-- A pointwise unit-unavailability witness refutes pointwise unit preimages. -/
theorem g8OrthodoxTauUnitPreimageUnavailable_refutes_unitPreimages
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8OrthodoxTauUnitPreimageUnavailableWitness source) :
    ¬ G8OrthodoxTauUnitAxisPreimagesExist source := by
  intro h
  obtain ⟨tauW, hUnit⟩ := h w.z w.offAxis
  exact w.noUnitPreimage tauW hUnit

end Tau.BookIII.Bridge
