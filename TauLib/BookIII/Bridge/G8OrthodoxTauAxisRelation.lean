import TauLib.BookIII.Bridge.G8OrthodoxPrimePolarityAxisPullback

/-!
# TauLib.BookIII.Bridge.G8OrthodoxTauAxisRelation

Concrete axis-coordinate relation for the G8f orthodox/tau pullback.

`G8OrthodoxPrimePolarityAxisPullback` still accepted an arbitrary
`shadowTauRelated` relation, together with a proof that related pairs align
their localization-bearing axis offsets.  This module makes the relation
itself concrete:

* an orthodox shadow and tau witness are related exactly when their axis
  offsets agree;
* axis-offset alignment is then theorem-backed by definition;
* off-critical related preimages still force tau B/C imbalance and tau
  critical imbalance;
* preimage existence remains an explicit field for the next hard wave.

This is local chart theory.  It does not construct all preimages, prove O3,
classify zero divisors, or prove the global RH target.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CONCRETE ORTHODOX/TAU AXIS RELATION
-- ============================================================

/-- Concrete orthodox/tau relation at the G8f localization layer.

The relation only compares the localization-bearing axis offset.  It does not
compare height/provenance data and does not assert divisor equality. -/
def G8OrthodoxTauAxisRelated
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness) : Prop :=
  (source.centeredShadow z).axisOffset =
    primePolarityAxisOffset (ctx.test.tauNormalForm w)

/-- The concrete axis-coordinate relation as a `G8OffAxisChartRelation`. -/
def G8OrthodoxTauAxisRelation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    G8OffAxisChartRelation
      (g8OrthodoxShadowAxisSource_to_chart source) :=
  fun z w => G8OrthodoxTauAxisRelated source z w

/-- The concrete axis relation is axis-offset aligned by definition. -/
theorem g8OrthodoxTauAxisRelation_axisOffsetAligned
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    G8PrimePolarityAxisOffsetAlignment
      (g8OrthodoxShadowAxisSource_to_chart source)
      (G8OrthodoxTauAxisRelation source) := by
  intro z w hRel
  exact hRel

/-- Related receiving/tau witnesses expose the axis-offset equality. -/
theorem g8OrthodoxTauAxisRelation_axisOffset_eq
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hRel : G8OrthodoxTauAxisRelation source z w) :
    ((g8OrthodoxShadowAxisSource_to_chart source).centeredShadow z).axisOffset =
      primePolarityAxisOffset (ctx.test.tauNormalForm w) :=
  hRel

/-- For related pairs, receiving on-axis status is equivalent to tau B/C
    balance. -/
theorem g8OrthodoxTauAxisRelation_onAxis_iff_bcBalanced
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hRel : G8OrthodoxTauAxisRelation source z w) :
    G8ChartCriticalAxis
      (g8OrthodoxShadowAxisSource_to_chart source) z ↔
      BCBalanced (ctx.test.tauNormalForm w) := by
  unfold G8ChartCriticalAxis OnCriticalAxis
  rw [g8OrthodoxTauAxisRelation_axisOffset_eq source z w hRel]
  exact
    primePolarityAxisOffset_eq_zero_iff_bcBalanced
      (ctx.test.tauNormalForm w)

/-- Related off-critical preimages carry tau B/C imbalance. -/
theorem
    g8OrthodoxTauAxisRelation_offCritical_relatedPreimage_bcImbalance
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hz : ClassicalOffCriticalZero ctx.test.base z)
    (hRel : G8OrthodoxTauAxisRelation source z w) :
    TauBCImbalance (ctx.test.tauNormalForm w) := by
  intro hBalanced
  have hOffAxis :
      G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z :=
    g8OrthodoxShadowAxisSource_offCritical_to_chartOffAxis source z hz
  have hAxis :
      G8ChartCriticalAxis
        (g8OrthodoxShadowAxisSource_to_chart source) z :=
    (g8OrthodoxTauAxisRelation_onAxis_iff_bcBalanced
      source z w hRel).mpr hBalanced
  exact
    (g8ChartOffAxis_notCriticalAxis
      (g8OrthodoxShadowAxisSource_to_chart source) hOffAxis)
      hAxis

/-- Related off-critical preimages carry tau critical imbalance. -/
theorem
    g8OrthodoxTauAxisRelation_offCritical_relatedPreimage_tauCritical
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hz : ClassicalOffCriticalZero ctx.test.base z)
    (hRel : G8OrthodoxTauAxisRelation source z w) :
    TauCriticalImbalance (ctx.test.tauNormalForm w) :=
  (tauCriticalImbalance_iff_bcImbalance
    (ctx.test.tauNormalForm w)).mpr
    (g8OrthodoxTauAxisRelation_offCritical_relatedPreimage_bcImbalance
      source z w hz hRel)

-- ============================================================
-- CONCRETE RELATION CONTEXT
-- ============================================================

/-- G8f relation context using the concrete orthodox/tau axis relation.

Preimage existence remains explicit: this context does not prove that every
off-axis shadow has a tau witness.  It only fixes what relation such a witness
must satisfy. -/
structure G8OrthodoxTauAxisRelationContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  source : G8OrthodoxShadowAxisSource ctx
  offAxisHasTauPreimage :
    G8OffAxisTauPreimageExists
      (g8OrthodoxShadowAxisSource_to_chart source)
      (G8OrthodoxTauAxisRelation source)
  tauWitness :
    G8OffAxisTauWitnessRealization
      (g8OrthodoxShadowAxisSource_to_chart source)
  offAxisGuard :
    G8OffAxisChartOnlyGhostGuard
      (g8OrthodoxShadowAxisSource_to_chart source)

/-- The context consumes as the prior orthodox prime-polarity axis pullback
    context. -/
def g8OrthodoxTauAxisRelation_to_pullbackContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (relCtx : G8OrthodoxTauAxisRelationContext ctx) :
    G8OrthodoxPrimePolarityAxisPullbackContext ctx where
  source := relCtx.source
  shadowTauRelated := G8OrthodoxTauAxisRelation relCtx.source
  offAxisHasTauPreimage := relCtx.offAxisHasTauPreimage
  axisOffsetAligned :=
    g8OrthodoxTauAxisRelation_axisOffsetAligned relCtx.source
  tauWitness := relCtx.tauWitness
  offAxisGuard := relCtx.offAxisGuard

/-- The concrete relation context supplies decomposed chart faithfulness. -/
def g8OrthodoxTauAxisRelation_to_decomposition
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (relCtx : G8OrthodoxTauAxisRelationContext ctx) :
    G8OffAxisChartFaithfulnessDecomposition
      (g8OrthodoxShadowAxisSource_to_chart relCtx.source) :=
  g8OrthodoxPrimePolarityAxisPullback_to_decomposition
    (g8OrthodoxTauAxisRelation_to_pullbackContext relCtx)

/-- The concrete relation context yields the local one-sided pullback. -/
theorem g8OrthodoxTauAxisRelation_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (relCtx : G8OrthodoxTauAxisRelationContext ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8OrthodoxPrimePolarityAxisPullback_yields_pullback
    ctx (g8OrthodoxTauAxisRelation_to_pullbackContext relCtx)

/-- The concrete relation context plus tau-side purity yields the local
    no-off-critical-zero conclusion. -/
theorem g8OrthodoxTauAxisRelation_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (relCtx : G8OrthodoxTauAxisRelationContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OrthodoxPrimePolarityAxisPullback_noOffCriticalZeros
    ctx (g8OrthodoxTauAxisRelation_to_pullbackContext relCtx)
    tauPurity

/-- The concrete relation context builds the existing localization audit. -/
def g8OrthodoxTauAxisRelation_to_localizationAudit
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (relCtx : G8OrthodoxTauAxisRelationContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base)
    (stage : Nat) (factor : Nat → Nat)
    (stageAdmissible : ctx.test.base.orthodoxZero → Prop)
    (sameTauTowerSubstrate : ctx.test.base.orthodoxZero → Prop)
    (sameFiniteApproximantSubstrate :
      ctx.test.base.orthodoxZero → Prop)
    (receivingShadowAdmissible :
      ctx.test.base.orthodoxZero → Prop) :
    G8PrimePolarityLocalizationAudit :=
  g8OrthodoxPrimePolarityAxisPullback_to_localizationAudit
    ctx (g8OrthodoxTauAxisRelation_to_pullbackContext relCtx)
    tauPurity stage factor stageAdmissible sameTauTowerSubstrate
    sameFiniteApproximantSubstrate receivingShadowAdmissible

-- ============================================================
-- RELATION MATCHING AGAINST LEGACY ARBITRARY RELATIONS
-- ============================================================

/-- A legacy arbitrary relation matches the concrete axis relation exactly. -/
def G8OrthodoxTauAxisRelationMatches
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (shadowTauRelated :
      G8OffAxisChartRelation
        (g8OrthodoxShadowAxisSource_to_chart source)) : Prop :=
  ∀ (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness),
    shadowTauRelated z w ↔ G8OrthodoxTauAxisRelated source z w

/-- A legacy relation that matches the concrete axis relation is also
    axis-offset aligned. -/
theorem g8OrthodoxTauAxisRelationMatches_axisOffsetAligned
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (shadowTauRelated :
      G8OffAxisChartRelation
        (g8OrthodoxShadowAxisSource_to_chart source))
    (hMatches :
      G8OrthodoxTauAxisRelationMatches source shadowTauRelated) :
    G8PrimePolarityAxisOffsetAlignment
      (g8OrthodoxShadowAxisSource_to_chart source)
      shadowTauRelated := by
  intro z w hRel
  exact (hMatches z w).mp hRel

-- ============================================================
-- FALSIFIERS AND DIAGNOSTICS
-- ============================================================

/-- An orthodox off-critical candidate with no witness satisfying the concrete
    axis relation. -/
structure G8OrthodoxTauAxisNoPreimageWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (relCtx : G8OrthodoxTauAxisRelationContext ctx) where
  z : ctx.test.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  noAxisPreimage :
    ∀ w : ctx.test.base.tauWitness,
      ¬ G8OrthodoxTauAxisRelated relCtx.source z w

/-- No-axis-preimage witnesses refute the concrete relation context. -/
theorem g8OrthodoxTauAxisNoPreimage_refutes_context
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {relCtx : G8OrthodoxTauAxisRelationContext ctx}
    (w : G8OrthodoxTauAxisNoPreimageWitness relCtx) :
    False := by
  have hOffAxis :
      G8ChartOffAxis
        (g8OrthodoxShadowAxisSource_to_chart relCtx.source) w.z :=
    g8OrthodoxShadowAxisSource_offCritical_to_chartOffAxis
      relCtx.source w.z w.offCritical
  obtain ⟨tauW, hRel⟩ :=
    relCtx.offAxisHasTauPreimage w.z hOffAxis
  exact w.noAxisPreimage tauW hRel

/-- A concrete-axis-related off-critical preimage that remains B/C-balanced. -/
structure G8OrthodoxTauAxisBalancedPreimageWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  w : ctx.test.base.tauWitness
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  related : G8OrthodoxTauAxisRelated source z w
  balanced : BCBalanced (ctx.test.tauNormalForm w)

/-- Concrete-axis-related balanced preimages are impossible for off-critical
    candidates. -/
theorem g8OrthodoxTauAxisBalancedPreimage_refutes_relation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8OrthodoxTauAxisBalancedPreimageWitness source) :
    False :=
  (g8OrthodoxTauAxisRelation_offCritical_relatedPreimage_bcImbalance
    source w.z w.w w.offCritical w.related) w.balanced

/-- A mismatch between a legacy arbitrary relation and the concrete axis
    relation. -/
structure G8OrthodoxTauAxisRelationMismatchWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (shadowTauRelated :
      G8OffAxisChartRelation
        (g8OrthodoxShadowAxisSource_to_chart source)) where
  z : ctx.test.base.orthodoxZero
  w : ctx.test.base.tauWitness
  mismatch :
    ¬ (shadowTauRelated z w ↔
        G8OrthodoxTauAxisRelated source z w)

/-- Relation mismatch refutes an exact-match claim for a legacy relation. -/
theorem g8OrthodoxTauAxisRelationMismatch_refutes_match
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    {shadowTauRelated :
      G8OffAxisChartRelation
        (g8OrthodoxShadowAxisSource_to_chart source)}
    (hMatches :
      G8OrthodoxTauAxisRelationMatches source shadowTauRelated)
    (w :
      G8OrthodoxTauAxisRelationMismatchWitness
        source shadowTauRelated) :
    False :=
  w.mismatch (hMatches w.z w.w)

/-- Height/provenance mismatch remains diagnostic as long as the concrete
    axis relation holds. -/
structure G8OrthodoxTauAxisHeightDiagnostic
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  w : ctx.test.base.tauWitness
  related : G8OrthodoxTauAxisRelated source z w
  heightMismatch :
    (source.centeredShadow z).heightWitness ≠
      (primePolarityAxisShadow
        (ctx.test.tauNormalForm w)).heightWitness

/-- Height/provenance mismatch alone is not a localization refutation. -/
theorem g8OrthodoxTauAxisHeightDiagnostic_not_refutation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (_w : G8OrthodoxTauAxisHeightDiagnostic source) :
    True :=
  trivial

end Tau.BookIII.Bridge
