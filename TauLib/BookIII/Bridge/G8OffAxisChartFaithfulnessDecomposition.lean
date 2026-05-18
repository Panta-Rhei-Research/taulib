import TauLib.BookIII.Bridge.G8OffAxisChartAudit

/-!
# TauLib.BookIII.Bridge.G8OffAxisChartFaithfulnessDecomposition

Proof-facing decomposition of the G8 off-axis chart-faithfulness hinge.

The preceding corridor modules package the one-sided route as a clean handoff
object.  This module splits the positive faithfulness hinge into named local
obligations:

* off-critical shadows are readable as off-axis in the centered chart;
* off-axis shadows have tau-related preimages;
* the chart relation preserves B-C imbalance;
* tau imbalance realizes the tau-side witness;
* off-axis chart-only ghosts are excluded.

The module remains an interface and adapter layer.  It does not prove
analytic-completion uniqueness, full zero-divisor transfer, O3, or the
orthodox RH target.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- NAMED DECOMPOSITION PREDICATES
-- ============================================================

/-- Chart readability in the decomposed off-axis corridor. -/
def G8OffAxisChartReadable
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx) : Prop :=
  G8ChartShadowReadable chart

/-- The chart relation between receiving-side shadows and tau-side witnesses. -/
abbrev G8OffAxisChartRelation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (_chart : G8OffAxisChartObject ctx) :=
  ctx.test.base.orthodoxZero → ctx.test.base.tauWitness → Prop

/-- Off-axis chart shadows have tau-related preimages. -/
def G8OffAxisTauPreimageExists
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (shadowTauRelated : G8OffAxisChartRelation chart) : Prop :=
  ∀ z : ctx.test.base.orthodoxZero,
    G8ChartOffAxis chart z →
      ∃ w : ctx.test.base.tauWitness, shadowTauRelated z w

/-- The chart relation preserves B-C imbalance for off-axis shadows. -/
def G8OffAxisRelationPreservesBCImbalance
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (shadowTauRelated : G8OffAxisChartRelation chart) : Prop :=
  ∀ (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness),
    G8ChartOffAxis chart z →
      shadowTauRelated z w →
        TauBCImbalance (ctx.test.tauNormalForm w)

/-- Tau-side imbalance realizes the tau witness used by the weak corridor. -/
def G8OffAxisTauWitnessRealization
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (_chart : G8OffAxisChartObject ctx) : Prop :=
  G8e1TauImbalanceRealizesWitness ctx.test

/-- Off-axis chart-only ghost exclusion in decomposed form. -/
def G8OffAxisChartOnlyGhostGuard
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (_chart : G8OffAxisChartObject ctx) : Prop :=
  NoChartOnlyOffCriticalZerosOutsideAxis ctx.test

-- ============================================================
-- DECOMPOSED FAITHFULNESS PACKAGE
-- ============================================================

/-- Decomposed proof-field package for off-axis chart faithfulness.

This is intentionally equivalent in strength to
`G8OffAxisChartFaithfulnessObject`, but its fields isolate the proof targets
that future geometry work must attack one by one. -/
structure G8OffAxisChartFaithfulnessDecomposition
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx) where
  shadowTauRelated : G8OffAxisChartRelation chart
  chartReadable : G8OffAxisChartReadable chart
  tauPreimageExists :
    G8OffAxisTauPreimageExists chart shadowTauRelated
  relationPreservesBCImbalance :
    G8OffAxisRelationPreservesBCImbalance chart shadowTauRelated
  tauWitness : G8OffAxisTauWitnessRealization chart
  offAxisGuard : G8OffAxisChartOnlyGhostGuard chart

/-- The decomposition rebuilds the existing chart-faithfulness object. -/
def g8OffAxisChartFaithfulnessDecomposition_to_object
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {chart : G8OffAxisChartObject ctx}
    (decomp : G8OffAxisChartFaithfulnessDecomposition chart) :
    G8OffAxisChartFaithfulnessObject chart where
  shadowTauRelated := decomp.shadowTauRelated
  offAxisHasTauPreimage := decomp.tauPreimageExists
  relatedPreimageCarriesBCImbalance :=
    decomp.relationPreservesBCImbalance
  tauWitness := decomp.tauWitness
  offAxisGuard := decomp.offAxisGuard

/-- The decomposition rebuilds the existing core package. -/
def g8OffAxisChartFaithfulnessDecomposition_to_core
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (chart : G8OffAxisChartObject ctx)
    (decomp : G8OffAxisChartFaithfulnessDecomposition chart) :
    G8OffAxisChartFaithfulnessCore ctx :=
  g8OffAxisChartFaithfulnessObject_to_core ctx chart
    (g8OffAxisChartFaithfulnessDecomposition_to_object decomp)

/-- The decomposition plugs into the positive realization ladder. -/
def g8OffAxisChartFaithfulnessDecomposition_to_realization
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (chart : G8OffAxisChartObject ctx)
    (decomp : G8OffAxisChartFaithfulnessDecomposition chart) :
    G8WeakOffAxisPullbackRealizationContext ctx :=
  g8OffAxisChartFaithfulnessObject_to_realization ctx chart
    (g8OffAxisChartFaithfulnessDecomposition_to_object decomp)

/-- The decomposition yields the local one-sided pullback. -/
theorem g8OffAxisChartFaithfulnessDecomposition_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (chart : G8OffAxisChartObject ctx)
    (decomp : G8OffAxisChartFaithfulnessDecomposition chart) :
    G8eOffCriticalPullback ctx.test.base :=
  g8OffAxisChartFaithfulnessObject_yields_pullback ctx chart
    (g8OffAxisChartFaithfulnessDecomposition_to_object decomp)

/-- The decomposition plus tau-side purity yields the local no-off-critical
    zero conclusion. -/
theorem g8OffAxisChartFaithfulnessDecomposition_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (chart : G8OffAxisChartObject ctx)
    (decomp : G8OffAxisChartFaithfulnessDecomposition chart)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OffAxisChartFaithfulnessObject_noOffCriticalZeros ctx chart
    (g8OffAxisChartFaithfulnessDecomposition_to_object decomp)
    tauPurity

-- ============================================================
-- FAILURE WITNESSES FOR INDIVIDUAL OBLIGATIONS
-- ============================================================

/-- A chart-local unreadable off-critical shadow. -/
structure G8DecompositionUnreadableChartShadowWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx) where
  z : ctx.test.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  notReadable : ¬ G8ChartOffAxis chart z

/-- A chart-local unreadable shadow refutes chart readability. -/
theorem g8DecompositionUnreadableChartShadow_refutes_readability
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {chart : G8OffAxisChartObject ctx}
    (w : G8DecompositionUnreadableChartShadowWitness chart) :
    ¬ G8OffAxisChartReadable chart := by
  intro h
  exact w.notReadable (h w.z w.offCritical)

/-- A chart-local unreadable shadow refutes the decomposition. -/
theorem g8DecompositionUnreadableChartShadow_refutes_decomposition
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {chart : G8OffAxisChartObject ctx}
    (w : G8DecompositionUnreadableChartShadowWitness chart) :
    ¬ Nonempty (G8OffAxisChartFaithfulnessDecomposition chart) := by
  intro h
  rcases h with ⟨decomp⟩
  exact g8DecompositionUnreadableChartShadow_refutes_readability
    w decomp.chartReadable

/-- A chart-local off-axis shadow with no tau preimage under the declared
    relation. -/
structure G8DecompositionNoTauPreimageWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (shadowTauRelated : G8OffAxisChartRelation chart) where
  z : ctx.test.base.orthodoxZero
  offAxis : G8ChartOffAxis chart z
  noTauPreimage :
    ∀ w : ctx.test.base.tauWitness, ¬ shadowTauRelated z w

/-- A chart-local no-preimage witness refutes preimage existence. -/
theorem g8DecompositionNoTauPreimage_refutes_preimageExistence
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {chart : G8OffAxisChartObject ctx}
    {shadowTauRelated : G8OffAxisChartRelation chart}
    (w : G8DecompositionNoTauPreimageWitness chart shadowTauRelated) :
    ¬ G8OffAxisTauPreimageExists chart shadowTauRelated := by
  intro h
  obtain ⟨tauW, hRel⟩ := h w.z w.offAxis
  exact w.noTauPreimage tauW hRel

/-- A chart-local no-preimage witness refutes the decomposition. -/
theorem g8DecompositionNoTauPreimage_refutes_decomposition
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {chart : G8OffAxisChartObject ctx}
    (decomp : G8OffAxisChartFaithfulnessDecomposition chart)
    (w :
      G8DecompositionNoTauPreimageWitness chart
        decomp.shadowTauRelated) :
    False :=
  g8DecompositionNoTauPreimage_refutes_preimageExistence
    w decomp.tauPreimageExists

/-- A relation-compatible off-axis tau preimage that remains B-C-balanced. -/
structure G8DecompositionBCBalancedPreimageWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (shadowTauRelated : G8OffAxisChartRelation chart) where
  z : ctx.test.base.orthodoxZero
  w : ctx.test.base.tauWitness
  offAxis : G8ChartOffAxis chart z
  related : shadowTauRelated z w
  balanced : BCBalanced (ctx.test.tauNormalForm w)

/-- A B-C-balanced related preimage refutes B-C imbalance preservation. -/
theorem g8DecompositionBCBalancedPreimage_refutes_bcPreservation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {chart : G8OffAxisChartObject ctx}
    {shadowTauRelated : G8OffAxisChartRelation chart}
    (w :
      G8DecompositionBCBalancedPreimageWitness
        chart shadowTauRelated) :
    ¬ G8OffAxisRelationPreservesBCImbalance
        chart shadowTauRelated := by
  intro h
  have hImbalance := h w.z w.w w.offAxis w.related
  unfold TauBCImbalance at hImbalance
  exact hImbalance w.balanced

/-- A B-C-balanced related preimage refutes the decomposition. -/
theorem g8DecompositionBCBalancedPreimage_refutes_decomposition
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {chart : G8OffAxisChartObject ctx}
    (decomp : G8OffAxisChartFaithfulnessDecomposition chart)
    (w :
      G8DecompositionBCBalancedPreimageWitness chart
        decomp.shadowTauRelated) :
    False :=
  g8DecompositionBCBalancedPreimage_refutes_bcPreservation
    w decomp.relationPreservesBCImbalance

/-- A tau imbalance not realized as a witness refutes the decomposition. -/
theorem g8DecompositionTauImbalanceNotRealized_refutes_decomposition
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {chart : G8OffAxisChartObject ctx}
    (decomp : G8OffAxisChartFaithfulnessDecomposition chart)
    (w : G8TauImbalanceNotRealizedWitness ctx) :
    False :=
  g8TauImbalanceNotRealized_refutes_tauWitnessRealization
    ctx w decomp.tauWitness

/-- An off-axis chart-only ghost refutes the decomposition. -/
theorem g8DecompositionChartOnlyGhost_refutes_decomposition
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {chart : G8OffAxisChartObject ctx}
    (decomp : G8OffAxisChartFaithfulnessDecomposition chart)
    (w : G8OffAxisChartOnlyGhostWitness ctx.test) :
    False :=
  g8OffAxisChartOnlyGhost_refutes_core ctx
    (g8OffAxisChartFaithfulnessDecomposition_to_core ctx chart decomp)
    w

-- ============================================================
-- STAGE-AWARE AND AUDIT HANDOFFS
-- ============================================================

/-- Stage-aware decomposition package. -/
structure G8StageAwareOffAxisChartFaithfulnessDecomposition
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) where
  lab : G8WeakOffAxisCompletionContext stageCorridor
  chart : G8OffAxisChartObject stageCorridor.corridor.weakTest
  decomposition : G8OffAxisChartFaithfulnessDecomposition chart

/-- The stage-aware decomposition rebuilds the explicit chart corridor. -/
def g8StageAwareOffAxisChartFaithfulnessDecomposition_to_corridor
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (decomp :
      G8StageAwareOffAxisChartFaithfulnessDecomposition stageCorridor) :
    G8StageAwareOffAxisChartCorridor stageCorridor where
  lab := decomp.lab
  chart := decomp.chart
  faithfulness :=
    g8OffAxisChartFaithfulnessDecomposition_to_object
      decomp.decomposition

/-- The stage-aware decomposition exposes the local no-off-critical-zero
    conclusion through the existing corridor. -/
theorem g8StageAwareOffAxisChartFaithfulnessDecomposition_noOffCriticalZeros
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (decomp :
      G8StageAwareOffAxisChartFaithfulnessDecomposition stageCorridor) :
    G8eNoOrthodoxOffCriticalZeros
      stageCorridor.corridor.weakTest.test.base :=
  g8StageAwareOffAxisChartCorridor_noOffCriticalZeros
    (g8StageAwareOffAxisChartFaithfulnessDecomposition_to_corridor
      decomp)

/-- A fatal stage-indexed off-axis ghost refutes the stage-aware
    decomposition. -/
theorem g8StageIndexedOffAxisGhost_refutes_decomposition
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (decomp :
      G8StageAwareOffAxisChartFaithfulnessDecomposition stageCorridor)
    (w : G8StageIndexedOffAxisGhostWitness decomp.lab) :
    False :=
  g8StageIndexedOffAxisGhost_refutes_stageAwareCorridor w

/-- The audit can be consumed as a decomposed faithfulness package. -/
def g8OffAxisChartAudit_to_decomposition
    (audit : G8OffAxisChartAudit) :
    G8OffAxisChartFaithfulnessDecomposition audit.corridor.chart where
  shadowTauRelated := audit.corridor.faithfulness.shadowTauRelated
  chartReadable := audit.corridor.chart.shadowReadable
  tauPreimageExists :=
    audit.corridor.faithfulness.offAxisHasTauPreimage
  relationPreservesBCImbalance :=
    audit.corridor.faithfulness.relatedPreimageCarriesBCImbalance
  tauWitness := audit.corridor.faithfulness.tauWitness
  offAxisGuard := audit.corridor.faithfulness.offAxisGuard

/-- The audit can be lifted into the stage-aware decomposition handoff. -/
def g8OffAxisChartAudit_to_stageAwareDecomposition
    (audit : G8OffAxisChartAudit) :
    G8StageAwareOffAxisChartFaithfulnessDecomposition
      audit.stageCorridor where
  lab := audit.corridor.lab
  chart := audit.corridor.chart
  decomposition := g8OffAxisChartAudit_to_decomposition audit

/-- Audit-level selector for the decomposed local pullback. -/
theorem g8OffAxisChartAudit_decomposition_yields_pullback
    (audit : G8OffAxisChartAudit) :
    G8eOffCriticalPullback
      audit.stageCorridor.corridor.weakTest.test.base :=
  g8OffAxisChartFaithfulnessDecomposition_yields_pullback
    audit.stageCorridor.corridor.weakTest
    audit.corridor.chart
    (g8OffAxisChartAudit_to_decomposition audit)

/-- Audit-level selector for the decomposed no-off-critical-zero conclusion. -/
theorem g8OffAxisChartAudit_decomposition_noOffCriticalZeros
    (audit : G8OffAxisChartAudit) :
    G8eNoOrthodoxOffCriticalZeros
      audit.stageCorridor.corridor.weakTest.test.base :=
  g8StageAwareOffAxisChartFaithfulnessDecomposition_noOffCriticalZeros
    (g8OffAxisChartAudit_to_stageAwareDecomposition audit)

/-- Audit-level finite guardrails are unchanged by the decomposition layer. -/
theorem g8OffAxisChartAudit_decomposition_finiteGuardrails
    (audit : G8OffAxisChartAudit) :
    finiteG8bContext.finiteOnly ∧
      finiteG8bContext.noXiDivisorClaim ∧
        finiteG8bContext.noAnalyticCompletionClaim :=
  ⟨
    g8OffAxisChartAudit_finiteOnly audit,
    g8OffAxisChartAudit_noXiDivisorClaim audit,
    g8OffAxisChartAudit_noAnalyticCompletionClaim audit
  ⟩

/-- Audit-level on-axis tolerance is unchanged by the decomposition layer. -/
theorem g8OffAxisChartAudit_decomposition_onAxisTolerated
    (audit : G8OffAxisChartAudit)
    (w : G8StageIndexedOnAxisGhostCandidate audit.corridor.lab) :
    True :=
  g8OffAxisChartAudit_onAxisCandidateTolerated audit w

/-- Audit-level stage-indexed off-axis ghosts still refute the decomposed
    handoff. -/
theorem g8OffAxisChartAudit_decomposition_refutes_stageIndexedOffAxisGhost
    (audit : G8OffAxisChartAudit)
    (w : G8StageIndexedOffAxisGhostWitness audit.corridor.lab) :
    False :=
  g8StageIndexedOffAxisGhost_refutes_decomposition
    (g8OffAxisChartAudit_to_stageAwareDecomposition audit)
    w

end Tau.BookIII.Bridge
