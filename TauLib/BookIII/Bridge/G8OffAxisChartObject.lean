import TauLib.BookIII.Bridge.G8OffAxisChartFaithfulnessCore

/-!
# TauLib.BookIII.Bridge.G8OffAxisChartObject

Explicit off-axis chart object for the weak G8 pullback corridor.

The preceding corridor already had the right conditional shape, but the
receiving-side chart lived mostly as fields on the test context.  This module
names the chart object itself:

* a centered receiving coordinate;
* the critical-axis and off-axis predicates;
* chart-shadow readability for orthodox off-critical candidates;
* an explicit off-axis chart-faithfulness proof-field package;
* the relation-level falsifier aligned with the weak completion lab.

Everything remains local and conditional.  No divisor equivalence, analytic
completion uniqueness, O3, or classical RH statement is proved here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- OFF-AXIS CHART OBJECT
-- ============================================================

/-- Local receiving-side chart object for the weak off-axis corridor.

`centeredShadow` is the explicit centered coordinate chart.  The agreement
field ties it back to the current test context, while `shadowReadable` is the
local fold-readability obligation in object form. -/
structure G8OffAxisChartObject
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  centeredShadow : ctx.test.base.orthodoxZero → CriticalAxisShadow
  shadowAgrees :
    ∀ z : ctx.test.base.orthodoxZero,
      centeredShadow z = ctx.test.orthodoxShadow z
  shadowReadable :
    ∀ z : ctx.test.base.orthodoxZero,
      ClassicalOffCriticalZero ctx.test.base z →
        ShadowOffAxis (centeredShadow z)

/-- The critical-axis zone of a local chart object. -/
def G8ChartCriticalAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (z : ctx.test.base.orthodoxZero) : Prop :=
  OnCriticalAxis (chart.centeredShadow z)

/-- The off-axis zone of a local chart object. -/
def G8ChartOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (z : ctx.test.base.orthodoxZero) : Prop :=
  ShadowOffAxis (chart.centeredShadow z)

/-- Chart-shadow readability in object form. -/
def G8ChartShadowReadable
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx) : Prop :=
  ∀ z : ctx.test.base.orthodoxZero,
    ClassicalOffCriticalZero ctx.test.base z →
      G8ChartOffAxis chart z

/-- The chart object exposes local fold readability for the existing weak
    test context. -/
theorem g8OffAxisChartObject_localFold
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (chart : G8OffAxisChartObject ctx) :
    G8e1LocalFoldReadable ctx.test := by
  intro z hz
  have hChart : ShadowOffAxis (chart.centeredShadow z) :=
    chart.shadowReadable z hz
  unfold ShadowOffAxis at hChart ⊢
  intro hAxis
  exact hChart ((chart.shadowAgrees z) ▸ hAxis)

/-- Off-axis in the explicit chart object is the same as off-axis in the test
    context shadow. -/
theorem g8ChartOffAxis_iff_contextOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (z : ctx.test.base.orthodoxZero) :
    G8ChartOffAxis chart z ↔
      ShadowOffAxis (ctx.test.orthodoxShadow z) := by
  unfold G8ChartOffAxis ShadowOffAxis
  rw [chart.shadowAgrees z]

/-- Context off-axis data transports into the explicit chart object. -/
theorem g8ChartOffAxis_from_context
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    {z : ctx.test.base.orthodoxZero}
    (h : ShadowOffAxis (ctx.test.orthodoxShadow z)) :
    G8ChartOffAxis chart z :=
  (g8ChartOffAxis_iff_contextOffAxis chart z).mpr h

/-- Explicit chart off-axis data transports back to the test context. -/
theorem g8ChartOffAxis_to_context
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    {z : ctx.test.base.orthodoxZero}
    (h : G8ChartOffAxis chart z) :
    ShadowOffAxis (ctx.test.orthodoxShadow z) :=
  (g8ChartOffAxis_iff_contextOffAxis chart z).mp h

-- ============================================================
-- AXIS / OFF-AXIS SEPARATION
-- ============================================================

/-- Anything marked off-axis by the chart object is algebraically outside the
    chart object's critical-axis zone.  This is local shadow algebra only and
    contains no divisor claim. -/
theorem g8ChartOffAxis_notCriticalAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    {z : ctx.test.base.orthodoxZero}
    (h : G8ChartOffAxis chart z) :
    ¬ G8ChartCriticalAxis chart z := by
  exact h

/-- A context-level on-axis shadow cannot coexist with chart-object off-axis
    data for the same point. -/
theorem g8ChartOffAxis_refutes_contextOnAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    {z : ctx.test.base.orthodoxZero}
    (h : G8ChartOffAxis chart z) :
    ¬ OnCriticalAxis (ctx.test.orthodoxShadow z) := by
  exact g8ChartOffAxis_to_context chart h

/-- Stage-indexed on-axis ghost candidates are outside the chart object's
    off-axis route for the same receiving point.  This is the formal split
    between tolerated on-axis bookkeeping and fatal off-axis ghosts. -/
theorem g8ChartOffAxis_refutes_stageIndexedOnAxisCandidate
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    {lab : G8WeakOffAxisCompletionContext stageCorridor}
    (chart : G8OffAxisChartObject stageCorridor.corridor.weakTest)
    (w : G8StageIndexedOnAxisGhostCandidate lab)
    (h : G8ChartOffAxis chart w.z) :
    False :=
  (g8ChartOffAxis_refutes_contextOnAxis chart h) w.onAxis

-- ============================================================
-- CHART FAITHFULNESS PREDICATE
-- ============================================================

/-- Core chart-faithfulness predicate against an explicit chart object.

It says: once an orthodox shadow is readable as off-axis in the centered chart,
the declared chart relation supplies a tau preimage and that relation preserves
enough structure to leave the tau B-C balance locus. -/
structure G8OffAxisChartFaithfulnessObject
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx) where
  shadowTauRelated :
    ctx.test.base.orthodoxZero → ctx.test.base.tauWitness → Prop
  offAxisHasTauPreimage :
    ∀ z : ctx.test.base.orthodoxZero,
      G8ChartOffAxis chart z →
        ∃ w : ctx.test.base.tauWitness, shadowTauRelated z w
  relatedPreimageCarriesBCImbalance :
    ∀ (z : ctx.test.base.orthodoxZero)
      (w : ctx.test.base.tauWitness),
      G8ChartOffAxis chart z →
        shadowTauRelated z w →
          TauBCImbalance (ctx.test.tauNormalForm w)
  tauWitness : G8e1TauImbalanceRealizesWitness ctx.test
  offAxisGuard : NoChartOnlyOffCriticalZerosOutsideAxis ctx.test

/-- The explicit chart-faithfulness object yields the existing core package. -/
def g8OffAxisChartFaithfulnessObject_to_core
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (chart : G8OffAxisChartObject ctx)
    (faith : G8OffAxisChartFaithfulnessObject chart) :
    G8OffAxisChartFaithfulnessCore ctx where
  shadowTauRelated := faith.shadowTauRelated
  localFold := g8OffAxisChartObject_localFold ctx chart
  offAxisHasTauPreimage := by
    intro z hOffAxis
    exact faith.offAxisHasTauPreimage z
      (g8ChartOffAxis_from_context chart hOffAxis)
  relatedPreimageCarriesBCImbalance := by
    intro z w hOffAxis hRel
    exact faith.relatedPreimageCarriesBCImbalance z w
      (g8ChartOffAxis_from_context chart hOffAxis) hRel
  tauWitness := faith.tauWitness
  offAxisGuard := faith.offAxisGuard

/-- The explicit chart-faithfulness object plugs into the positive realization
    ladder. -/
def g8OffAxisChartFaithfulnessObject_to_realization
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (chart : G8OffAxisChartObject ctx)
    (faith : G8OffAxisChartFaithfulnessObject chart) :
    G8WeakOffAxisPullbackRealizationContext ctx :=
  g8OffAxisChartFaithfulnessCore_to_realization ctx
    (g8OffAxisChartFaithfulnessObject_to_core ctx chart faith)

/-- Explicit chart faithfulness yields the local one-sided pullback. -/
theorem g8OffAxisChartFaithfulnessObject_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (chart : G8OffAxisChartObject ctx)
    (faith : G8OffAxisChartFaithfulnessObject chart) :
    G8eOffCriticalPullback ctx.test.base :=
  g8OffAxisChartFaithfulnessCore_yields_pullback ctx
    (g8OffAxisChartFaithfulnessObject_to_core ctx chart faith)

/-- Explicit chart faithfulness plus tau-side purity yields the local
    no-off-critical-zero conclusion. -/
theorem g8OffAxisChartFaithfulnessObject_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (chart : G8OffAxisChartObject ctx)
    (faith : G8OffAxisChartFaithfulnessObject chart)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OffAxisChartFaithfulnessCore_noOffCriticalZeros ctx
    (g8OffAxisChartFaithfulnessObject_to_core ctx chart faith)
    tauPurity

-- ============================================================
-- STAGE-AWARE CORRIDOR HANDOFF
-- ============================================================

/-- Stage-aware handoff object: finite/tower substrate plus explicit off-axis
    chart object plus chart-faithfulness proof fields. -/
structure G8StageAwareOffAxisChartCorridor
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) where
  lab : G8WeakOffAxisCompletionContext stageCorridor
  chart : G8OffAxisChartObject stageCorridor.corridor.weakTest
  faithfulness : G8OffAxisChartFaithfulnessObject chart

/-- Convert the explicit chart corridor to the earlier stage-aware core
    package. -/
def g8StageAwareOffAxisChartCorridor_to_core
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (corridor : G8StageAwareOffAxisChartCorridor stageCorridor) :
    G8StageAwareOffAxisChartFaithfulnessCore stageCorridor where
  lab := corridor.lab
  core :=
    g8OffAxisChartFaithfulnessObject_to_core
      stageCorridor.corridor.weakTest
      corridor.chart
      corridor.faithfulness

/-- The explicit chart corridor exposes the finite stage support. -/
def g8StageAwareOffAxisChartCorridor_stageSupport
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (corridor : G8StageAwareOffAxisChartCorridor stageCorridor) :
    G8PullbackStageSupport :=
  g8StageAwareOffAxisChartFaithfulnessCore_stageSupport
    (g8StageAwareOffAxisChartCorridor_to_core corridor)

/-- The explicit chart corridor keeps finite stages finite-only. -/
theorem g8StageAwareOffAxisChartCorridor_finiteOnly
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (corridor : G8StageAwareOffAxisChartCorridor stageCorridor) :
    finiteG8bContext.finiteOnly :=
  g8StageAwareOffAxisChartFaithfulnessCore_finiteOnly
    (g8StageAwareOffAxisChartCorridor_to_core corridor)

/-- The explicit chart corridor carries no xi-divisor claim from finite
    stages. -/
theorem g8StageAwareOffAxisChartCorridor_noXiDivisorClaim
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (corridor : G8StageAwareOffAxisChartCorridor stageCorridor) :
    finiteG8bContext.noXiDivisorClaim :=
  g8StageAwareOffAxisChartFaithfulnessCore_noXiDivisorClaim
    (g8StageAwareOffAxisChartCorridor_to_core corridor)

/-- The explicit chart corridor carries no analytic-completion claim from
    finite stages. -/
theorem g8StageAwareOffAxisChartCorridor_noAnalyticCompletionClaim
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (corridor : G8StageAwareOffAxisChartCorridor stageCorridor) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8StageAwareOffAxisChartFaithfulnessCore_noAnalyticCompletionClaim
    (g8StageAwareOffAxisChartCorridor_to_core corridor)

/-- The explicit chart corridor exposes the local no-off-critical-zero
    conclusion already guarded by the stage corridor's tau purity. -/
theorem g8StageAwareOffAxisChartCorridor_noOffCriticalZeros
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (corridor : G8StageAwareOffAxisChartCorridor stageCorridor) :
    G8eNoOrthodoxOffCriticalZeros
      stageCorridor.corridor.weakTest.test.base :=
  g8StageAwareOffAxisChartFaithfulnessCore_noOffCriticalZeros
    (g8StageAwareOffAxisChartCorridor_to_core corridor)

-- ============================================================
-- RED-TEAM FALSIFIER ALIGNMENT
-- ============================================================

/-- Relation-level fatal witness against the explicit chart-faithfulness
    corridor.

This is the sharpened negative test: same finite/tower substrate, an off-axis
receiving shadow, and no related tau preimage carrying B-C imbalance. -/
structure G8StageIndexedOffAxisChartFaithfulnessFailure
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (corridor : G8StageAwareOffAxisChartCorridor stageCorridor) where
  z : stageCorridor.corridor.weakTest.test.base.orthodoxZero
  stageAdmissible : G8WeakOffAxisStageAdmissible corridor.lab z
  sameTauTower : G8WeakOffAxisSameTauTowerSubstrate corridor.lab z
  sameFinite : G8WeakOffAxisSameFiniteSubstrate corridor.lab z
  shadowAdmissible : G8WeakOffAxisReceivingShadowAdmissible corridor.lab z
  offCritical :
    ClassicalOffCriticalZero
      stageCorridor.corridor.weakTest.test.base z
  offAxis :
    ShadowOffAxis
      (stageCorridor.corridor.weakTest.test.orthodoxShadow z)
  noRelatedTauImbalancePreimage :
    ∀ w : stageCorridor.corridor.weakTest.test.base.tauWitness,
      ¬ (corridor.faithfulness.shadowTauRelated z w ∧
        TauBCImbalance
          (stageCorridor.corridor.weakTest.test.tauNormalForm w))

/-- A relation-level fatal witness directly refutes explicit chart
    faithfulness. -/
theorem g8StageIndexedChartFaithfulnessFailure_refutes_corridor
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    {corridor : G8StageAwareOffAxisChartCorridor stageCorridor}
    (w : G8StageIndexedOffAxisChartFaithfulnessFailure corridor) :
    False := by
  have hChartOffAxis :
      G8ChartOffAxis corridor.chart w.z :=
    g8ChartOffAxis_from_context corridor.chart w.offAxis
  obtain ⟨tauW, hRel⟩ :=
    corridor.faithfulness.offAxisHasTauPreimage w.z hChartOffAxis
  have hBC :
      TauBCImbalance
        (stageCorridor.corridor.weakTest.test.tauNormalForm tauW) :=
    corridor.faithfulness.relatedPreimageCarriesBCImbalance
      w.z tauW hChartOffAxis hRel
  exact w.noRelatedTauImbalancePreimage tauW ⟨hRel, hBC⟩

/-- The weak completion lab's fatal off-axis ghost is a relation-level
    chart-faithfulness failure for the explicit corridor. -/
def g8StageIndexedOffAxisGhost_to_chartFaithfulnessFailure
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    {corridor : G8StageAwareOffAxisChartCorridor stageCorridor}
    (w : G8StageIndexedOffAxisGhostWitness corridor.lab) :
    G8StageIndexedOffAxisChartFaithfulnessFailure corridor where
  z := w.z
  stageAdmissible := w.stageAdmissible
  sameTauTower := w.sameTauTower
  sameFinite := w.sameFinite
  shadowAdmissible := w.shadowAdmissible
  offCritical := w.offCritical
  offAxis := w.offAxis
  noRelatedTauImbalancePreimage := by
    intro tauW hRelAndImbalance
    have hTauCritical :
        TauCriticalImbalance
          (stageCorridor.corridor.weakTest.test.tauNormalForm tauW) :=
      (tauCriticalImbalance_iff_bcImbalance
        (stageCorridor.corridor.weakTest.test.tauNormalForm tauW)).mpr
        hRelAndImbalance.right
    exact w.noTauImbalancePreimage tauW
      (corridor.faithfulness.tauWitness tauW hTauCritical)

/-- The weak completion lab's fatal witness refutes the explicit chart
    corridor through the sharper relation-level failure shape. -/
theorem g8StageIndexedOffAxisGhost_refutes_chartCorridor
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    {corridor : G8StageAwareOffAxisChartCorridor stageCorridor}
    (w : G8StageIndexedOffAxisGhostWitness corridor.lab) :
    False :=
  g8StageIndexedChartFaithfulnessFailure_refutes_corridor
    (g8StageIndexedOffAxisGhost_to_chartFaithfulnessFailure w)

end Tau.BookIII.Bridge
