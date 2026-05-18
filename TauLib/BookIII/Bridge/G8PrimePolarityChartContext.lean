import TauLib.BookIII.Bridge.G8OffAxisChartFaithfulnessDecomposition
import TauLib.BookIII.Bridge.G8MasterSwitches

/-!
# TauLib.BookIII.Bridge.G8PrimePolarityChartContext

Prime-polarity chart context for the weak G8 off-axis localization corridor.

The preceding modules made the corridor explicit: an orthodox off-critical
shadow must be readable off-axis, related to tau data, and then reflected as a
B/C imbalance witness.  This module sharpens the source-geometric hinge.

The key local principle is not full zero-divisor equivalence.  It is the
one-sided balance-image law:

* if a related tau preimage remains B/C-balanced, its receiving shadow lies on
  the centered critical axis;
* therefore a related off-axis shadow cannot remain B/C-balanced;
* hence the related tau preimage carries B/C imbalance and feeds the existing
  weak pullback corridor.

Everything here remains local and conditional.  The module does not prove O3,
analytic-completion uniqueness, full divisor transfer, or the classical RH
target.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- PRIME-POLARITY CHART CONTEXT
-- ============================================================

/-- Source-side discipline required by the prime-polarity chart corridor.

This is a compact record of the currently recognized source facts: the
hyperbolic/elliptic chart distinction, ultrametric substrate, and canonical
prime-polarity boundary spectrum.  It is intentionally separated from any
zero-divisor claim. -/
structure G8PrimePolarityChartSource where
  masterSwitches : G8MasterSwitchesRecognized :=
    g8MasterSwitches_recognized
  primePolarity : CanonicalPrimePolarityRecognized :=
    canonicalPrimePolarity_recognized
  notExternalOperatorChoice : True := True.intro

/-- Prime-polarity chart context over the current weak off-axis pullback test.

The decisive field is `balancedPreimageMapsToAxis`: related tau data that is
still B/C-balanced can only appear on the receiving critical axis.  Together
with chart off-axis data, this proves the B/C-imbalance field needed by the
existing decomposition layer. -/
structure G8PrimePolarityChartContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  source : G8PrimePolarityChartSource := {}
  chart : G8OffAxisChartObject ctx
  shadowTauRelated : G8OffAxisChartRelation chart
  offAxisHasTauPreimage :
    G8OffAxisTauPreimageExists chart shadowTauRelated
  balancedPreimageMapsToAxis :
    ∀ (z : ctx.test.base.orthodoxZero)
      (w : ctx.test.base.tauWitness),
      shadowTauRelated z w →
        BCBalanced (ctx.test.tauNormalForm w) →
          G8ChartCriticalAxis chart z
  tauWitness : G8OffAxisTauWitnessRealization chart
  offAxisGuard : G8OffAxisChartOnlyGhostGuard chart

-- ============================================================
-- SOURCE AND CHART SELECTORS
-- ============================================================

/-- The prime-polarity chart context exposes the three master switches. -/
theorem g8PrimePolarityChart_masterSwitches
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chartCtx : G8PrimePolarityChartContext ctx) :
    G8MasterSwitchesRecognized :=
  chartCtx.source.masterSwitches

/-- The prime-polarity chart context exposes canonical prime polarity. -/
theorem g8PrimePolarityChart_primePolarity
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chartCtx : G8PrimePolarityChartContext ctx) :
    CanonicalPrimePolarityRecognized :=
  chartCtx.source.primePolarity

/-- Prime polarity is recorded as source structure, not an external operator
    choice. -/
theorem g8PrimePolarityChart_notExternalOperatorChoice
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chartCtx : G8PrimePolarityChartContext ctx) :
    True :=
  chartCtx.source.notExternalOperatorChoice

/-- The concrete chart object is available to downstream audit layers. -/
def g8PrimePolarityChart_chart
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chartCtx : G8PrimePolarityChartContext ctx) :
    G8OffAxisChartObject ctx :=
  chartCtx.chart

/-- The concrete chart relation is available to downstream audit layers. -/
def g8PrimePolarityChart_relation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chartCtx : G8PrimePolarityChartContext ctx) :
    G8OffAxisChartRelation chartCtx.chart :=
  chartCtx.shadowTauRelated

/-- The chart object supplies chart-shadow readability. -/
theorem g8PrimePolarityChart_readable
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chartCtx : G8PrimePolarityChartContext ctx) :
    G8OffAxisChartReadable chartCtx.chart :=
  chartCtx.chart.shadowReadable

-- ============================================================
-- BALANCE-TO-AXIS AND OFF-AXIS IMBALANCE
-- ============================================================

/-- Related B/C-balanced tau preimages map to the receiving critical axis.

This is the source-geometric image law that replaces a direct assumption of
off-axis B/C imbalance. -/
theorem g8PrimePolarityChart_balancedPreimage_maps_to_axis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chartCtx : G8PrimePolarityChartContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hRel : chartCtx.shadowTauRelated z w)
    (hBalanced : BCBalanced (ctx.test.tauNormalForm w)) :
    G8ChartCriticalAxis chartCtx.chart z :=
  chartCtx.balancedPreimageMapsToAxis z w hRel hBalanced

/-- A related off-axis preimage cannot remain B/C-balanced. -/
theorem g8PrimePolarityChart_offAxis_relatedPreimage_bcImbalance
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chartCtx : G8PrimePolarityChartContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hOffAxis : G8ChartOffAxis chartCtx.chart z)
    (hRel : chartCtx.shadowTauRelated z w) :
    TauBCImbalance (ctx.test.tauNormalForm w) := by
  intro hBalanced
  have hAxis : G8ChartCriticalAxis chartCtx.chart z :=
    chartCtx.balancedPreimageMapsToAxis z w hRel hBalanced
  exact (g8ChartOffAxis_notCriticalAxis chartCtx.chart hOffAxis) hAxis

/-- The prime-polarity chart context supplies the decomposed B/C-imbalance
    preservation field. -/
theorem g8PrimePolarityChart_relationPreservesBCImbalance
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chartCtx : G8PrimePolarityChartContext ctx) :
    G8OffAxisRelationPreservesBCImbalance
      chartCtx.chart chartCtx.shadowTauRelated := by
  intro z w hOffAxis hRel
  exact
    g8PrimePolarityChart_offAxis_relatedPreimage_bcImbalance
      chartCtx z w hOffAxis hRel

-- ============================================================
-- ADAPTERS INTO THE EXISTING CORRIDOR
-- ============================================================

/-- The prime-polarity chart context rebuilds the current faithfulness
    decomposition. -/
def g8PrimePolarityChart_to_decomposition
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chartCtx : G8PrimePolarityChartContext ctx) :
    G8OffAxisChartFaithfulnessDecomposition chartCtx.chart where
  shadowTauRelated := chartCtx.shadowTauRelated
  chartReadable := g8PrimePolarityChart_readable chartCtx
  tauPreimageExists := chartCtx.offAxisHasTauPreimage
  relationPreservesBCImbalance :=
    g8PrimePolarityChart_relationPreservesBCImbalance chartCtx
  tauWitness := chartCtx.tauWitness
  offAxisGuard := chartCtx.offAxisGuard

/-- The prime-polarity chart context plugs into the chart-faithfulness object. -/
def g8PrimePolarityChart_to_faithfulnessObject
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chartCtx : G8PrimePolarityChartContext ctx) :
    G8OffAxisChartFaithfulnessObject chartCtx.chart :=
  g8OffAxisChartFaithfulnessDecomposition_to_object
    (g8PrimePolarityChart_to_decomposition chartCtx)

/-- The prime-polarity chart context plugs into the core faithfulness layer. -/
def g8PrimePolarityChart_to_core
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (chartCtx : G8PrimePolarityChartContext ctx) :
    G8OffAxisChartFaithfulnessCore ctx :=
  g8OffAxisChartFaithfulnessDecomposition_to_core
    ctx chartCtx.chart
    (g8PrimePolarityChart_to_decomposition chartCtx)

/-- The prime-polarity chart context plugs into the positive realization
    ladder. -/
def g8PrimePolarityChart_to_realization
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (chartCtx : G8PrimePolarityChartContext ctx) :
    G8WeakOffAxisPullbackRealizationContext ctx :=
  g8OffAxisChartFaithfulnessDecomposition_to_realization
    ctx chartCtx.chart
    (g8PrimePolarityChart_to_decomposition chartCtx)

/-- The prime-polarity chart context yields the local one-sided pullback. -/
theorem g8PrimePolarityChart_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (chartCtx : G8PrimePolarityChartContext ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8OffAxisChartFaithfulnessDecomposition_yields_pullback
    ctx chartCtx.chart
    (g8PrimePolarityChart_to_decomposition chartCtx)

/-- The prime-polarity chart context plus tau-side purity yields the local
    no-off-critical-zero conclusion. -/
theorem g8PrimePolarityChart_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (chartCtx : G8PrimePolarityChartContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OffAxisChartFaithfulnessDecomposition_noOffCriticalZeros
    ctx chartCtx.chart
    (g8PrimePolarityChart_to_decomposition chartCtx)
    tauPurity

-- ============================================================
-- FAILURE PRESSURE IN PRIME-POLARITY FORM
-- ============================================================

/-- A related off-axis tau preimage that stays B/C-balanced refutes the
    prime-polarity balance-image law. -/
theorem g8PrimePolarityChart_balancedOffAxisPreimage_refutes_context
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chartCtx : G8PrimePolarityChartContext ctx)
    (w :
      G8DecompositionBCBalancedPreimageWitness
        chartCtx.chart chartCtx.shadowTauRelated) :
    False := by
  have hAxis :
      G8ChartCriticalAxis chartCtx.chart w.z :=
    chartCtx.balancedPreimageMapsToAxis
      w.z w.w w.related w.balanced
  exact (g8ChartOffAxis_notCriticalAxis chartCtx.chart w.offAxis) hAxis

/-- A no-preimage witness refutes the prime-polarity chart context. -/
theorem g8PrimePolarityChart_noPreimage_refutes_context
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chartCtx : G8PrimePolarityChartContext ctx)
    (w :
      G8DecompositionNoTauPreimageWitness
        chartCtx.chart chartCtx.shadowTauRelated) :
    False :=
  g8DecompositionNoTauPreimage_refutes_decomposition
    (g8PrimePolarityChart_to_decomposition chartCtx) w

/-- A chart-only ghost refutes the prime-polarity chart context through the
    existing off-axis guard. -/
theorem g8PrimePolarityChart_chartOnlyGhost_refutes_context
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chartCtx : G8PrimePolarityChartContext ctx)
    (w : G8OffAxisChartOnlyGhostWitness ctx.test) :
    False :=
  g8DecompositionChartOnlyGhost_refutes_decomposition
    (g8PrimePolarityChart_to_decomposition chartCtx) w

end Tau.BookIII.Bridge

