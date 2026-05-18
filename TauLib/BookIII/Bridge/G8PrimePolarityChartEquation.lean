import TauLib.BookIII.Bridge.G8PrimePolarityChartContext

/-!
# TauLib.BookIII.Bridge.G8PrimePolarityChartEquation

Equation-level refinement of the prime-polarity chart context.

`G8PrimePolarityChartContext` made the key one-sided image law explicit:
related tau data that remains B/C-balanced maps to the receiving critical
axis.  This module sharpens that field into a proof-facing chart equation:

* for related receiving/tau witnesses, the centered receiving critical axis is
  equivalent to tau B/C balance;
* the previous one-sided balance-image law follows immediately;
* off-axis related preimages therefore carry B/C imbalance.

This is still a local bridge interface.  It does not assert that the orthodox
xi divisor has been classified, does not prove analytic-completion uniqueness,
and does not prove the classical RH target.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- BALANCE / AXIS EQUATION
-- ============================================================

/-- The equation-level chart law: for related tau/receiving witnesses, the
    centered receiving axis is exactly the tau B/C balance locus. -/
def G8PrimePolarityBalanceAxisEquation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (shadowTauRelated : G8OffAxisChartRelation chart) : Prop :=
  ∀ (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness),
    shadowTauRelated z w →
      (G8ChartCriticalAxis chart z ↔
        BCBalanced (ctx.test.tauNormalForm w))

/-- Equation-level prime-polarity chart context.

Compared with `G8PrimePolarityChartContext`, this record carries the stronger
balance/axis equivalence.  It is the more precise target for later chart
construction work. -/
structure G8PrimePolarityChartEquationContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  source : G8PrimePolarityChartSource := {}
  chart : G8OffAxisChartObject ctx
  shadowTauRelated : G8OffAxisChartRelation chart
  offAxisHasTauPreimage :
    G8OffAxisTauPreimageExists chart shadowTauRelated
  balanceAxisEquation :
    G8PrimePolarityBalanceAxisEquation chart shadowTauRelated
  tauWitness : G8OffAxisTauWitnessRealization chart
  offAxisGuard : G8OffAxisChartOnlyGhostGuard chart

-- ============================================================
-- EQUATION SELECTORS
-- ============================================================

/-- The equation context exposes the master-switch source discipline. -/
theorem g8PrimePolarityChartEquation_masterSwitches
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (eqCtx : G8PrimePolarityChartEquationContext ctx) :
    G8MasterSwitchesRecognized :=
  eqCtx.source.masterSwitches

/-- The equation context exposes canonical prime polarity. -/
theorem g8PrimePolarityChartEquation_primePolarity
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (eqCtx : G8PrimePolarityChartEquationContext ctx) :
    CanonicalPrimePolarityRecognized :=
  eqCtx.source.primePolarity

/-- Related axis data is equivalent to related tau B/C balance. -/
theorem g8PrimePolarityChartEquation_axis_iff_balance
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (eqCtx : G8PrimePolarityChartEquationContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hRel : eqCtx.shadowTauRelated z w) :
    G8ChartCriticalAxis eqCtx.chart z ↔
      BCBalanced (ctx.test.tauNormalForm w) :=
  eqCtx.balanceAxisEquation z w hRel

/-- Related B/C-balanced tau data maps to the receiving critical axis. -/
theorem g8PrimePolarityChartEquation_balance_maps_to_axis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (eqCtx : G8PrimePolarityChartEquationContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hRel : eqCtx.shadowTauRelated z w)
    (hBalanced : BCBalanced (ctx.test.tauNormalForm w)) :
    G8ChartCriticalAxis eqCtx.chart z :=
  (g8PrimePolarityChartEquation_axis_iff_balance
    eqCtx z w hRel).mpr hBalanced

/-- Related on-axis receiving data maps back to tau B/C balance. -/
theorem g8PrimePolarityChartEquation_axis_maps_to_balance
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (eqCtx : G8PrimePolarityChartEquationContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hRel : eqCtx.shadowTauRelated z w)
    (hAxis : G8ChartCriticalAxis eqCtx.chart z) :
    BCBalanced (ctx.test.tauNormalForm w) :=
  (g8PrimePolarityChartEquation_axis_iff_balance
    eqCtx z w hRel).mp hAxis

/-- A related off-axis receiving shadow cannot have a B/C-balanced tau
    preimage. -/
theorem g8PrimePolarityChartEquation_offAxis_relatedPreimage_bcImbalance
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (eqCtx : G8PrimePolarityChartEquationContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hOffAxis : G8ChartOffAxis eqCtx.chart z)
    (hRel : eqCtx.shadowTauRelated z w) :
    TauBCImbalance (ctx.test.tauNormalForm w) := by
  intro hBalanced
  have hAxis : G8ChartCriticalAxis eqCtx.chart z :=
    g8PrimePolarityChartEquation_balance_maps_to_axis
      eqCtx z w hRel hBalanced
  exact (g8ChartOffAxis_notCriticalAxis eqCtx.chart hOffAxis) hAxis

/-- The equation context supplies the B/C-imbalance preservation field needed
    by the decomposed corridor. -/
theorem g8PrimePolarityChartEquation_relationPreservesBCImbalance
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (eqCtx : G8PrimePolarityChartEquationContext ctx) :
    G8OffAxisRelationPreservesBCImbalance
      eqCtx.chart eqCtx.shadowTauRelated := by
  intro z w hOffAxis hRel
  exact
    g8PrimePolarityChartEquation_offAxis_relatedPreimage_bcImbalance
      eqCtx z w hOffAxis hRel

-- ============================================================
-- ADAPTERS INTO THE PRIME-POLARITY CONTEXT
-- ============================================================

/-- The equation-level context rebuilds the one-sided prime-polarity chart
    context. -/
def g8PrimePolarityChartEquation_to_context
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (eqCtx : G8PrimePolarityChartEquationContext ctx) :
    G8PrimePolarityChartContext ctx where
  source := eqCtx.source
  chart := eqCtx.chart
  shadowTauRelated := eqCtx.shadowTauRelated
  offAxisHasTauPreimage := eqCtx.offAxisHasTauPreimage
  balancedPreimageMapsToAxis :=
    g8PrimePolarityChartEquation_balance_maps_to_axis eqCtx
  tauWitness := eqCtx.tauWitness
  offAxisGuard := eqCtx.offAxisGuard

/-- The equation-level context rebuilds the decomposed chart-faithfulness
    package. -/
def g8PrimePolarityChartEquation_to_decomposition
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (eqCtx : G8PrimePolarityChartEquationContext ctx) :
    G8OffAxisChartFaithfulnessDecomposition eqCtx.chart :=
  g8PrimePolarityChart_to_decomposition
    (g8PrimePolarityChartEquation_to_context eqCtx)

/-- The equation-level context plugs into the positive realization ladder. -/
def g8PrimePolarityChartEquation_to_realization
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (eqCtx : G8PrimePolarityChartEquationContext ctx) :
    G8WeakOffAxisPullbackRealizationContext ctx :=
  g8PrimePolarityChart_to_realization ctx
    (g8PrimePolarityChartEquation_to_context eqCtx)

/-- The equation-level context yields the local one-sided pullback. -/
theorem g8PrimePolarityChartEquation_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (eqCtx : G8PrimePolarityChartEquationContext ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8PrimePolarityChart_yields_pullback ctx
    (g8PrimePolarityChartEquation_to_context eqCtx)

/-- The equation-level context plus tau-side purity yields the local
    no-off-critical-zero conclusion. -/
theorem g8PrimePolarityChartEquation_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (eqCtx : G8PrimePolarityChartEquationContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8PrimePolarityChart_noOffCriticalZeros ctx
    (g8PrimePolarityChartEquation_to_context eqCtx)
    tauPurity

-- ============================================================
-- EQUATION-LEVEL FAILURE PRESSURE
-- ============================================================

/-- A related axis witness that is not B/C-balanced refutes the equation. -/
structure G8PrimePolarityAxisButUnbalancedWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (shadowTauRelated : G8OffAxisChartRelation chart) where
  z : ctx.test.base.orthodoxZero
  w : ctx.test.base.tauWitness
  related : shadowTauRelated z w
  axis : G8ChartCriticalAxis chart z
  unbalanced : TauBCImbalance (ctx.test.tauNormalForm w)

/-- A related B/C-balanced witness that is off-axis refutes the equation. -/
structure G8PrimePolarityBalancedButOffAxisWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (shadowTauRelated : G8OffAxisChartRelation chart) where
  z : ctx.test.base.orthodoxZero
  w : ctx.test.base.tauWitness
  related : shadowTauRelated z w
  balanced : BCBalanced (ctx.test.tauNormalForm w)
  offAxis : G8ChartOffAxis chart z

/-- Axis-but-unbalanced witnesses refute the balance/axis equation. -/
theorem g8PrimePolarityAxisButUnbalanced_refutes_equation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {chart : G8OffAxisChartObject ctx}
    {shadowTauRelated : G8OffAxisChartRelation chart}
    (eqn : G8PrimePolarityBalanceAxisEquation chart shadowTauRelated)
    (w :
      G8PrimePolarityAxisButUnbalancedWitness
        chart shadowTauRelated) :
    False := by
  have hBalanced : BCBalanced (ctx.test.tauNormalForm w.w) :=
    (eqn w.z w.w w.related).mp w.axis
  exact w.unbalanced hBalanced

/-- Balanced-but-off-axis witnesses refute the balance/axis equation. -/
theorem g8PrimePolarityBalancedButOffAxis_refutes_equation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {chart : G8OffAxisChartObject ctx}
    {shadowTauRelated : G8OffAxisChartRelation chart}
    (eqn : G8PrimePolarityBalanceAxisEquation chart shadowTauRelated)
    (w :
      G8PrimePolarityBalancedButOffAxisWitness
        chart shadowTauRelated) :
    False := by
  have hAxis : G8ChartCriticalAxis chart w.z :=
    (eqn w.z w.w w.related).mpr w.balanced
  exact (g8ChartOffAxis_notCriticalAxis chart w.offAxis) hAxis

/-- Axis-but-unbalanced witnesses refute the equation-level context. -/
theorem g8PrimePolarityChartEquation_axisButUnbalanced_refutes_context
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (eqCtx : G8PrimePolarityChartEquationContext ctx)
    (w :
      G8PrimePolarityAxisButUnbalancedWitness
        eqCtx.chart eqCtx.shadowTauRelated) :
    False :=
  g8PrimePolarityAxisButUnbalanced_refutes_equation
    eqCtx.balanceAxisEquation w

/-- Balanced-but-off-axis witnesses refute the equation-level context. -/
theorem g8PrimePolarityChartEquation_balancedButOffAxis_refutes_context
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (eqCtx : G8PrimePolarityChartEquationContext ctx)
    (w :
      G8PrimePolarityBalancedButOffAxisWitness
        eqCtx.chart eqCtx.shadowTauRelated) :
    False :=
  g8PrimePolarityBalancedButOffAxis_refutes_equation
    eqCtx.balanceAxisEquation w

end Tau.BookIII.Bridge

