import TauLib.BookIII.Bridge.G8PrimePolarityChartEquation
import TauLib.BookIII.Bridge.G8OffAxisChartAudit

/-!
# TauLib.BookIII.Bridge.G8PrimePolarityLocalizationAudit

Stage-aware audit handoff for the prime-polarity localization corridor.

`G8PrimePolarityChartEquation` sharpened the source-geometric hinge into an
equation: for related tau/receiving witnesses, receiving critical-axis
membership is equivalent to tau B/C balance.  This module packages that
equation into the existing stage-aware off-axis chart-audit corridor.

The point is proof plumbing, not claim closure:

* the equation context yields the weak guarded pullback obligations;
* tau-side purity yields the local no-off-critical-zero conclusion;
* G8a/G8b finite support remains substrate only;
* off-axis ghost and chart-faithfulness falsifiers remain visible.

No analytic-completion uniqueness, full xi-divisor transfer, O3 theorem, or
classical RH theorem is proved here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- EQUATION CONTEXT TO OFF-AXIS CORRIDOR
-- ============================================================

/-- The prime-polarity chart equation supplies the guarded weak subobligation
    package consumed by the off-axis corridor. -/
def g8PrimePolarityChartEquation_guardedObligations
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (eqCtx : G8PrimePolarityChartEquationContext ctx) :
    G8OffAxisGuardedWeakSubobligations ctx :=
  g8WeakOffAxisRealization_guardedSubobligations
    ctx
    (g8PrimePolarityChartEquation_to_realization ctx eqCtx)

/-- The prime-polarity chart equation plus tau-side purity builds the weak
    off-axis exclusion corridor. -/
def g8PrimePolarityChartEquation_to_corridor
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (eqCtx : G8PrimePolarityChartEquationContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8OffAxisGhostExclusionCorridor where
  weakTest := ctx
  obligations :=
    g8PrimePolarityChartEquation_guardedObligations ctx eqCtx
  tauPurity := tauPurity

/-- Attach a finite stage/factor family to the prime-polarity corridor. -/
def g8PrimePolarityChartEquation_to_stageCorridor
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (eqCtx : G8PrimePolarityChartEquationContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base)
    (stage : Nat) (factor : Nat → Nat) :
    G8StageAwareOffAxisGhostExclusionCorridor :=
  g8StageAwareOffAxisGhostExclusionCorridor
    (g8PrimePolarityChartEquation_to_corridor ctx eqCtx tauPurity)
    stage factor

-- ============================================================
-- PRIME-POLARITY LOCALIZATION AUDIT
-- ============================================================

/-- Stage-aware prime-polarity localization audit.

The record carries the equation-level chart context, tau-side purity, and a
finite-stage lab.  The finite lab is intentionally just the G8a/G8b substrate:
it does not provide xi-divisor transfer or analytic-completion uniqueness. -/
structure G8PrimePolarityLocalizationAudit where
  ctx : G8WeakOffCriticalPullbackTestContext
  eqCtx : G8PrimePolarityChartEquationContext ctx
  tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base
  stage : Nat
  factor : Nat → Nat
  stageAdmissible : ctx.test.base.orthodoxZero → Prop
  sameTauTowerSubstrate : ctx.test.base.orthodoxZero → Prop
  sameFiniteApproximantSubstrate : ctx.test.base.orthodoxZero → Prop
  receivingShadowAdmissible : ctx.test.base.orthodoxZero → Prop

/-- The stage-aware corridor induced by the audit. -/
def g8PrimePolarityLocalizationAudit_stageCorridor
    (audit : G8PrimePolarityLocalizationAudit) :
    G8StageAwareOffAxisGhostExclusionCorridor :=
  g8PrimePolarityChartEquation_to_stageCorridor
    audit.ctx audit.eqCtx audit.tauPurity audit.stage audit.factor

/-- The weak completion lab induced by the audit's finite-stage predicates. -/
def g8PrimePolarityLocalizationAudit_lab
    (audit : G8PrimePolarityLocalizationAudit) :
    G8WeakOffAxisCompletionContext
      (g8PrimePolarityLocalizationAudit_stageCorridor audit) where
  stageAdmissible := audit.stageAdmissible
  sameTauTowerSubstrate := audit.sameTauTowerSubstrate
  sameFiniteApproximantSubstrate := audit.sameFiniteApproximantSubstrate
  receivingShadowAdmissible := audit.receivingShadowAdmissible

/-- The explicit chart corridor induced by the prime-polarity equation. -/
def g8PrimePolarityLocalizationAudit_chartCorridor
    (audit : G8PrimePolarityLocalizationAudit) :
    G8StageAwareOffAxisChartCorridor
      (g8PrimePolarityLocalizationAudit_stageCorridor audit) where
  lab := g8PrimePolarityLocalizationAudit_lab audit
  chart := audit.eqCtx.chart
  faithfulness :=
    g8OffAxisChartFaithfulnessDecomposition_to_object
      (g8PrimePolarityChartEquation_to_decomposition audit.eqCtx)

/-- Convert the prime-polarity localization audit into the generic off-axis
    chart-audit handoff. -/
def g8PrimePolarityLocalizationAudit_to_chartAudit
    (audit : G8PrimePolarityLocalizationAudit) :
    G8OffAxisChartAudit where
  stageCorridor := g8PrimePolarityLocalizationAudit_stageCorridor audit
  corridor := g8PrimePolarityLocalizationAudit_chartCorridor audit

-- ============================================================
-- PRIME-POLARITY EQUATION SELECTORS
-- ============================================================

/-- The audit exposes the master-switch source discipline. -/
theorem g8PrimePolarityLocalizationAudit_masterSwitches
    (audit : G8PrimePolarityLocalizationAudit) :
    G8MasterSwitchesRecognized :=
  g8PrimePolarityChartEquation_masterSwitches audit.eqCtx

/-- The audit exposes canonical prime polarity. -/
theorem g8PrimePolarityLocalizationAudit_primePolarity
    (audit : G8PrimePolarityLocalizationAudit) :
    CanonicalPrimePolarityRecognized :=
  g8PrimePolarityChartEquation_primePolarity audit.eqCtx

/-- The audit exposes the axis iff B/C-balance law for related witnesses. -/
theorem g8PrimePolarityLocalizationAudit_axis_iff_balance
    (audit : G8PrimePolarityLocalizationAudit)
    (z : audit.ctx.test.base.orthodoxZero)
    (w : audit.ctx.test.base.tauWitness)
    (hRel : audit.eqCtx.shadowTauRelated z w) :
    G8ChartCriticalAxis audit.eqCtx.chart z ↔
      BCBalanced (audit.ctx.test.tauNormalForm w) :=
  g8PrimePolarityChartEquation_axis_iff_balance
    audit.eqCtx z w hRel

/-- A related off-axis preimage carries tau B/C imbalance. -/
theorem g8PrimePolarityLocalizationAudit_offAxis_relatedPreimage_bcImbalance
    (audit : G8PrimePolarityLocalizationAudit)
    (z : audit.ctx.test.base.orthodoxZero)
    (w : audit.ctx.test.base.tauWitness)
    (hOffAxis : G8ChartOffAxis audit.eqCtx.chart z)
    (hRel : audit.eqCtx.shadowTauRelated z w) :
    TauBCImbalance (audit.ctx.test.tauNormalForm w) :=
  g8PrimePolarityChartEquation_offAxis_relatedPreimage_bcImbalance
    audit.eqCtx z w hOffAxis hRel

/-- The audit exposes the local one-sided pullback. -/
theorem g8PrimePolarityLocalizationAudit_yields_pullback
    (audit : G8PrimePolarityLocalizationAudit) :
    G8eOffCriticalPullback audit.ctx.test.base :=
  g8PrimePolarityChartEquation_yields_pullback audit.ctx audit.eqCtx

/-- The audit yields the local no-off-critical-zero conclusion, conditional
    on its tau-side purity field. -/
theorem g8PrimePolarityLocalizationAudit_noOffCriticalZeros
    (audit : G8PrimePolarityLocalizationAudit) :
    G8eNoOrthodoxOffCriticalZeros audit.ctx.test.base :=
  g8OffAxisChartAudit_noOffCriticalZeros
    (g8PrimePolarityLocalizationAudit_to_chartAudit audit)

-- ============================================================
-- FINITE-STAGE GUARDRAIL SELECTORS
-- ============================================================

/-- The audit exposes its finite stage support. -/
def g8PrimePolarityLocalizationAudit_stageSupport
    (audit : G8PrimePolarityLocalizationAudit) :
    G8PullbackStageSupport :=
  g8OffAxisChartAudit_stageSupport
    (g8PrimePolarityLocalizationAudit_to_chartAudit audit)

/-- Finite stages remain finite-only substrate. -/
theorem g8PrimePolarityLocalizationAudit_finiteOnly
    (audit : G8PrimePolarityLocalizationAudit) :
    finiteG8bContext.finiteOnly :=
  g8OffAxisChartAudit_finiteOnly
    (g8PrimePolarityLocalizationAudit_to_chartAudit audit)

/-- Finite stages carry no xi-divisor claim. -/
theorem g8PrimePolarityLocalizationAudit_noXiDivisorClaim
    (audit : G8PrimePolarityLocalizationAudit) :
    finiteG8bContext.noXiDivisorClaim :=
  g8OffAxisChartAudit_noXiDivisorClaim
    (g8PrimePolarityLocalizationAudit_to_chartAudit audit)

/-- Finite stages carry no analytic-completion claim. -/
theorem g8PrimePolarityLocalizationAudit_noAnalyticCompletionClaim
    (audit : G8PrimePolarityLocalizationAudit) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8OffAxisChartAudit_noAnalyticCompletionClaim
    (g8PrimePolarityLocalizationAudit_to_chartAudit audit)

/-- The finite stage is visible at its primorial support. -/
theorem g8PrimePolarityLocalizationAudit_stageVisible
    (audit : G8PrimePolarityLocalizationAudit) :
    G8aFiniteSupportVisibleAt
      (g8PrimePolarityLocalizationAudit_lab
        audit).stageSupport.approximant.support.modulus
      (g8PrimePolarityLocalizationAudit_lab
        audit).stageSupport.approximant.support.stage :=
  g8OffAxisChartAudit_stageVisible
    (g8PrimePolarityLocalizationAudit_to_chartAudit audit)

/-- The finite stage projection is compatible with the declared support. -/
theorem g8PrimePolarityLocalizationAudit_stageProjectionCompatible
    (audit : G8PrimePolarityLocalizationAudit)
    (x : Nat) :
    (g8PrimePolarityLocalizationAudit_lab
      audit).stageSupport.approximant.support.residue
        (PrimorialStageProjection x
          (g8PrimePolarityLocalizationAudit_lab
            audit).stageSupport.approximant.support.stage) =
      (g8PrimePolarityLocalizationAudit_lab
        audit).stageSupport.approximant.support.residue x :=
  g8OffAxisChartAudit_stageProjectionCompatible
    (g8PrimePolarityLocalizationAudit_to_chartAudit audit) x

-- ============================================================
-- FALSIFIER PRESSURE
-- ============================================================

/-- Axis-but-unbalanced witnesses refute the prime-polarity audit. -/
theorem g8PrimePolarityLocalizationAudit_refutes_axisButUnbalanced
    (audit : G8PrimePolarityLocalizationAudit)
    (w :
      G8PrimePolarityAxisButUnbalancedWitness
        audit.eqCtx.chart audit.eqCtx.shadowTauRelated) :
    False :=
  g8PrimePolarityChartEquation_axisButUnbalanced_refutes_context
    audit.eqCtx w

/-- Balanced-but-off-axis witnesses refute the prime-polarity audit. -/
theorem g8PrimePolarityLocalizationAudit_refutes_balancedButOffAxis
    (audit : G8PrimePolarityLocalizationAudit)
    (w :
      G8PrimePolarityBalancedButOffAxisWitness
        audit.eqCtx.chart audit.eqCtx.shadowTauRelated) :
    False :=
  g8PrimePolarityChartEquation_balancedButOffAxis_refutes_context
    audit.eqCtx w

/-- A stage-indexed off-axis ghost refutes the prime-polarity audit. -/
theorem g8PrimePolarityLocalizationAudit_refutes_stageIndexedOffAxisGhost
    (audit : G8PrimePolarityLocalizationAudit)
    (w :
      G8StageIndexedOffAxisGhostWitness
        (g8PrimePolarityLocalizationAudit_lab audit)) :
    False :=
  g8OffAxisChartAudit_refutes_stageIndexedOffAxisGhost
    (g8PrimePolarityLocalizationAudit_to_chartAudit audit) w

/-- The relation-level chart-faithfulness failure refutes the audit. -/
theorem g8PrimePolarityLocalizationAudit_refutes_chartFaithfulnessFailure
    (audit : G8PrimePolarityLocalizationAudit)
    (w :
      G8StageIndexedOffAxisChartFaithfulnessFailure
        (g8PrimePolarityLocalizationAudit_chartCorridor audit)) :
    False :=
  g8OffAxisChartAudit_refutes_chartFaithfulnessFailure
    (g8PrimePolarityLocalizationAudit_to_chartAudit audit) w

/-- On-axis candidates remain localization-tolerated only; the audit makes no
    ghost-existence or divisor-classification claim. -/
theorem g8PrimePolarityLocalizationAudit_onAxisCandidate_tolerated
    (audit : G8PrimePolarityLocalizationAudit)
    (w :
      G8StageIndexedOnAxisGhostCandidate
        (g8PrimePolarityLocalizationAudit_lab audit)) :
    True :=
  g8OffAxisChartAudit_onAxisCandidateTolerated
    (g8PrimePolarityLocalizationAudit_to_chartAudit audit) w

/-- On-axis tolerance is not divisor classification at the prime-polarity
    audit level. -/
theorem g8PrimePolarityLocalizationAudit_onAxisCandidate_notDivisorClassification
    (audit : G8PrimePolarityLocalizationAudit)
    (w :
      G8StageIndexedOnAxisGhostCandidate
        (g8PrimePolarityLocalizationAudit_lab audit)) :
    True :=
  g8OffAxisChartAudit_onAxisCandidate_notDivisorClassification
    (g8PrimePolarityLocalizationAudit_to_chartAudit audit) w

/-- On-axis tolerance does not assert ghost existence at the prime-polarity
    audit level. -/
theorem g8PrimePolarityLocalizationAudit_onAxisCandidate_noGhostExistenceClaim
    (audit : G8PrimePolarityLocalizationAudit)
    (w :
      G8StageIndexedOnAxisGhostCandidate
        (g8PrimePolarityLocalizationAudit_lab audit)) :
    True :=
  g8OffAxisChartAudit_onAxisCandidate_noGhostExistenceClaim
    (g8PrimePolarityLocalizationAudit_to_chartAudit audit) w

end Tau.BookIII.Bridge
