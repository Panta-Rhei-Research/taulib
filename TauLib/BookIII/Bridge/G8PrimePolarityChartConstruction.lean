import TauLib.BookIII.Bridge.G8PrimePolarityLocalizationAudit

/-!
# TauLib.BookIII.Bridge.G8PrimePolarityChartConstruction

Prime-polarity chart construction from boundary normal form.

The preceding prime-polarity modules made the balance/axis law explicit as a
proof field.  This module takes the next construction step: it defines a small
theorem-backed tau source shadow from `BoundaryNF` to `CriticalAxisShadow`.

The source shadow is deliberately local and normalized:

* its axis offset is zero exactly when the B/C parts of the boundary normal
  form are balanced;
* alignment of a receiving chart to this tau source shadow supplies the
  existing `G8PrimePolarityChartEquationContext`;
* the resulting localization audit keeps all finite-stage and off-axis
  falsifier guardrails visible.

No analytic-completion uniqueness, O3 theorem, full xi-divisor transfer, or
classical RH theorem is proved here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- THEOREM-BACKED PRIME-POLARITY SOURCE SHADOW
-- ============================================================

/-- Normalized prime-polarity axis offset.

The offset is zero exactly on the B/C balance locus and one otherwise.  This
is a local chart-shadow normal form, not a zeta-zero coordinate. -/
def primePolarityAxisOffset (nf : BoundaryNF) : Nat :=
  if nf.b_part = nf.c_part then 0 else 1

/-- Prime-polarity source shadow associated to a tau boundary normal form. -/
def primePolarityAxisShadow (nf : BoundaryNF) :
    CriticalAxisShadow where
  axisOffset := primePolarityAxisOffset nf
  heightWitness := nf.depth

/-- The prime-polarity source shadow is on the receiving critical axis exactly
    when the tau boundary normal form is B/C-balanced. -/
theorem primePolarityAxisShadow_onAxis_iff_bcBalanced
    (nf : BoundaryNF) :
    OnCriticalAxis (primePolarityAxisShadow nf) ↔ BCBalanced nf := by
  unfold primePolarityAxisShadow OnCriticalAxis
    primePolarityAxisOffset BCBalanced
  by_cases h : nf.b_part = nf.c_part
  · simp [h]
  · simp [h]

/-- Off-axis in the source shadow is exactly tau B/C imbalance. -/
theorem primePolarityAxisShadow_offAxis_iff_bcImbalance
    (nf : BoundaryNF) :
    ShadowOffAxis (primePolarityAxisShadow nf) ↔ TauBCImbalance nf := by
  unfold ShadowOffAxis TauBCImbalance
  exact not_congr (primePolarityAxisShadow_onAxis_iff_bcBalanced nf)

-- ============================================================
-- CONSTRUCTION CONTEXT
-- ============================================================

/-- Alignment of a receiving chart to the prime-polarity source shadow. -/
def G8PrimePolarityShadowAlignment
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (shadowTauRelated : G8OffAxisChartRelation chart) : Prop :=
  ∀ (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness),
    shadowTauRelated z w →
      chart.centeredShadow z =
        primePolarityAxisShadow (ctx.test.tauNormalForm w)

/-- Concrete construction context for the prime-polarity chart equation.

The hard analytic obligation is now isolated as `shadowAligned`: related
receiving/tau witnesses must have the receiving chart shadow equal to the
prime-polarity source shadow of the tau normal form. -/
structure G8PrimePolarityChartConstructionContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  source : G8PrimePolarityChartSource := {}
  chart : G8OffAxisChartObject ctx
  shadowTauRelated : G8OffAxisChartRelation chart
  offAxisHasTauPreimage :
    G8OffAxisTauPreimageExists chart shadowTauRelated
  shadowAligned :
    G8PrimePolarityShadowAlignment chart shadowTauRelated
  tauWitness : G8OffAxisTauWitnessRealization chart
  offAxisGuard : G8OffAxisChartOnlyGhostGuard chart

-- ============================================================
-- CONSTRUCTION SELECTORS
-- ============================================================

/-- The construction context exposes the master-switch source discipline. -/
theorem g8PrimePolarityChartConstruction_masterSwitches
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (construction : G8PrimePolarityChartConstructionContext ctx) :
    G8MasterSwitchesRecognized :=
  construction.source.masterSwitches

/-- The construction context exposes canonical prime polarity. -/
theorem g8PrimePolarityChartConstruction_primePolarity
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (construction : G8PrimePolarityChartConstructionContext ctx) :
    CanonicalPrimePolarityRecognized :=
  construction.source.primePolarity

/-- Related receiving/tau witnesses have the constructed source shadow. -/
theorem g8PrimePolarityChartConstruction_shadowAligned
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (construction : G8PrimePolarityChartConstructionContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hRel : construction.shadowTauRelated z w) :
    construction.chart.centeredShadow z =
      primePolarityAxisShadow (ctx.test.tauNormalForm w) :=
  construction.shadowAligned z w hRel

/-- The construction context derives the balance/axis equation from source
    shadow alignment. -/
theorem g8PrimePolarityChartConstruction_balanceAxisEquation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (construction : G8PrimePolarityChartConstructionContext ctx) :
    G8PrimePolarityBalanceAxisEquation
      construction.chart construction.shadowTauRelated := by
  intro z w hRel
  unfold G8ChartCriticalAxis
  rw [g8PrimePolarityChartConstruction_shadowAligned
    construction z w hRel]
  exact
    primePolarityAxisShadow_onAxis_iff_bcBalanced
      (ctx.test.tauNormalForm w)

/-- Related axis data is equivalent to related tau B/C balance. -/
theorem g8PrimePolarityChartConstruction_axis_iff_balance
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (construction : G8PrimePolarityChartConstructionContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hRel : construction.shadowTauRelated z w) :
    G8ChartCriticalAxis construction.chart z ↔
      BCBalanced (ctx.test.tauNormalForm w) :=
  g8PrimePolarityChartConstruction_balanceAxisEquation
    construction z w hRel

/-- A related off-axis preimage carries tau B/C imbalance. -/
theorem g8PrimePolarityChartConstruction_offAxis_relatedPreimage_bcImbalance
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (construction : G8PrimePolarityChartConstructionContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hOffAxis : G8ChartOffAxis construction.chart z)
    (hRel : construction.shadowTauRelated z w) :
    TauBCImbalance (ctx.test.tauNormalForm w) := by
  intro hBalanced
  have hAxis : G8ChartCriticalAxis construction.chart z :=
    (g8PrimePolarityChartConstruction_axis_iff_balance
      construction z w hRel).mpr hBalanced
  exact (g8ChartOffAxis_notCriticalAxis
    construction.chart hOffAxis) hAxis

-- ============================================================
-- ADAPTERS INTO EXISTING CORRIDORS
-- ============================================================

/-- The construction context builds the equation-level prime-polarity chart
    context. -/
def g8PrimePolarityChartConstruction_to_equationContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (construction : G8PrimePolarityChartConstructionContext ctx) :
    G8PrimePolarityChartEquationContext ctx where
  source := construction.source
  chart := construction.chart
  shadowTauRelated := construction.shadowTauRelated
  offAxisHasTauPreimage := construction.offAxisHasTauPreimage
  balanceAxisEquation :=
    g8PrimePolarityChartConstruction_balanceAxisEquation construction
  tauWitness := construction.tauWitness
  offAxisGuard := construction.offAxisGuard

/-- The construction context plugs into the local one-sided pullback. -/
theorem g8PrimePolarityChartConstruction_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (construction : G8PrimePolarityChartConstructionContext ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8PrimePolarityChartEquation_yields_pullback ctx
    (g8PrimePolarityChartConstruction_to_equationContext construction)

/-- The construction context plus tau-side purity yields the local
    no-off-critical-zero conclusion. -/
theorem g8PrimePolarityChartConstruction_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (construction : G8PrimePolarityChartConstructionContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8PrimePolarityChartEquation_noOffCriticalZeros ctx
    (g8PrimePolarityChartConstruction_to_equationContext construction)
    tauPurity

/-- Build the stage-aware localization audit from the construction context. -/
def g8PrimePolarityChartConstruction_to_localizationAudit
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (construction : G8PrimePolarityChartConstructionContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base)
    (stage : Nat) (factor : Nat → Nat)
    (stageAdmissible : ctx.test.base.orthodoxZero → Prop)
    (sameTauTowerSubstrate : ctx.test.base.orthodoxZero → Prop)
    (sameFiniteApproximantSubstrate :
      ctx.test.base.orthodoxZero → Prop)
    (receivingShadowAdmissible :
      ctx.test.base.orthodoxZero → Prop) :
    G8PrimePolarityLocalizationAudit where
  ctx := ctx
  eqCtx :=
    g8PrimePolarityChartConstruction_to_equationContext construction
  tauPurity := tauPurity
  stage := stage
  factor := factor
  stageAdmissible := stageAdmissible
  sameTauTowerSubstrate := sameTauTowerSubstrate
  sameFiniteApproximantSubstrate := sameFiniteApproximantSubstrate
  receivingShadowAdmissible := receivingShadowAdmissible

-- ============================================================
-- AUDIT-LEVEL SELECTORS
-- ============================================================

/-- The construction-derived audit exposes the axis iff B/C-balance law. -/
theorem g8PrimePolarityChartConstruction_audit_axis_iff_balance
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (construction : G8PrimePolarityChartConstructionContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base)
    (stage : Nat) (factor : Nat → Nat)
    (stageAdmissible : ctx.test.base.orthodoxZero → Prop)
    (sameTauTowerSubstrate : ctx.test.base.orthodoxZero → Prop)
    (sameFiniteApproximantSubstrate :
      ctx.test.base.orthodoxZero → Prop)
    (receivingShadowAdmissible :
      ctx.test.base.orthodoxZero → Prop)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hRel : construction.shadowTauRelated z w) :
    G8ChartCriticalAxis construction.chart z ↔
      BCBalanced (ctx.test.tauNormalForm w) :=
  g8PrimePolarityLocalizationAudit_axis_iff_balance
    (g8PrimePolarityChartConstruction_to_localizationAudit
      ctx construction tauPurity stage factor stageAdmissible
      sameTauTowerSubstrate sameFiniteApproximantSubstrate
      receivingShadowAdmissible)
    z w hRel

/-- The construction-derived audit keeps finite stages below xi-divisor
    claims. -/
theorem g8PrimePolarityChartConstruction_audit_noXiDivisorClaim
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (construction : G8PrimePolarityChartConstructionContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base)
    (stage : Nat) (factor : Nat → Nat)
    (stageAdmissible : ctx.test.base.orthodoxZero → Prop)
    (sameTauTowerSubstrate : ctx.test.base.orthodoxZero → Prop)
    (sameFiniteApproximantSubstrate :
      ctx.test.base.orthodoxZero → Prop)
    (receivingShadowAdmissible :
      ctx.test.base.orthodoxZero → Prop) :
    finiteG8bContext.noXiDivisorClaim :=
  g8PrimePolarityLocalizationAudit_noXiDivisorClaim
    (g8PrimePolarityChartConstruction_to_localizationAudit
      ctx construction tauPurity stage factor stageAdmissible
      sameTauTowerSubstrate sameFiniteApproximantSubstrate
      receivingShadowAdmissible)

/-- The construction-derived audit keeps finite stages below analytic
    completion claims. -/
theorem g8PrimePolarityChartConstruction_audit_noAnalyticCompletionClaim
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (construction : G8PrimePolarityChartConstructionContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base)
    (stage : Nat) (factor : Nat → Nat)
    (stageAdmissible : ctx.test.base.orthodoxZero → Prop)
    (sameTauTowerSubstrate : ctx.test.base.orthodoxZero → Prop)
    (sameFiniteApproximantSubstrate :
      ctx.test.base.orthodoxZero → Prop)
    (receivingShadowAdmissible :
      ctx.test.base.orthodoxZero → Prop) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8PrimePolarityLocalizationAudit_noAnalyticCompletionClaim
    (g8PrimePolarityChartConstruction_to_localizationAudit
      ctx construction tauPurity stage factor stageAdmissible
      sameTauTowerSubstrate sameFiniteApproximantSubstrate
      receivingShadowAdmissible)

-- ============================================================
-- MISALIGNMENT AND EXISTING FALSIFIER PRESSURE
-- ============================================================

/-- A related receiving/tau witness whose chart shadow is not the
    prime-polarity source shadow refutes the construction alignment. -/
structure G8PrimePolarityShadowMisalignmentWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (shadowTauRelated : G8OffAxisChartRelation chart) where
  z : ctx.test.base.orthodoxZero
  w : ctx.test.base.tauWitness
  related : shadowTauRelated z w
  notAligned :
    chart.centeredShadow z ≠
      primePolarityAxisShadow (ctx.test.tauNormalForm w)

/-- A shadow-misalignment witness refutes the construction context. -/
theorem g8PrimePolarityShadowMisalignment_refutes_construction
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (construction : G8PrimePolarityChartConstructionContext ctx)
    (w :
      G8PrimePolarityShadowMisalignmentWitness
        construction.chart construction.shadowTauRelated) :
    False :=
  w.notAligned (construction.shadowAligned w.z w.w w.related)

/-- Axis-but-unbalanced witnesses refute the constructed equation context. -/
theorem g8PrimePolarityChartConstruction_refutes_axisButUnbalanced
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (construction : G8PrimePolarityChartConstructionContext ctx)
    (w :
      G8PrimePolarityAxisButUnbalancedWitness
        construction.chart construction.shadowTauRelated) :
    False :=
  g8PrimePolarityChartEquation_axisButUnbalanced_refutes_context
    (g8PrimePolarityChartConstruction_to_equationContext construction)
    w

/-- Balanced-but-off-axis witnesses refute the constructed equation context. -/
theorem g8PrimePolarityChartConstruction_refutes_balancedButOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (construction : G8PrimePolarityChartConstructionContext ctx)
    (w :
      G8PrimePolarityBalancedButOffAxisWitness
        construction.chart construction.shadowTauRelated) :
    False :=
  g8PrimePolarityChartEquation_balancedButOffAxis_refutes_context
    (g8PrimePolarityChartConstruction_to_equationContext construction)
    w

/-- A stage-indexed off-axis ghost refutes the construction-derived audit. -/
theorem g8PrimePolarityChartConstruction_refutes_stageIndexedOffAxisGhost
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (construction : G8PrimePolarityChartConstructionContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base)
    (stage : Nat) (factor : Nat → Nat)
    (stageAdmissible : ctx.test.base.orthodoxZero → Prop)
    (sameTauTowerSubstrate : ctx.test.base.orthodoxZero → Prop)
    (sameFiniteApproximantSubstrate :
      ctx.test.base.orthodoxZero → Prop)
    (receivingShadowAdmissible :
      ctx.test.base.orthodoxZero → Prop)
    (w :
      G8StageIndexedOffAxisGhostWitness
        (g8PrimePolarityLocalizationAudit_lab
          (g8PrimePolarityChartConstruction_to_localizationAudit
            ctx construction tauPurity stage factor stageAdmissible
            sameTauTowerSubstrate sameFiniteApproximantSubstrate
            receivingShadowAdmissible))) :
    False :=
  g8PrimePolarityLocalizationAudit_refutes_stageIndexedOffAxisGhost
    (g8PrimePolarityChartConstruction_to_localizationAudit
      ctx construction tauPurity stage factor stageAdmissible
      sameTauTowerSubstrate sameFiniteApproximantSubstrate
      receivingShadowAdmissible)
    w

/-- A relation-level chart-faithfulness failure refutes the
    construction-derived audit. -/
theorem g8PrimePolarityChartConstruction_refutes_chartFaithfulnessFailure
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (construction : G8PrimePolarityChartConstructionContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base)
    (stage : Nat) (factor : Nat → Nat)
    (stageAdmissible : ctx.test.base.orthodoxZero → Prop)
    (sameTauTowerSubstrate : ctx.test.base.orthodoxZero → Prop)
    (sameFiniteApproximantSubstrate :
      ctx.test.base.orthodoxZero → Prop)
    (receivingShadowAdmissible :
      ctx.test.base.orthodoxZero → Prop)
    (w :
      G8StageIndexedOffAxisChartFaithfulnessFailure
        (g8PrimePolarityLocalizationAudit_chartCorridor
          (g8PrimePolarityChartConstruction_to_localizationAudit
            ctx construction tauPurity stage factor stageAdmissible
            sameTauTowerSubstrate sameFiniteApproximantSubstrate
            receivingShadowAdmissible))) :
    False :=
  g8PrimePolarityLocalizationAudit_refutes_chartFaithfulnessFailure
    (g8PrimePolarityChartConstruction_to_localizationAudit
      ctx construction tauPurity stage factor stageAdmissible
      sameTauTowerSubstrate sameFiniteApproximantSubstrate
      receivingShadowAdmissible)
    w

end Tau.BookIII.Bridge
