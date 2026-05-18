import TauLib.BookIII.Bridge.G8PrimePolarityChartConstruction

/-!
# TauLib.BookIII.Bridge.G8PrimePolarityAxisOffsetAlignment

Axis-offset alignment for the prime-polarity G8 localization corridor.

`G8PrimePolarityChartConstruction` used full `CriticalAxisShadow` equality to
derive the balance/axis equation.  That is stronger than the off-axis
localization corridor needs: RH localization only reads the centered
axis-offset coordinate.  Height/provenance data belongs to later analytic,
divisor, and multiplicity work.

This module therefore factors the construction through an axis-offset-only
alignment interface:

* `primePolarityAxisOffset` is zero exactly on B/C balance;
* related receiving/tau witnesses only need matching axis offsets;
* the existing equation context and localization audit are recovered from that
  weaker alignment;
* full-shadow alignment remains a convenience adapter;
* height mismatches are diagnostic/tolerated for localization, while
  axis-offset mismatches remain fatal.

No O3 theorem, analytic-completion uniqueness, full xi-divisor transfer, or
classical RH theorem is proved here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- AXIS-OFFSET SOURCE LAW
-- ============================================================

/-- The normalized prime-polarity axis offset vanishes exactly on B/C
    balance. -/
theorem primePolarityAxisOffset_eq_zero_iff_bcBalanced
    (nf : BoundaryNF) :
    primePolarityAxisOffset nf = 0 ↔ BCBalanced nf := by
  unfold primePolarityAxisOffset BCBalanced
  by_cases h : nf.b_part = nf.c_part
  · simp [h]
  · simp [h]

/-- Nonzero prime-polarity axis offset is exactly tau B/C imbalance. -/
theorem primePolarityAxisOffset_ne_zero_iff_bcImbalance
    (nf : BoundaryNF) :
    primePolarityAxisOffset nf ≠ 0 ↔ TauBCImbalance nf := by
  unfold TauBCImbalance
  exact not_congr (primePolarityAxisOffset_eq_zero_iff_bcBalanced nf)

-- ============================================================
-- AXIS-OFFSET ALIGNMENT CONTEXT
-- ============================================================

/-- Alignment of a receiving chart to the localization-bearing
    prime-polarity axis-offset coordinate. -/
def G8PrimePolarityAxisOffsetAlignment
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (shadowTauRelated : G8OffAxisChartRelation chart) : Prop :=
  ∀ (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness),
    shadowTauRelated z w →
      (chart.centeredShadow z).axisOffset =
        primePolarityAxisOffset (ctx.test.tauNormalForm w)

/-- Axis-offset-only construction context.

This is the localization-facing version of the prime-polarity construction:
it requires equality only of the centered off-axis displacement, not of the
entire shadow. -/
structure G8PrimePolarityAxisOffsetConstructionContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  source : G8PrimePolarityChartSource := {}
  chart : G8OffAxisChartObject ctx
  shadowTauRelated : G8OffAxisChartRelation chart
  offAxisHasTauPreimage :
    G8OffAxisTauPreimageExists chart shadowTauRelated
  axisOffsetAligned :
    G8PrimePolarityAxisOffsetAlignment chart shadowTauRelated
  tauWitness : G8OffAxisTauWitnessRealization chart
  offAxisGuard : G8OffAxisChartOnlyGhostGuard chart

-- ============================================================
-- SELECTORS AND LOCALIZATION LAW
-- ============================================================

/-- The axis-offset context exposes the master-switch source discipline. -/
theorem g8PrimePolarityAxisOffset_masterSwitches
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx) :
    G8MasterSwitchesRecognized :=
  offsetCtx.source.masterSwitches

/-- The axis-offset context exposes canonical prime polarity. -/
theorem g8PrimePolarityAxisOffset_primePolarity
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx) :
    CanonicalPrimePolarityRecognized :=
  offsetCtx.source.primePolarity

/-- Related receiving/tau witnesses have matching localization-bearing
    axis offsets. -/
theorem g8PrimePolarityAxisOffset_aligned
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hRel : offsetCtx.shadowTauRelated z w) :
    (offsetCtx.chart.centeredShadow z).axisOffset =
      primePolarityAxisOffset (ctx.test.tauNormalForm w) :=
  offsetCtx.axisOffsetAligned z w hRel

/-- Axis-offset alignment derives the same balance/axis equation without
    requiring full shadow equality. -/
theorem g8PrimePolarityAxisOffset_balanceAxisEquation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx) :
    G8PrimePolarityBalanceAxisEquation
      offsetCtx.chart offsetCtx.shadowTauRelated := by
  intro z w hRel
  unfold G8ChartCriticalAxis OnCriticalAxis
  rw [g8PrimePolarityAxisOffset_aligned offsetCtx z w hRel]
  exact
    primePolarityAxisOffset_eq_zero_iff_bcBalanced
      (ctx.test.tauNormalForm w)

/-- Related axis data is equivalent to related tau B/C balance. -/
theorem g8PrimePolarityAxisOffset_axis_iff_balance
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hRel : offsetCtx.shadowTauRelated z w) :
    G8ChartCriticalAxis offsetCtx.chart z ↔
      BCBalanced (ctx.test.tauNormalForm w) :=
  g8PrimePolarityAxisOffset_balanceAxisEquation
    offsetCtx z w hRel

/-- A related off-axis preimage carries tau B/C imbalance. -/
theorem g8PrimePolarityAxisOffset_offAxis_relatedPreimage_bcImbalance
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hOffAxis : G8ChartOffAxis offsetCtx.chart z)
    (hRel : offsetCtx.shadowTauRelated z w) :
    TauBCImbalance (ctx.test.tauNormalForm w) := by
  intro hBalanced
  have hAxis : G8ChartCriticalAxis offsetCtx.chart z :=
    (g8PrimePolarityAxisOffset_axis_iff_balance
      offsetCtx z w hRel).mpr hBalanced
  exact (g8ChartOffAxis_notCriticalAxis
    offsetCtx.chart hOffAxis) hAxis

-- ============================================================
-- ADAPTERS INTO EXISTING CORRIDORS
-- ============================================================

/-- The axis-offset context builds the equation-level prime-polarity chart
    context. -/
def g8PrimePolarityAxisOffset_to_equationContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx) :
    G8PrimePolarityChartEquationContext ctx where
  source := offsetCtx.source
  chart := offsetCtx.chart
  shadowTauRelated := offsetCtx.shadowTauRelated
  offAxisHasTauPreimage := offsetCtx.offAxisHasTauPreimage
  balanceAxisEquation :=
    g8PrimePolarityAxisOffset_balanceAxisEquation offsetCtx
  tauWitness := offsetCtx.tauWitness
  offAxisGuard := offsetCtx.offAxisGuard

/-- The axis-offset context plugs into the local one-sided pullback. -/
theorem g8PrimePolarityAxisOffset_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8PrimePolarityChartEquation_yields_pullback ctx
    (g8PrimePolarityAxisOffset_to_equationContext offsetCtx)

/-- The axis-offset context plus tau-side purity yields the local
    no-off-critical-zero conclusion. -/
theorem g8PrimePolarityAxisOffset_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8PrimePolarityChartEquation_noOffCriticalZeros ctx
    (g8PrimePolarityAxisOffset_to_equationContext offsetCtx)
    tauPurity

/-- Build the stage-aware localization audit from the axis-offset context. -/
def g8PrimePolarityAxisOffset_to_localizationAudit
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx)
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
  eqCtx := g8PrimePolarityAxisOffset_to_equationContext offsetCtx
  tauPurity := tauPurity
  stage := stage
  factor := factor
  stageAdmissible := stageAdmissible
  sameTauTowerSubstrate := sameTauTowerSubstrate
  sameFiniteApproximantSubstrate := sameFiniteApproximantSubstrate
  receivingShadowAdmissible := receivingShadowAdmissible

-- ============================================================
-- FULL-SHADOW CONSTRUCTION AS A STRONGER ADAPTER
-- ============================================================

/-- Full shadow alignment implies axis-offset alignment. -/
theorem g8PrimePolarityChartConstruction_axisOffsetAlignment
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (construction : G8PrimePolarityChartConstructionContext ctx) :
    G8PrimePolarityAxisOffsetAlignment
      construction.chart construction.shadowTauRelated := by
  intro z w hRel
  exact congrArg CriticalAxisShadow.axisOffset
    (g8PrimePolarityChartConstruction_shadowAligned
      construction z w hRel)

/-- The stronger full-shadow construction can be consumed through the
    axis-offset-only corridor. -/
def g8PrimePolarityChartConstruction_to_axisOffsetContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (construction : G8PrimePolarityChartConstructionContext ctx) :
    G8PrimePolarityAxisOffsetConstructionContext ctx where
  source := construction.source
  chart := construction.chart
  shadowTauRelated := construction.shadowTauRelated
  offAxisHasTauPreimage := construction.offAxisHasTauPreimage
  axisOffsetAligned :=
    g8PrimePolarityChartConstruction_axisOffsetAlignment construction
  tauWitness := construction.tauWitness
  offAxisGuard := construction.offAxisGuard

-- ============================================================
-- AUDIT-LEVEL GUARDRAILS
-- ============================================================

/-- The axis-offset-derived audit exposes the axis iff B/C-balance law. -/
theorem g8PrimePolarityAxisOffset_audit_axis_iff_balance
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx)
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
    (hRel : offsetCtx.shadowTauRelated z w) :
    G8ChartCriticalAxis offsetCtx.chart z ↔
      BCBalanced (ctx.test.tauNormalForm w) :=
  g8PrimePolarityLocalizationAudit_axis_iff_balance
    (g8PrimePolarityAxisOffset_to_localizationAudit
      ctx offsetCtx tauPurity stage factor stageAdmissible
      sameTauTowerSubstrate sameFiniteApproximantSubstrate
      receivingShadowAdmissible)
    z w hRel

/-- The axis-offset-derived audit keeps finite stages below xi-divisor
    claims. -/
theorem g8PrimePolarityAxisOffset_audit_noXiDivisorClaim
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx)
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
    (g8PrimePolarityAxisOffset_to_localizationAudit
      ctx offsetCtx tauPurity stage factor stageAdmissible
      sameTauTowerSubstrate sameFiniteApproximantSubstrate
      receivingShadowAdmissible)

/-- The axis-offset-derived audit keeps finite stages below analytic
    completion claims. -/
theorem g8PrimePolarityAxisOffset_audit_noAnalyticCompletionClaim
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx)
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
    (g8PrimePolarityAxisOffset_to_localizationAudit
      ctx offsetCtx tauPurity stage factor stageAdmissible
      sameTauTowerSubstrate sameFiniteApproximantSubstrate
      receivingShadowAdmissible)

-- ============================================================
-- FALSIFIER AND HEIGHT-DIAGNOSTIC DISCIPLINE
-- ============================================================

/-- A related receiving/tau witness with mismatched axis offset refutes the
    axis-offset alignment context. -/
structure G8PrimePolarityAxisOffsetMismatchWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (shadowTauRelated : G8OffAxisChartRelation chart) where
  z : ctx.test.base.orthodoxZero
  w : ctx.test.base.tauWitness
  related : shadowTauRelated z w
  axisOffsetMismatch :
    (chart.centeredShadow z).axisOffset ≠
      primePolarityAxisOffset (ctx.test.tauNormalForm w)

/-- Axis-offset mismatch refutes the axis-offset construction context. -/
theorem g8PrimePolarityAxisOffsetMismatch_refutes_context
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx)
    (w :
      G8PrimePolarityAxisOffsetMismatchWitness
        offsetCtx.chart offsetCtx.shadowTauRelated) :
    False :=
  w.axisOffsetMismatch
    (offsetCtx.axisOffsetAligned w.z w.w w.related)

/-- Height mismatch is diagnostic bookkeeping for later analytic work, not a
    localization refutation when axis offsets already agree. -/
structure G8PrimePolarityHeightMismatchDiagnostic
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (shadowTauRelated : G8OffAxisChartRelation chart) where
  z : ctx.test.base.orthodoxZero
  w : ctx.test.base.tauWitness
  related : shadowTauRelated z w
  axisOffsetAligned :
    (chart.centeredShadow z).axisOffset =
      primePolarityAxisOffset (ctx.test.tauNormalForm w)
  heightMismatch :
    (chart.centeredShadow z).heightWitness ≠
      (primePolarityAxisShadow
        (ctx.test.tauNormalForm w)).heightWitness

/-- Height mismatch alone is tolerated by the localization corridor. -/
theorem g8PrimePolarityHeightMismatchDiagnostic_tolerated
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {chart : G8OffAxisChartObject ctx}
    {shadowTauRelated : G8OffAxisChartRelation chart}
    (_w :
      G8PrimePolarityHeightMismatchDiagnostic
        chart shadowTauRelated) :
    True :=
  True.intro

/-- A full-shadow misalignment becomes fatal for localization only when it
    carries an axis-offset mismatch. -/
structure G8PrimePolarityShadowMisalignmentWithAxisOffsetMismatch
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (shadowTauRelated : G8OffAxisChartRelation chart) where
  shadowMisalignment :
    G8PrimePolarityShadowMisalignmentWitness chart shadowTauRelated
  axisOffsetMismatch :
    (chart.centeredShadow shadowMisalignment.z).axisOffset ≠
      primePolarityAxisOffset
        (ctx.test.tauNormalForm shadowMisalignment.w)

/-- Full-shadow misalignment with an axis-offset mismatch refutes the
    axis-offset construction context. -/
theorem
    g8PrimePolarityShadowMisalignment_withAxisOffsetMismatch_refutes_context
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx)
    (w :
      G8PrimePolarityShadowMisalignmentWithAxisOffsetMismatch
        offsetCtx.chart offsetCtx.shadowTauRelated) :
    False :=
  w.axisOffsetMismatch
    (offsetCtx.axisOffsetAligned
      w.shadowMisalignment.z
      w.shadowMisalignment.w
      w.shadowMisalignment.related)

/-- Full-shadow misalignment with aligned axis offsets is a height/provenance
    diagnostic for localization purposes. -/
structure G8PrimePolarityShadowMisalignmentHeightOnlyDiagnostic
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (chart : G8OffAxisChartObject ctx)
    (shadowTauRelated : G8OffAxisChartRelation chart) where
  shadowMisalignment :
    G8PrimePolarityShadowMisalignmentWitness chart shadowTauRelated
  axisOffsetAligned :
    (chart.centeredShadow shadowMisalignment.z).axisOffset =
      primePolarityAxisOffset
        (ctx.test.tauNormalForm shadowMisalignment.w)

/-- Height/provenance-only full-shadow misalignment is tolerated by the
    off-axis localization corridor. -/
theorem
    g8PrimePolarityShadowMisalignmentHeightOnlyDiagnostic_tolerated
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {chart : G8OffAxisChartObject ctx}
    {shadowTauRelated : G8OffAxisChartRelation chart}
    (_w :
      G8PrimePolarityShadowMisalignmentHeightOnlyDiagnostic
        chart shadowTauRelated) :
    True :=
  True.intro

/-- A stage-indexed off-axis ghost refutes the axis-offset-derived audit. -/
theorem g8PrimePolarityAxisOffset_refutes_stageIndexedOffAxisGhost
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx)
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
          (g8PrimePolarityAxisOffset_to_localizationAudit
            ctx offsetCtx tauPurity stage factor stageAdmissible
            sameTauTowerSubstrate sameFiniteApproximantSubstrate
            receivingShadowAdmissible))) :
    False :=
  g8PrimePolarityLocalizationAudit_refutes_stageIndexedOffAxisGhost
    (g8PrimePolarityAxisOffset_to_localizationAudit
      ctx offsetCtx tauPurity stage factor stageAdmissible
      sameTauTowerSubstrate sameFiniteApproximantSubstrate
      receivingShadowAdmissible)
    w

/-- A relation-level chart-faithfulness failure refutes the axis-offset-derived
    audit. -/
theorem g8PrimePolarityAxisOffset_refutes_chartFaithfulnessFailure
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (offsetCtx : G8PrimePolarityAxisOffsetConstructionContext ctx)
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
          (g8PrimePolarityAxisOffset_to_localizationAudit
            ctx offsetCtx tauPurity stage factor stageAdmissible
            sameTauTowerSubstrate sameFiniteApproximantSubstrate
            receivingShadowAdmissible))) :
    False :=
  g8PrimePolarityLocalizationAudit_refutes_chartFaithfulnessFailure
    (g8PrimePolarityAxisOffset_to_localizationAudit
      ctx offsetCtx tauPurity stage factor stageAdmissible
      sameTauTowerSubstrate sameFiniteApproximantSubstrate
      receivingShadowAdmissible)
    w

end Tau.BookIII.Bridge
