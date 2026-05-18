import TauLib.BookIII.Bridge.G8WeakOffAxisPullbackRealization

/-!
# TauLib.BookIII.Bridge.G8OffAxisChartFaithfulnessCore

Core off-axis chart-faithfulness interface for the weak G8 corridor.

The preceding modules packaged the weak off-axis corridor from both sides:

* the negative side: a stage-compatible off-axis receiving shadow with no
  tau-native imbalance preimage is fatal;
* the positive side: an orthodox off-critical shadow must become an off-axis
  readable chart signal, then a tau-related preimage, then a tau-native
  imbalance witness.

This module sharpens the positive side around the source geometry:

* the receiving-side axis is the centered fold axis from `CriticalAxisShadow`;
* the tau-side balance locus is the `J`-fixed / B-C equalizer locus;
* off-axis chart faithfulness means that a related off-axis receiving shadow
  carries B-C imbalance on the tau side.

The module is still an interface.  It does not prove an analytic chart,
analytic-completion uniqueness, O3, full zero-divisor transfer, or any
classical RH result.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- EXPLICIT AXIS / BALANCE VOCABULARY
-- ============================================================

/-- The receiving-side critical-axis image in the centered shadow model. -/
def G8OrthodoxCriticalAxisImage
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (z : ctx.test.base.orthodoxZero) : Prop :=
  OnCriticalAxis (ctx.test.orthodoxShadow z)

/-- The receiving-side off-axis image in the centered shadow model. -/
def G8OrthodoxOffAxisImage
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (z : ctx.test.base.orthodoxZero) : Prop :=
  ShadowOffAxis (ctx.test.orthodoxShadow z)

/-- Off-axis image data is exactly fold-obstruction data in the local centered
    shadow model.  This is the algebraic shadow of the quadratic fold only; it
    carries no zero-divisor claim. -/
theorem g8OrthodoxOffAxisImage_iff_foldObstruction
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (z : ctx.test.base.orthodoxZero) :
    G8OrthodoxOffAxisImage ctx z ↔
      ShadowFoldObstruction (ctx.test.orthodoxShadow z) :=
  shadowOffAxis_iff_foldObstruction (ctx.test.orthodoxShadow z)

/-- The tau-native balance locus for a witness candidate. -/
def G8TauBalanceLocus
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (w : ctx.test.base.tauWitness) : Prop :=
  TauCriticalLocus (ctx.test.tauNormalForm w)

/-- The tau-native B-C equalizer form of the same balance locus. -/
def G8TauBCEqualizer
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (w : ctx.test.base.tauWitness) : Prop :=
  BCBalanced (ctx.test.tauNormalForm w)

/-- The tau balance locus is exactly the B-C equalizer locus. -/
theorem g8TauBalanceLocus_iff_bcEqualizer
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (w : ctx.test.base.tauWitness) :
    G8TauBalanceLocus ctx w ↔ G8TauBCEqualizer ctx w :=
  tauCriticalLocus_iff_bcBalanced (ctx.test.tauNormalForm w)

/-- The tau-native imbalance form used by the pullback corridor is exactly
    failure of the B-C equalizer. -/
theorem g8TauCriticalImbalance_iff_bcImbalance
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (w : ctx.test.base.tauWitness) :
    TauCriticalImbalance (ctx.test.tauNormalForm w) ↔
      TauBCImbalance (ctx.test.tauNormalForm w) :=
  tauCriticalImbalance_iff_bcImbalance (ctx.test.tauNormalForm w)

-- ============================================================
-- CORE OFF-AXIS CHART FAITHFULNESS
-- ============================================================

/-- Core off-axis chart-faithfulness package.

Compared with `G8WeakOffAxisPullbackRealizationContext`, this record names
the tau-side consequence as B-C imbalance.  That is the source-geometric
content of the current route: off-axis receiving shadows may pass through the
chart only if their related tau preimages leave the B-C equalizer / `J`-fixed
balance locus.
-/
structure G8OffAxisChartFaithfulnessCore
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  shadowTauRelated :
    ctx.test.base.orthodoxZero → ctx.test.base.tauWitness → Prop
  localFold : G8e1LocalFoldReadable ctx.test
  offAxisHasTauPreimage :
    ∀ z : ctx.test.base.orthodoxZero,
      G8OrthodoxOffAxisImage ctx z →
        ∃ w : ctx.test.base.tauWitness, shadowTauRelated z w
  relatedPreimageCarriesBCImbalance :
    ∀ (z : ctx.test.base.orthodoxZero)
      (w : ctx.test.base.tauWitness),
      G8OrthodoxOffAxisImage ctx z →
        shadowTauRelated z w →
          TauBCImbalance (ctx.test.tauNormalForm w)
  tauWitness : G8e1TauImbalanceRealizesWitness ctx.test
  offAxisGuard : NoChartOnlyOffCriticalZerosOutsideAxis ctx.test

/-- The core package yields the realization ladder's tau-critical imbalance
    preservation field. -/
theorem g8OffAxisChartFaithfulnessCore_imbalancePreservation
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (core : G8OffAxisChartFaithfulnessCore ctx) :
    ∀ (z : ctx.test.base.orthodoxZero)
      (w : ctx.test.base.tauWitness),
      ShadowOffAxis (ctx.test.orthodoxShadow z) →
        core.shadowTauRelated z w →
          TauCriticalImbalance (ctx.test.tauNormalForm w) := by
  intro z w hOffAxis hRel
  exact
    (tauCriticalImbalance_iff_bcImbalance
      (ctx.test.tauNormalForm w)).mpr
      (core.relatedPreimageCarriesBCImbalance z w hOffAxis hRel)

/-- The core package rebuilds the positive realization ladder. -/
def g8OffAxisChartFaithfulnessCore_to_realization
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (core : G8OffAxisChartFaithfulnessCore ctx) :
    G8WeakOffAxisPullbackRealizationContext ctx where
  shadowTauRelated := core.shadowTauRelated
  localFold := core.localFold
  offAxisHasTauPreimage := core.offAxisHasTauPreimage
  relatedPreimageCarriesTauImbalance :=
    g8OffAxisChartFaithfulnessCore_imbalancePreservation ctx core
  tauWitness := core.tauWitness
  offAxisGuard := core.offAxisGuard

/-- The core package exposes the existing weak pullback subobligations. -/
def g8OffAxisChartFaithfulnessCore_weakSubobligations
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (core : G8OffAxisChartFaithfulnessCore ctx) :
    G8WeakOffCriticalPullbackSubobligations ctx :=
  g8WeakOffAxisRealization_weakSubobligations ctx
    (g8OffAxisChartFaithfulnessCore_to_realization ctx core)

/-- The core package yields the one-sided pullback. -/
theorem g8OffAxisChartFaithfulnessCore_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (core : G8OffAxisChartFaithfulnessCore ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8WeakOffAxisRealization_yields_pullback ctx
    (g8OffAxisChartFaithfulnessCore_to_realization ctx core)

/-- Core off-axis chart faithfulness plus tau-side purity yields the local
    no-off-critical-zero conclusion. -/
theorem g8OffAxisChartFaithfulnessCore_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (core : G8OffAxisChartFaithfulnessCore ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8WeakOffAxisRealization_noOffCriticalZeros ctx
    (g8OffAxisChartFaithfulnessCore_to_realization ctx core)
    tauPurity

-- ============================================================
-- LOCAL FAILURE WITNESSES
-- ============================================================

/-- A related off-axis tau preimage that remains B-C-balanced.  This is the
    source-geometric form of the balanced-preimage falsifier. -/
structure G8OffAxisRelatedPreimageBCBalancedWitness
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (shadowTauRelated :
      ctx.test.base.orthodoxZero → ctx.test.base.tauWitness → Prop) where
  z : ctx.test.base.orthodoxZero
  w : ctx.test.base.tauWitness
  offAxis : G8OrthodoxOffAxisImage ctx z
  related : shadowTauRelated z w
  balanced : G8TauBCEqualizer ctx w

/-- A B-C-balanced related preimage refutes the core B-C imbalance field. -/
theorem g8OffAxisBCBalanced_refutes_bcImbalancePreservation
    (ctx : G8WeakOffCriticalPullbackTestContext)
    {shadowTauRelated :
      ctx.test.base.orthodoxZero → ctx.test.base.tauWitness → Prop}
    (w :
      G8OffAxisRelatedPreimageBCBalancedWitness
        ctx shadowTauRelated) :
    ¬ (∀ (z : ctx.test.base.orthodoxZero)
        (tauW : ctx.test.base.tauWitness),
        G8OrthodoxOffAxisImage ctx z →
          shadowTauRelated z tauW →
            TauBCImbalance (ctx.test.tauNormalForm tauW)) := by
  intro h
  unfold TauBCImbalance at h
  exact h w.z w.w w.offAxis w.related w.balanced

/-- A B-C-balanced related preimage refutes a core package using that
    relation. -/
theorem g8OffAxisBCBalanced_refutes_core
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (core : G8OffAxisChartFaithfulnessCore ctx)
    (w :
      G8OffAxisRelatedPreimageBCBalancedWitness
        ctx core.shadowTauRelated) :
    False :=
  g8OffAxisBCBalanced_refutes_bcImbalancePreservation
    ctx w core.relatedPreimageCarriesBCImbalance

/-- The existing no-preimage witness refutes the core package. -/
theorem g8NoTauPreimageForOffAxisShadow_refutes_core
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (core : G8OffAxisChartFaithfulnessCore ctx)
    (w :
      G8NoTauPreimageForOffAxisShadowWitness
        ctx core.shadowTauRelated) :
    False :=
  g8NoTauPreimageForOffAxisShadow_refutes_realization
    ctx (g8OffAxisChartFaithfulnessCore_to_realization ctx core) w

/-- An unreadable off-critical shadow refutes the core package. -/
theorem g8UnreadableOffCriticalShadow_refutes_core
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (w : G8UnreadableOffCriticalShadowWitness ctx) :
    ¬ Nonempty (G8OffAxisChartFaithfulnessCore ctx) := by
  intro h
  rcases h with ⟨core⟩
  exact g8UnreadableOffCriticalShadow_refutes_localFold
    ctx w core.localFold

/-- An off-axis chart-only ghost refutes the core package. -/
theorem g8OffAxisChartOnlyGhost_refutes_core
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (core : G8OffAxisChartFaithfulnessCore ctx)
    (w : G8OffAxisChartOnlyGhostWitness ctx.test) :
    False :=
  g8OffAxisChartOnlyGhost_refutes_realization
    ctx (g8OffAxisChartFaithfulnessCore_to_realization ctx core) w

-- ============================================================
-- STAGE-AWARE HANDOFF
-- ============================================================

/-- Stage-aware core faithfulness package tied to the current off-axis
    corridor and weak completion lab. -/
structure G8StageAwareOffAxisChartFaithfulnessCore
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) where
  lab : G8WeakOffAxisCompletionContext stageCorridor
  core :
    G8OffAxisChartFaithfulnessCore
      stageCorridor.corridor.weakTest

/-- The stage-aware core package rebuilds the existing stage-aware realization
    handoff. -/
def g8StageAwareOffAxisChartFaithfulnessCore_to_realization
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (core : G8StageAwareOffAxisChartFaithfulnessCore stageCorridor) :
    G8StageAwareWeakOffAxisPullbackRealization stageCorridor where
  lab := core.lab
  realization :=
    g8OffAxisChartFaithfulnessCore_to_realization
      stageCorridor.corridor.weakTest core.core

/-- Stage-aware core faithfulness exposes the finite stage support. -/
def g8StageAwareOffAxisChartFaithfulnessCore_stageSupport
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (core : G8StageAwareOffAxisChartFaithfulnessCore stageCorridor) :
    G8PullbackStageSupport :=
  g8StageAwareWeakOffAxisRealization_stageSupport
    (g8StageAwareOffAxisChartFaithfulnessCore_to_realization core)

/-- Stage-aware core faithfulness keeps finite data finite-only. -/
theorem g8StageAwareOffAxisChartFaithfulnessCore_finiteOnly
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (core : G8StageAwareOffAxisChartFaithfulnessCore stageCorridor) :
    finiteG8bContext.finiteOnly :=
  g8StageAwareWeakOffAxisRealization_finiteOnly
    (g8StageAwareOffAxisChartFaithfulnessCore_to_realization core)

/-- Stage-aware core faithfulness carries no xi-divisor claim from finite
    stages. -/
theorem g8StageAwareOffAxisChartFaithfulnessCore_noXiDivisorClaim
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (core : G8StageAwareOffAxisChartFaithfulnessCore stageCorridor) :
    finiteG8bContext.noXiDivisorClaim :=
  g8StageAwareWeakOffAxisRealization_noXiDivisorClaim
    (g8StageAwareOffAxisChartFaithfulnessCore_to_realization core)

/-- Stage-aware core faithfulness carries no analytic-completion claim from
    finite stages. -/
theorem g8StageAwareOffAxisChartFaithfulnessCore_noAnalyticCompletionClaim
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (core : G8StageAwareOffAxisChartFaithfulnessCore stageCorridor) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8StageAwareWeakOffAxisRealization_noAnalyticCompletionClaim
    (g8StageAwareOffAxisChartFaithfulnessCore_to_realization core)

/-- Stage-aware core faithfulness exposes the local no-off-critical-zero
    conclusion already guarded by the corridor's tau purity. -/
theorem g8StageAwareOffAxisChartFaithfulnessCore_noOffCriticalZeros
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (core : G8StageAwareOffAxisChartFaithfulnessCore stageCorridor) :
    G8eNoOrthodoxOffCriticalZeros
      stageCorridor.corridor.weakTest.test.base :=
  g8StageAwareWeakOffAxisRealization_noOffCriticalZeros
    (g8StageAwareOffAxisChartFaithfulnessCore_to_realization core)

/-- A fatal stage-indexed off-axis ghost remains the standing countermodel
    pressure against the stage-aware core package. -/
theorem g8StageAwareOffAxisChartFaithfulnessCore_fatalGhost_refutes
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (core : G8StageAwareOffAxisChartFaithfulnessCore stageCorridor)
    (w : G8StageIndexedOffAxisGhostWitness core.lab) :
    False :=
  g8StageAwareWeakOffAxisRealization_fatalGhost_refutes
    (g8StageAwareOffAxisChartFaithfulnessCore_to_realization core) w

end Tau.BookIII.Bridge
