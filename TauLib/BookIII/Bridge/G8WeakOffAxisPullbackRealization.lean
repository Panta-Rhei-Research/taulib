import TauLib.BookIII.Bridge.G8WeakOffAxisCompletionLab

/-!
# TauLib.BookIII.Bridge.G8WeakOffAxisPullbackRealization

Positive realization ladder for the weak off-axis G8 corridor.

The completion lab sharpens the negative falsifier: an off-axis receiving
shadow with no tau-native imbalance preimage is fatal.  This module records
the matching positive route as a relation-level interface:

orthodox off-critical shadow -> off-axis readable chart signal -> tau-related
preimage -> tau-native imbalance witness -> tau-side purity contradiction.

The package remains local and conditional.  It does not prove analytic
completion uniqueness, O3, full zero-divisor transfer, or any classical RH
claim.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- POSITIVE REALIZATION LADDER
-- ============================================================

/-- Relation-level realization context for the weak off-axis route.

`shadowTauRelated` is the planned chart relation between receiving-side
off-axis shadows and tau-side witness candidates.  The fields state exactly the
positive obligations needed to rebuild the existing guarded weak pullback
package. -/
structure G8WeakOffAxisPullbackRealizationContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  shadowTauRelated :
    ctx.test.base.orthodoxZero → ctx.test.base.tauWitness → Prop
  localFold : G8e1LocalFoldReadable ctx.test
  offAxisHasTauPreimage :
    ∀ z : ctx.test.base.orthodoxZero,
      ShadowOffAxis (ctx.test.orthodoxShadow z) →
        ∃ w : ctx.test.base.tauWitness, shadowTauRelated z w
  relatedPreimageCarriesTauImbalance :
    ∀ (z : ctx.test.base.orthodoxZero)
      (w : ctx.test.base.tauWitness),
      ShadowOffAxis (ctx.test.orthodoxShadow z) →
        shadowTauRelated z w →
          TauCriticalImbalance (ctx.test.tauNormalForm w)
  tauWitness : G8e1TauImbalanceRealizesWitness ctx.test
  offAxisGuard : NoChartOnlyOffCriticalZerosOutsideAxis ctx.test

/-- The realization context yields the G8e.1 chart-faithfulness predicate. -/
theorem g8WeakOffAxisRealization_chartFaithful
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (r : G8WeakOffAxisPullbackRealizationContext ctx) :
    G8e1ChartFaithfulToTauImbalance ctx.test := by
  intro z hOffAxis
  obtain ⟨w, hRel⟩ := r.offAxisHasTauPreimage z hOffAxis
  exact ⟨w, r.relatedPreimageCarriesTauImbalance z w hOffAxis hRel⟩

/-- The realization context rebuilds the existing off-axis guarded weak
    subobligation package. -/
def g8WeakOffAxisRealization_guardedSubobligations
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (r : G8WeakOffAxisPullbackRealizationContext ctx) :
    G8OffAxisGuardedWeakSubobligations ctx where
  localFold := r.localFold
  chartFaithful := g8WeakOffAxisRealization_chartFaithful ctx r
  tauWitness := r.tauWitness
  offAxisGuard := r.offAxisGuard

/-- The realization context yields the ordinary weak pullback subobligations. -/
def g8WeakOffAxisRealization_weakSubobligations
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (r : G8WeakOffAxisPullbackRealizationContext ctx) :
    G8WeakOffCriticalPullbackSubobligations ctx :=
  g8OffAxisGuarded_to_weakSubobligations ctx
    (g8WeakOffAxisRealization_guardedSubobligations ctx r)

/-- The realization context exposes the one-sided off-critical pullback. -/
theorem g8WeakOffAxisRealization_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (r : G8WeakOffAxisPullbackRealizationContext ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8WeakOffCritical_subobligations_yield_pullback ctx
    (g8WeakOffAxisRealization_weakSubobligations ctx r)

/-- Positive realization plus tau-side purity yields the local
    no-off-critical-zero conclusion. -/
theorem g8WeakOffAxisRealization_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (r : G8WeakOffAxisPullbackRealizationContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OffAxisGuard_noOffCriticalZeros ctx
    (g8WeakOffAxisRealization_guardedSubobligations ctx r)
    tauPurity

-- ============================================================
-- FAILURE WITNESSES
-- ============================================================

/-- An orthodox off-critical zero whose receiving-side shadow is not readable
    as off-axis. -/
structure G8UnreadableOffCriticalShadowWitness
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  z : ctx.test.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  notOffAxis : ¬ ShadowOffAxis (ctx.test.orthodoxShadow z)

/-- An unreadable off-critical shadow refutes local fold readability. -/
theorem g8UnreadableOffCriticalShadow_refutes_localFold
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (w : G8UnreadableOffCriticalShadowWitness ctx) :
    ¬ G8e1LocalFoldReadable ctx.test := by
  intro h
  exact w.notOffAxis (h w.z w.offCritical)

/-- An unreadable off-critical shadow refutes the positive realization package. -/
theorem g8UnreadableOffCriticalShadow_refutes_realization
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (w : G8UnreadableOffCriticalShadowWitness ctx) :
    ¬ Nonempty (G8WeakOffAxisPullbackRealizationContext ctx) := by
  intro h
  rcases h with ⟨r⟩
  exact g8UnreadableOffCriticalShadow_refutes_localFold ctx w r.localFold

/-- An off-axis shadow with no tau preimage under the declared relation. -/
structure G8NoTauPreimageForOffAxisShadowWitness
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (shadowTauRelated :
      ctx.test.base.orthodoxZero → ctx.test.base.tauWitness → Prop) where
  z : ctx.test.base.orthodoxZero
  offAxis : ShadowOffAxis (ctx.test.orthodoxShadow z)
  noTauPreimage :
    ∀ w : ctx.test.base.tauWitness, ¬ shadowTauRelated z w

/-- A no-preimage witness refutes off-axis preimage existence. -/
theorem g8NoTauPreimageForOffAxisShadow_refutes_preimageExistence
    (ctx : G8WeakOffCriticalPullbackTestContext)
    {shadowTauRelated :
      ctx.test.base.orthodoxZero → ctx.test.base.tauWitness → Prop}
    (w : G8NoTauPreimageForOffAxisShadowWitness ctx shadowTauRelated) :
    ¬ (∀ z : ctx.test.base.orthodoxZero,
        ShadowOffAxis (ctx.test.orthodoxShadow z) →
          ∃ tauW : ctx.test.base.tauWitness,
            shadowTauRelated z tauW) := by
  intro h
  obtain ⟨tauW, hRel⟩ := h w.z w.offAxis
  exact w.noTauPreimage tauW hRel

/-- A no-preimage witness refutes a realization context using that relation. -/
theorem g8NoTauPreimageForOffAxisShadow_refutes_realization
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (r : G8WeakOffAxisPullbackRealizationContext ctx)
    (w : G8NoTauPreimageForOffAxisShadowWitness ctx r.shadowTauRelated) :
    False :=
  g8NoTauPreimageForOffAxisShadow_refutes_preimageExistence
    ctx w r.offAxisHasTauPreimage

/-- A related tau preimage that remains B/C-balanced. -/
structure G8BalancedRelatedTauPreimageWitness
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (shadowTauRelated :
      ctx.test.base.orthodoxZero → ctx.test.base.tauWitness → Prop) where
  z : ctx.test.base.orthodoxZero
  w : ctx.test.base.tauWitness
  offAxis : ShadowOffAxis (ctx.test.orthodoxShadow z)
  related : shadowTauRelated z w
  balanced : BCBalanced (ctx.test.tauNormalForm w)

/-- A balanced related preimage refutes imbalance preservation. -/
theorem g8BalancedRelatedTauPreimage_refutes_imbalancePreservation
    (ctx : G8WeakOffCriticalPullbackTestContext)
    {shadowTauRelated :
      ctx.test.base.orthodoxZero → ctx.test.base.tauWitness → Prop}
    (w : G8BalancedRelatedTauPreimageWitness ctx shadowTauRelated) :
    ¬ (∀ (z : ctx.test.base.orthodoxZero)
        (tauW : ctx.test.base.tauWitness),
        ShadowOffAxis (ctx.test.orthodoxShadow z) →
          shadowTauRelated z tauW →
            TauCriticalImbalance (ctx.test.tauNormalForm tauW)) := by
  intro h
  have hImbalance := h w.z w.w w.offAxis w.related
  unfold TauCriticalImbalance at hImbalance
  exact hImbalance
    ((tauCriticalLocus_iff_bcBalanced (ctx.test.tauNormalForm w.w)).mpr
      w.balanced)

/-- A balanced related preimage refutes a realization context using that
    relation. -/
theorem g8BalancedRelatedTauPreimage_refutes_realization
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (r : G8WeakOffAxisPullbackRealizationContext ctx)
    (w : G8BalancedRelatedTauPreimageWitness ctx r.shadowTauRelated) :
    False :=
  g8BalancedRelatedTauPreimage_refutes_imbalancePreservation
    ctx w r.relatedPreimageCarriesTauImbalance

/-- A tau-native imbalance that is not realized as the declared tau witness. -/
structure G8TauImbalanceNotRealizedWitness
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  w : ctx.test.base.tauWitness
  imbalance : TauCriticalImbalance (ctx.test.tauNormalForm w)
  notWitness : ¬ TauOffCriticalWitness ctx.test.base w

/-- A non-realized imbalance refutes tau witness realization. -/
theorem g8TauImbalanceNotRealized_refutes_tauWitnessRealization
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (w : G8TauImbalanceNotRealizedWitness ctx) :
    ¬ G8e1TauImbalanceRealizesWitness ctx.test := by
  intro h
  exact w.notWitness (h w.w w.imbalance)

/-- A non-realized imbalance refutes a realization context. -/
theorem g8TauImbalanceNotRealized_refutes_realization
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (r : G8WeakOffAxisPullbackRealizationContext ctx)
    (w : G8TauImbalanceNotRealizedWitness ctx) :
    False :=
  g8TauImbalanceNotRealized_refutes_tauWitnessRealization
    ctx w r.tauWitness

/-- An off-axis chart-only ghost refutes the positive realization package. -/
theorem g8OffAxisChartOnlyGhost_refutes_realization
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (r : G8WeakOffAxisPullbackRealizationContext ctx)
    (w : G8OffAxisChartOnlyGhostWitness ctx.test) :
    False :=
  r.offAxisGuard ⟨w⟩

-- ============================================================
-- STAGE-AWARE HANDOFF
-- ============================================================

/-- Stage-aware positive realization package tied to the current off-axis
    corridor and weak completion lab. -/
structure G8StageAwareWeakOffAxisPullbackRealization
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) where
  lab : G8WeakOffAxisCompletionContext stageCorridor
  realization :
    G8WeakOffAxisPullbackRealizationContext
      stageCorridor.corridor.weakTest

/-- The stage-aware realization exposes its finite stage support. -/
def g8StageAwareWeakOffAxisRealization_stageSupport
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (r : G8StageAwareWeakOffAxisPullbackRealization stageCorridor) :
    G8PullbackStageSupport :=
  g8WeakOffAxisCompletionLab_stageSupport r.lab

/-- Stage-aware realization keeps finite data finite-only. -/
theorem g8StageAwareWeakOffAxisRealization_finiteOnly
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (r : G8StageAwareWeakOffAxisPullbackRealization stageCorridor) :
    finiteG8bContext.finiteOnly :=
  g8WeakOffAxisCompletionLab_finiteOnly r.lab

/-- Stage-aware realization carries no xi-divisor claim from finite stages. -/
theorem g8StageAwareWeakOffAxisRealization_noXiDivisorClaim
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (r : G8StageAwareWeakOffAxisPullbackRealization stageCorridor) :
    finiteG8bContext.noXiDivisorClaim :=
  g8WeakOffAxisCompletionLab_noXiDivisorClaim r.lab

/-- Stage-aware realization carries no analytic-completion claim from finite
    stages. -/
theorem g8StageAwareWeakOffAxisRealization_noAnalyticCompletionClaim
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (r : G8StageAwareWeakOffAxisPullbackRealization stageCorridor) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8WeakOffAxisCompletionLab_noAnalyticCompletionClaim r.lab

/-- Stage-aware realization exposes the local no-off-critical-zero conclusion
    already guarded by the corridor's tau purity. -/
theorem g8StageAwareWeakOffAxisRealization_noOffCriticalZeros
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (r : G8StageAwareWeakOffAxisPullbackRealization stageCorridor) :
    G8eNoOrthodoxOffCriticalZeros
      stageCorridor.corridor.weakTest.test.base :=
  g8WeakOffAxisRealization_noOffCriticalZeros
    stageCorridor.corridor.weakTest
    r.realization
    stageCorridor.corridor.tauPurity

/-- A fatal stage-indexed off-axis ghost remains the standing countermodel
    pressure against the stage-aware handoff. -/
theorem g8StageAwareWeakOffAxisRealization_fatalGhost_refutes
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (r : G8StageAwareWeakOffAxisPullbackRealization stageCorridor)
    (w : G8StageIndexedOffAxisGhostWitness r.lab) :
    False :=
  g8StageIndexedOffAxisGhost_refutes_stageAwareCorridor w

end Tau.BookIII.Bridge
