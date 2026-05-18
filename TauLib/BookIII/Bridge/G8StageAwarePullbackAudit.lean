import TauLib.BookIII.Bridge.G8PullbackRouteAudit
import TauLib.BookIII.Bridge.G8FiniteApproximants

/-!
# TauLib.BookIII.Bridge.G8StageAwarePullbackAudit

Stage-aware handoff package for the G8 off-critical pullback corridor.

`G8PullbackRouteAudit` packages the conditional pullback route, its upstream
bridge gates, and its falsifier guards.  This module adds the finite substrate:
the theorem-backed G8a arithmetic cofinality layer and the finite-only G8b
determinant-approximant layer.

The stage support is deliberately finite.  It supplies primorial-stage
visibility and projection compatibility, but it does not supply analytic
completion uniqueness, zero-divisor transfer, or any classical RH statement.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- STAGE SUPPORT
-- ============================================================

/-- Finite stage support attached to a G8 pullback route.

The object is proof-carrying: a consumer does not merely receive a staged
approximant, but also the G8a visibility/projection facts and the G8b finite
guardrails needed to keep the finite substrate below analytic-completion and
zero-divisor claims. -/
structure G8PullbackStageSupport where
  approximant : TauFiniteDetStageApprox
  supportVisible :
    G8aFiniteSupportVisibleAt
      approximant.support.modulus approximant.support.stage
  projectionCompatible :
    ∀ x : Nat,
      approximant.support.residue
        (PrimorialStageProjection x approximant.support.stage) =
        approximant.support.residue x
  primaryRole :
    approximant.conventions.role = .primaryFiniteDeterminant
  finiteDeterminantClass :
    approximant.conventions.determinantClass = .finite
  zeroModeExcluded :
    approximant.conventions.zeroModePolicy = .excluded
  finiteOnlyGuardrails : G8bFiniteOnlyGuardrails finiteG8bContext

/-- Build finite stage support from a primorial stage and diagonal factor
    family. -/
def g8PullbackStageSupport
    (stage : Nat) (factor : Nat → Nat) :
    G8PullbackStageSupport where
  approximant := mkTauFiniteDetStageApprox stage factor
  supportVisible :=
    tauFiniteDetStageApprox_support_visibleAtOwnStage
      (mkTauFiniteDetStageApprox stage factor)
  projectionCompatible :=
    tauFiniteDetStageApprox_support_projection_compatible
      (mkTauFiniteDetStageApprox stage factor)
  primaryRole := rfl
  finiteDeterminantClass := rfl
  zeroModeExcluded := rfl
  finiteOnlyGuardrails := finiteG8bContext_guardrails

-- ============================================================
-- STAGE SUPPORT PROJECTIONS
-- ============================================================

/-- The support capsule exposes a staged finite determinant approximant. -/
def g8StageSupport_stagedApproximant
    (S : G8PullbackStageSupport) :
    TauFiniteDetStageApprox :=
  S.approximant

/-- The stage support is visible at its declared primorial stage. -/
theorem g8StageSupport_visibleAtStage
    (S : G8PullbackStageSupport) :
    G8aFiniteSupportVisibleAt
      S.approximant.support.modulus S.approximant.support.stage :=
  S.supportVisible

/-- The stage support carries projection compatibility. -/
theorem g8StageSupport_projectionCompatible
    (S : G8PullbackStageSupport) (x : Nat) :
    S.approximant.support.residue
      (PrimorialStageProjection x S.approximant.support.stage) =
      S.approximant.support.residue x :=
  S.projectionCompatible x

/-- The support capsule uses the primary finite determinant role. -/
theorem g8StageSupport_primaryFiniteDeterminant
    (S : G8PullbackStageSupport) :
    S.approximant.conventions.role = .primaryFiniteDeterminant :=
  S.primaryRole

/-- The support capsule uses the finite determinant class. -/
theorem g8StageSupport_finiteDeterminantClass
    (S : G8PullbackStageSupport) :
    S.approximant.conventions.determinantClass = .finite :=
  S.finiteDeterminantClass

/-- The support capsule excludes the zero mode at the finite stage. -/
theorem g8StageSupport_zeroModeExcluded
    (S : G8PullbackStageSupport) :
    S.approximant.conventions.zeroModePolicy = .excluded :=
  S.zeroModeExcluded

/-- The support capsule carries the finite-only G8b guardrails. -/
theorem g8StageSupport_finiteOnlyGuardrails
    (S : G8PullbackStageSupport) :
    G8bFiniteOnlyGuardrails finiteG8bContext :=
  S.finiteOnlyGuardrails

/-- The finite stage support is finite-only. -/
theorem g8StageSupport_finiteOnly
    (S : G8PullbackStageSupport) :
    finiteG8bContext.finiteOnly :=
  S.finiteOnlyGuardrails.left

/-- The finite stage support carries no xi-divisor claim. -/
theorem g8StageSupport_noXiDivisorClaim
    (S : G8PullbackStageSupport) :
    finiteG8bContext.noXiDivisorClaim :=
  S.finiteOnlyGuardrails.right.left

/-- The finite stage support carries no analytic-completion claim. -/
theorem g8StageSupport_noAnalyticCompletionClaim
    (S : G8PullbackStageSupport) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  S.finiteOnlyGuardrails.right.right

-- ============================================================
-- STAGE-AWARE ROUTE AUDIT
-- ============================================================

/-- Stage-aware pullback audit.

This is the existing G8 pullback audit plus a finite substrate package.  It is
the intended handoff object for the next uniqueness or countermodel wave. -/
structure G8StageAwarePullbackRouteAudit
    (ctx : G8MasterSwitchContext) where
  routeAudit : G8PullbackRouteAudit ctx
  stageSupport : G8PullbackStageSupport

/-- Attach a finite stage support capsule to an existing route audit. -/
def g8StageAwarePullbackRouteAudit
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx)
    (stage : Nat) (factor : Nat → Nat) :
    G8StageAwarePullbackRouteAudit ctx where
  routeAudit := audit
  stageSupport := g8PullbackStageSupport stage factor

-- ============================================================
-- ROUTE DEPENDENCY PROJECTIONS
-- ============================================================

/-- The stage-aware audit exposes the G3 zeta-bridge dependency. -/
theorem g8StageAwareAudit_requires_g3ZetaBridge
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    (g8e4ZetaChartContext ctx).g3ZetaBridge :=
  g8e4_routeAudit_requires_g3ZetaBridge ctx audit.routeAudit

/-- The stage-aware audit exposes the G4 analytic-continuation dependency. -/
theorem g8StageAwareAudit_requires_g4AnalyticContinuation
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    (g8e4ZetaChartContext ctx).g4AnalyticContinuation :=
  g8e4_routeAudit_requires_g4AnalyticContinuation ctx audit.routeAudit

/-- The stage-aware audit exposes the G5 operator-carrier dependency. -/
theorem g8StageAwareAudit_requires_g5OperatorCarrier
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    (g8e4ZetaChartContext ctx).g5OperatorCarrier :=
  g8e4_routeAudit_requires_g5OperatorCarrier ctx audit.routeAudit

/-- The stage-aware audit exposes the G6 determinant/O3 bridge dependency. -/
theorem g8StageAwareAudit_requires_g6O3DeterminantBridge
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    (g8e4ZetaChartContext ctx).g6O3DeterminantBridge :=
  g8e4_routeAudit_requires_g6O3DeterminantBridge ctx audit.routeAudit

/-- The stage-aware audit exposes analytic-completion uniqueness. -/
theorem g8StageAwareAudit_requires_completionUnique
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    tauTower_analyticCompletion_unique (g8e4ZetaChartContext ctx) :=
  g8e4_routeAudit_requires_completionUnique ctx audit.routeAudit

/-- The stage-aware audit exposes the same-xi-divisor dependency. -/
theorem g8StageAwareAudit_requires_sameXiDivisor
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    (g8e4ZetaChartContext ctx).sameXiDivisor :=
  g8e4_routeAudit_requires_sameXiDivisor ctx audit.routeAudit

/-- The stage-aware audit exposes no-lost-zero transfer. -/
theorem g8StageAwareAudit_requires_noLost
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    (g8e4TransferContext ctx).noLostZeros :=
  g8e4_routeAudit_requires_noLost ctx audit.routeAudit

/-- The stage-aware audit exposes no-spurious-zero transfer. -/
theorem g8StageAwareAudit_requires_noSpurious
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    (g8e4TransferContext ctx).noSpuriousZeros :=
  g8e4_routeAudit_requires_noSpurious ctx audit.routeAudit

/-- The stage-aware audit exposes multiplicity preservation. -/
theorem g8StageAwareAudit_requires_multiplicityPreserved
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    (g8e4TransferContext ctx).multiplicityPreserved :=
  g8e4_routeAudit_requires_multiplicityPreserved ctx audit.routeAudit

/-- The stage-aware audit exposes the local no-off-critical-zero conclusion. -/
theorem g8StageAwareAudit_noOffCriticalZeros
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    G8eNoOrthodoxOffCriticalZeros ctx.chart.faithfulness.test.base :=
  g8e4_routeAudit_noOffCriticalZeros ctx audit.routeAudit

-- ============================================================
-- STAGE SUBSTRATE PROJECTIONS
-- ============================================================

/-- The stage-aware audit exposes its finite stage support. -/
def g8StageAwareAudit_stageSupport
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    G8PullbackStageSupport :=
  audit.stageSupport

/-- The stage-aware audit exposes G8a support visibility. -/
theorem g8StageAwareAudit_stageVisible
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    G8aFiniteSupportVisibleAt
      audit.stageSupport.approximant.support.modulus
      audit.stageSupport.approximant.support.stage :=
  g8StageSupport_visibleAtStage audit.stageSupport

/-- The stage-aware audit exposes G8a projection compatibility. -/
theorem g8StageAwareAudit_stageProjectionCompatible
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx)
    (x : Nat) :
    audit.stageSupport.approximant.support.residue
      (PrimorialStageProjection x
        audit.stageSupport.approximant.support.stage) =
      audit.stageSupport.approximant.support.residue x :=
  g8StageSupport_projectionCompatible audit.stageSupport x

/-- The stage-aware audit exposes the primary finite determinant role. -/
theorem g8StageAwareAudit_primaryFiniteDeterminant
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    audit.stageSupport.approximant.conventions.role =
      .primaryFiniteDeterminant :=
  g8StageSupport_primaryFiniteDeterminant audit.stageSupport

/-- The stage-aware audit exposes the finite determinant class. -/
theorem g8StageAwareAudit_finiteDeterminantClass
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    audit.stageSupport.approximant.conventions.determinantClass = .finite :=
  g8StageSupport_finiteDeterminantClass audit.stageSupport

/-- The stage-aware audit exposes zero-mode exclusion at the finite stage. -/
theorem g8StageAwareAudit_zeroModeExcluded
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    audit.stageSupport.approximant.conventions.zeroModePolicy = .excluded :=
  g8StageSupport_zeroModeExcluded audit.stageSupport

/-- The stage-aware audit exposes finite-only G8b guardrails. -/
theorem g8StageAwareAudit_finiteOnlyGuardrails
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    G8bFiniteOnlyGuardrails finiteG8bContext :=
  g8StageSupport_finiteOnlyGuardrails audit.stageSupport

/-- The stage-aware finite substrate is finite-only. -/
theorem g8StageAwareAudit_finiteOnly
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    finiteG8bContext.finiteOnly :=
  g8StageSupport_finiteOnly audit.stageSupport

/-- The stage-aware finite substrate carries no xi-divisor claim. -/
theorem g8StageAwareAudit_noXiDivisorClaim
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    finiteG8bContext.noXiDivisorClaim :=
  g8StageSupport_noXiDivisorClaim audit.stageSupport

/-- The stage-aware finite substrate carries no analytic-completion claim. -/
theorem g8StageAwareAudit_noAnalyticCompletionClaim
    (ctx : G8MasterSwitchContext)
    (audit : G8StageAwarePullbackRouteAudit ctx) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8StageSupport_noAnalyticCompletionClaim audit.stageSupport

-- ============================================================
-- FALSIFIERS REFUTE STAGE-AWARE AUDITS
-- ============================================================

/-- A non-unique-completion witness refutes a stage-aware audit. -/
theorem g8StageAware_nonuniqueCompletionWitness_refutes_audit
    (ctx : G8MasterSwitchContext)
    (w : G8cNonuniqueCompletionWitness (g8e4CompletionContext ctx)) :
    ¬ Nonempty (G8StageAwarePullbackRouteAudit ctx) := by
  intro h
  rcases h with ⟨audit⟩
  exact g8e4_nonuniqueCompletionWitness_refutes_routeAudit
    ctx w audit.routeAudit

/-- A same-tower, different-divisor witness refutes a stage-aware audit. -/
theorem g8StageAware_sameTowerDifferentDivisor_refutes_audit
    (ctx : G8MasterSwitchContext)
    (w : SameTauTowerDifferentDivisorFalsifier
      (g8e4CompletionContext ctx)) :
    ¬ Nonempty (G8StageAwarePullbackRouteAudit ctx) := by
  intro h
  rcases h with ⟨audit⟩
  exact g8e4_sameTowerDifferentDivisor_refutes_routeAudit
    ctx w audit.routeAudit

/-- A lost-zero witness refutes a stage-aware audit. -/
theorem g8StageAware_lostZeroWitness_refutes_audit
    (ctx : G8MasterSwitchContext)
    (w : LostOrthodoxZeroWitness (g8e4TransferContext ctx)) :
    ¬ Nonempty (G8StageAwarePullbackRouteAudit ctx) := by
  intro h
  rcases h with ⟨audit⟩
  exact g8e4_lostZeroWitness_refutes_routeAudit ctx w audit.routeAudit

/-- A spurious-zero witness refutes a stage-aware audit. -/
theorem g8StageAware_spuriousZeroWitness_refutes_audit
    (ctx : G8MasterSwitchContext)
    (w : SpuriousTauZeroWitness (g8e4TransferContext ctx)) :
    ¬ Nonempty (G8StageAwarePullbackRouteAudit ctx) := by
  intro h
  rcases h with ⟨audit⟩
  exact g8e4_spuriousZeroWitness_refutes_routeAudit ctx w audit.routeAudit

/-- A multiplicity-mismatch witness refutes a stage-aware audit. -/
theorem g8StageAware_multiplicityMismatchWitness_refutes_audit
    (ctx : G8MasterSwitchContext)
    (w : MultiplicityMismatchWitness (g8e4TransferContext ctx)) :
    ¬ Nonempty (G8StageAwarePullbackRouteAudit ctx) := by
  intro h
  rcases h with ⟨audit⟩
  exact g8e4_multiplicityMismatchWitness_refutes_routeAudit
    ctx w audit.routeAudit

/-- A chart-only witness refutes a stage-aware audit. -/
theorem g8StageAware_chartOnlyWitness_refutes_audit
    (ctx : G8MasterSwitchContext)
    (w : ChartOnlyOffCriticalZeroWitness (g8e4BaseContext ctx)) :
    ¬ Nonempty (G8StageAwarePullbackRouteAudit ctx) := by
  intro h
  rcases h with ⟨audit⟩
  exact g8e4_chartOnlyWitness_refutes_routeAudit ctx w audit.routeAudit

/-- A meromorphic-artifact witness refutes a stage-aware audit. -/
theorem g8StageAware_meromorphicArtifactWitness_refutes_audit
    (ctx : G8MasterSwitchContext)
    (w : MeromorphicChartArtifactFalsifier ctx.chart) :
    ¬ Nonempty (G8StageAwarePullbackRouteAudit ctx) := by
  intro h
  rcases h with ⟨audit⟩
  exact g8e4_meromorphicArtifactWitness_refutes_routeAudit
    ctx w audit.routeAudit

/-- A no-preimage witness refutes a stage-aware audit. -/
theorem g8StageAware_noPreimageWitness_refutes_audit
    (ctx : G8MasterSwitchContext)
    (w : NoTauPreimageForOffAxisShadowWitness ctx.chart.faithfulness) :
    ¬ Nonempty (G8StageAwarePullbackRouteAudit ctx) := by
  intro h
  rcases h with ⟨audit⟩
  exact g8e4_noPreimageWitness_refutes_routeAudit ctx w audit.routeAudit

/-- A balanced-preimage witness refutes a stage-aware audit. -/
theorem g8StageAware_balancedPreimageWitness_refutes_audit
    (ctx : G8MasterSwitchContext)
    (w : BalancedTauPreimageWitness ctx.chart.faithfulness) :
    ¬ Nonempty (G8StageAwarePullbackRouteAudit ctx) := by
  intro h
  rcases h with ⟨audit⟩
  exact g8e4_balancedPreimageWitness_refutes_routeAudit
    ctx w audit.routeAudit

end Tau.BookIII.Bridge
