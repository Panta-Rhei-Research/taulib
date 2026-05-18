import TauLib.BookIII.Bridge.G8StageAwarePullbackAudit

/-!
# TauLib.BookIII.Bridge.G8StageAwarePullbackTarget

Stage-aware certificate and target packaging for the G8 off-critical pullback
corridor.

The previous stage-aware audit attaches the G8a/G8b finite substrate to the
route-audit object.  This module raises that finite substrate into the
certificate and conditional-target layer, so future G8 work can consume one
handoff object that carries route dependencies, falsifier guards, local
no-off-critical-zero conclusion, and finite-stage guardrails.

Everything here is projection and packaging.  It does not prove analytic
completion uniqueness, zero-divisor transfer, determinant correspondence, or
any classical RH statement.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- STAGE-AWARE CERTIFICATE
-- ============================================================

/-- Stage-aware route certificate.

This is the ordinary G8 pullback route certificate plus the finite stage
support package from G8a/G8b.  The support is deliberately finite substrate:
it carries visibility, projection compatibility, finite determinant
conventions, and finite-only guardrails, not zero-divisor transfer. -/
structure G8StageAwarePullbackRouteCertificate
    (ctx : G8MasterSwitchContext) where
  routeCertificate : G8PullbackRouteCertificate ctx
  stageSupport : G8PullbackStageSupport

/-- Build a stage-aware certificate from an ordinary route certificate and a
    chosen finite stage/factor family. -/
def g8StageAwarePullbackRouteCertificate
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx)
    (stage : Nat) (factor : Nat → Nat) :
    G8StageAwarePullbackRouteCertificate ctx where
  routeCertificate := cert
  stageSupport := g8PullbackStageSupport stage factor

/-- Turn a stage-aware certificate into the corresponding stage-aware route
    audit. -/
def g8StageAwareRouteAudit_from_certificate
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    G8StageAwarePullbackRouteAudit ctx where
  routeAudit := g8e4_routeAudit_from_certificate ctx cert.routeCertificate
  stageSupport := cert.stageSupport

-- ============================================================
-- CERTIFICATE PROJECTIONS
-- ============================================================

/-- The stage-aware certificate exposes its finite stage support. -/
def g8StageAwareCertificate_stageSupport
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    G8PullbackStageSupport :=
  cert.stageSupport

/-- The stage-aware certificate exposes its ordinary route certificate. -/
def g8StageAwareCertificate_routeCertificate
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    G8PullbackRouteCertificate ctx :=
  cert.routeCertificate

/-- The stage-aware certificate exposes the G3 zeta-bridge dependency. -/
theorem g8StageAwareCertificate_requires_g3ZetaBridge
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    (g8e4ZetaChartContext ctx).g3ZetaBridge :=
  g8e4_certificate_requires_g3ZetaBridge ctx cert.routeCertificate

/-- The stage-aware certificate exposes the G4 analytic-continuation
    dependency. -/
theorem g8StageAwareCertificate_requires_g4AnalyticContinuation
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    (g8e4ZetaChartContext ctx).g4AnalyticContinuation :=
  g8e4_certificate_requires_g4AnalyticContinuation ctx
    cert.routeCertificate

/-- The stage-aware certificate exposes the G5 operator-carrier dependency. -/
theorem g8StageAwareCertificate_requires_g5OperatorCarrier
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    (g8e4ZetaChartContext ctx).g5OperatorCarrier :=
  g8e4_certificate_requires_g5OperatorCarrier ctx cert.routeCertificate

/-- The stage-aware certificate exposes the G6 determinant/O3 dependency. -/
theorem g8StageAwareCertificate_requires_g6O3DeterminantBridge
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    (g8e4ZetaChartContext ctx).g6O3DeterminantBridge :=
  g8e4_certificate_requires_g6O3DeterminantBridge ctx
    cert.routeCertificate

/-- The stage-aware certificate exposes analytic-completion uniqueness as a
    named dependency. -/
theorem g8StageAwareCertificate_requires_completionUnique
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    tauTower_analyticCompletion_unique (g8e4ZetaChartContext ctx) :=
  g8e4_certificate_requires_completionUnique ctx cert.routeCertificate

/-- The stage-aware certificate exposes the same-xi-divisor dependency. -/
theorem g8StageAwareCertificate_requires_sameXiDivisor
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    (g8e4ZetaChartContext ctx).sameXiDivisor :=
  g8e4_certificate_requires_sameXiDivisor ctx cert.routeCertificate

/-- The stage-aware certificate exposes no-lost-zero transfer. -/
theorem g8StageAwareCertificate_requires_noLost
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    (g8e4TransferContext ctx).noLostZeros :=
  g8e4_certificate_requires_noLost ctx cert.routeCertificate

/-- The stage-aware certificate exposes no-spurious-zero transfer. -/
theorem g8StageAwareCertificate_requires_noSpurious
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    (g8e4TransferContext ctx).noSpuriousZeros :=
  g8e4_certificate_requires_noSpurious ctx cert.routeCertificate

/-- The stage-aware certificate exposes multiplicity preservation. -/
theorem g8StageAwareCertificate_requires_multiplicityPreserved
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    (g8e4TransferContext ctx).multiplicityPreserved :=
  g8e4_certificate_requires_multiplicityPreserved ctx
    cert.routeCertificate

/-- The stage-aware certificate yields the local no-off-critical-zero
    conclusion through its ordinary route certificate. -/
theorem g8StageAwareCertificate_noOffCriticalZeros
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    G8eNoOrthodoxOffCriticalZeros ctx.chart.faithfulness.test.base :=
  g8e4_noOffCriticalZeros_from_routeCertificate ctx cert.routeCertificate

/-- The certificate's finite stage is visible at its primorial stage. -/
theorem g8StageAwareCertificate_stageVisible
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    G8aFiniteSupportVisibleAt
      cert.stageSupport.approximant.support.modulus
      cert.stageSupport.approximant.support.stage :=
  g8StageSupport_visibleAtStage cert.stageSupport

/-- The certificate's finite stage carries projection compatibility. -/
theorem g8StageAwareCertificate_stageProjectionCompatible
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx)
    (x : Nat) :
    cert.stageSupport.approximant.support.residue
      (PrimorialStageProjection x
        cert.stageSupport.approximant.support.stage) =
      cert.stageSupport.approximant.support.residue x :=
  g8StageSupport_projectionCompatible cert.stageSupport x

/-- The certificate's finite support uses the primary finite determinant
    role. -/
theorem g8StageAwareCertificate_primaryFiniteDeterminant
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    cert.stageSupport.approximant.conventions.role =
      .primaryFiniteDeterminant :=
  g8StageSupport_primaryFiniteDeterminant cert.stageSupport

/-- The certificate's finite support uses the finite determinant class. -/
theorem g8StageAwareCertificate_finiteDeterminantClass
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    cert.stageSupport.approximant.conventions.determinantClass =
      .finite :=
  g8StageSupport_finiteDeterminantClass cert.stageSupport

/-- The certificate's finite support excludes the zero mode. -/
theorem g8StageAwareCertificate_zeroModeExcluded
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    cert.stageSupport.approximant.conventions.zeroModePolicy =
      .excluded :=
  g8StageSupport_zeroModeExcluded cert.stageSupport

/-- The certificate carries the finite-only G8b guardrails. -/
theorem g8StageAwareCertificate_finiteOnlyGuardrails
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    G8bFiniteOnlyGuardrails finiteG8bContext :=
  g8StageSupport_finiteOnlyGuardrails cert.stageSupport

/-- The certificate's finite stage is finite-only. -/
theorem g8StageAwareCertificate_finiteOnly
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    finiteG8bContext.finiteOnly :=
  g8StageSupport_finiteOnly cert.stageSupport

/-- The certificate's finite stage carries no xi-divisor claim. -/
theorem g8StageAwareCertificate_noXiDivisorClaim
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    finiteG8bContext.noXiDivisorClaim :=
  g8StageSupport_noXiDivisorClaim cert.stageSupport

/-- The certificate's finite stage carries no analytic-completion claim. -/
theorem g8StageAwareCertificate_noAnalyticCompletionClaim
    (ctx : G8MasterSwitchContext)
    (cert : G8StageAwarePullbackRouteCertificate ctx) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8StageSupport_noAnalyticCompletionClaim cert.stageSupport

-- ============================================================
-- STAGE-AWARE CONDITIONAL TARGET
-- ============================================================

/-- Stage-aware conditional pullback target.

This target is the high-level handoff object for later G8 work: it keeps the
ordinary conditional target, the route certificate, the stage-aware audit, and
the finite-stage support tied together. -/
structure G8StageAwareConditionalPullbackTarget
    (ctx : G8MasterSwitchContext) where
  routeCertificate : G8StageAwarePullbackRouteCertificate ctx
  stageAwareAudit : G8StageAwarePullbackRouteAudit ctx
  conditionalTarget : G8ConditionalPullbackTarget ctx

/-- Build a stage-aware conditional target from an ordinary route certificate
    and a chosen finite stage/factor family. -/
def g8StageAwareConditionalPullbackTarget
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx)
    (stage : Nat) (factor : Nat → Nat) :
    G8StageAwareConditionalPullbackTarget ctx :=
  let stageCert :=
    g8StageAwarePullbackRouteCertificate ctx cert stage factor
  {
    routeCertificate := stageCert
    stageAwareAudit :=
      g8StageAwareRouteAudit_from_certificate ctx stageCert
    conditionalTarget :=
      g8e4_assembleConditionalTarget ctx cert
  }

-- ============================================================
-- TARGET PROJECTIONS
-- ============================================================

/-- The target exposes its stage-aware audit. -/
def g8StageAwareTarget_audit
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    G8StageAwarePullbackRouteAudit ctx :=
  target.stageAwareAudit

/-- The target exposes its ordinary conditional target. -/
def g8StageAwareTarget_conditionalTarget
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    G8ConditionalPullbackTarget ctx :=
  target.conditionalTarget

/-- The target exposes the G3 zeta-bridge dependency. -/
theorem g8StageAwareTarget_requires_g3ZetaBridge
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    (g8e4ZetaChartContext ctx).g3ZetaBridge :=
  g8StageAwareAudit_requires_g3ZetaBridge ctx target.stageAwareAudit

/-- The target exposes the G4 analytic-continuation dependency. -/
theorem g8StageAwareTarget_requires_g4AnalyticContinuation
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    (g8e4ZetaChartContext ctx).g4AnalyticContinuation :=
  g8StageAwareAudit_requires_g4AnalyticContinuation ctx
    target.stageAwareAudit

/-- The target exposes the G5 operator-carrier dependency. -/
theorem g8StageAwareTarget_requires_g5OperatorCarrier
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    (g8e4ZetaChartContext ctx).g5OperatorCarrier :=
  g8StageAwareAudit_requires_g5OperatorCarrier ctx target.stageAwareAudit

/-- The target exposes the G6 determinant/O3 dependency. -/
theorem g8StageAwareTarget_requires_g6O3DeterminantBridge
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    (g8e4ZetaChartContext ctx).g6O3DeterminantBridge :=
  g8StageAwareAudit_requires_g6O3DeterminantBridge ctx
    target.stageAwareAudit

/-- The target exposes analytic-completion uniqueness as a named dependency. -/
theorem g8StageAwareTarget_requires_completionUnique
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    tauTower_analyticCompletion_unique (g8e4ZetaChartContext ctx) :=
  g8StageAwareAudit_requires_completionUnique ctx target.stageAwareAudit

/-- The target exposes the same-xi-divisor dependency. -/
theorem g8StageAwareTarget_requires_sameXiDivisor
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    (g8e4ZetaChartContext ctx).sameXiDivisor :=
  g8StageAwareAudit_requires_sameXiDivisor ctx target.stageAwareAudit

/-- The target exposes no-lost-zero transfer. -/
theorem g8StageAwareTarget_requires_noLost
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    (g8e4TransferContext ctx).noLostZeros :=
  g8StageAwareAudit_requires_noLost ctx target.stageAwareAudit

/-- The target exposes no-spurious-zero transfer. -/
theorem g8StageAwareTarget_requires_noSpurious
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    (g8e4TransferContext ctx).noSpuriousZeros :=
  g8StageAwareAudit_requires_noSpurious ctx target.stageAwareAudit

/-- The target exposes multiplicity preservation. -/
theorem g8StageAwareTarget_requires_multiplicityPreserved
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    (g8e4TransferContext ctx).multiplicityPreserved :=
  g8StageAwareAudit_requires_multiplicityPreserved ctx
    target.stageAwareAudit

/-- The target exposes the local no-off-critical-zero conclusion. -/
theorem g8StageAwareTarget_noOffCriticalZeros
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    G8eNoOrthodoxOffCriticalZeros ctx.chart.faithfulness.test.base :=
  g8StageAwareAudit_noOffCriticalZeros ctx target.stageAwareAudit

/-- The target's finite stage is visible at its primorial stage. -/
theorem g8StageAwareTarget_stageVisible
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    G8aFiniteSupportVisibleAt
      target.stageAwareAudit.stageSupport.approximant.support.modulus
      target.stageAwareAudit.stageSupport.approximant.support.stage :=
  g8StageAwareAudit_stageVisible ctx target.stageAwareAudit

/-- The target's finite stage carries projection compatibility. -/
theorem g8StageAwareTarget_stageProjectionCompatible
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx)
    (x : Nat) :
    target.stageAwareAudit.stageSupport.approximant.support.residue
      (PrimorialStageProjection x
        target.stageAwareAudit.stageSupport.approximant.support.stage) =
      target.stageAwareAudit.stageSupport.approximant.support.residue x :=
  g8StageAwareAudit_stageProjectionCompatible ctx target.stageAwareAudit x

/-- The target's finite stage uses the primary finite determinant role. -/
theorem g8StageAwareTarget_primaryFiniteDeterminant
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    target.stageAwareAudit.stageSupport.approximant.conventions.role =
      .primaryFiniteDeterminant :=
  g8StageAwareAudit_primaryFiniteDeterminant ctx target.stageAwareAudit

/-- The target's finite stage uses the finite determinant class. -/
theorem g8StageAwareTarget_finiteDeterminantClass
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    target.stageAwareAudit.stageSupport.approximant.conventions.determinantClass =
      .finite :=
  g8StageAwareAudit_finiteDeterminantClass ctx target.stageAwareAudit

/-- The target's finite stage excludes the zero mode. -/
theorem g8StageAwareTarget_zeroModeExcluded
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    target.stageAwareAudit.stageSupport.approximant.conventions.zeroModePolicy =
      .excluded :=
  g8StageAwareAudit_zeroModeExcluded ctx target.stageAwareAudit

/-- The target carries the finite-only G8b guardrails. -/
theorem g8StageAwareTarget_finiteOnlyGuardrails
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    G8bFiniteOnlyGuardrails finiteG8bContext :=
  g8StageAwareAudit_finiteOnlyGuardrails ctx target.stageAwareAudit

/-- The target's finite stage is finite-only. -/
theorem g8StageAwareTarget_finiteOnly
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    finiteG8bContext.finiteOnly :=
  g8StageAwareAudit_finiteOnly ctx target.stageAwareAudit

/-- The target's finite stage carries no xi-divisor claim. -/
theorem g8StageAwareTarget_noXiDivisorClaim
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    finiteG8bContext.noXiDivisorClaim :=
  g8StageAwareAudit_noXiDivisorClaim ctx target.stageAwareAudit

/-- The target's finite stage carries no analytic-completion claim. -/
theorem g8StageAwareTarget_noAnalyticCompletionClaim
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8StageAwareAudit_noAnalyticCompletionClaim ctx target.stageAwareAudit

-- ============================================================
-- FALSIFIER REFUTATIONS: CERTIFICATE LEVEL
-- ============================================================

/-- A non-unique-completion witness refutes any stage-aware certificate. -/
theorem g8StageAware_nonuniqueCompletionWitness_refutes_certificate
    (ctx : G8MasterSwitchContext)
    (w : G8cNonuniqueCompletionWitness (g8e4CompletionContext ctx)) :
    ¬ Nonempty (G8StageAwarePullbackRouteCertificate ctx) := by
  intro h
  rcases h with ⟨cert⟩
  exact g8e4_nonuniqueCompletionWitness_refutes_routeCertificate
    ctx w cert.routeCertificate

/-- A same-tower, different-divisor witness refutes any stage-aware
    certificate. -/
theorem g8StageAware_sameTowerDifferentDivisor_refutes_certificate
    (ctx : G8MasterSwitchContext)
    (w : SameTauTowerDifferentDivisorFalsifier
      (g8e4CompletionContext ctx)) :
    ¬ Nonempty (G8StageAwarePullbackRouteCertificate ctx) := by
  intro h
  rcases h with ⟨cert⟩
  exact g8e4_sameTowerDifferentDivisor_refutes_routeCertificate
    ctx w cert.routeCertificate

/-- A lost-zero witness refutes any stage-aware certificate. -/
theorem g8StageAware_lostZeroWitness_refutes_certificate
    (ctx : G8MasterSwitchContext)
    (w : LostOrthodoxZeroWitness (g8e4TransferContext ctx)) :
    ¬ Nonempty (G8StageAwarePullbackRouteCertificate ctx) := by
  intro h
  rcases h with ⟨cert⟩
  exact g8e4_lostZeroWitness_refutes_routeCertificate
    ctx w cert.routeCertificate

/-- A spurious-zero witness refutes any stage-aware certificate. -/
theorem g8StageAware_spuriousZeroWitness_refutes_certificate
    (ctx : G8MasterSwitchContext)
    (w : SpuriousTauZeroWitness (g8e4TransferContext ctx)) :
    ¬ Nonempty (G8StageAwarePullbackRouteCertificate ctx) := by
  intro h
  rcases h with ⟨cert⟩
  exact g8e4_spuriousZeroWitness_refutes_routeCertificate
    ctx w cert.routeCertificate

/-- A multiplicity-mismatch witness refutes any stage-aware certificate. -/
theorem g8StageAware_multiplicityMismatchWitness_refutes_certificate
    (ctx : G8MasterSwitchContext)
    (w : MultiplicityMismatchWitness (g8e4TransferContext ctx)) :
    ¬ Nonempty (G8StageAwarePullbackRouteCertificate ctx) := by
  intro h
  rcases h with ⟨cert⟩
  exact g8e4_multiplicityMismatchWitness_refutes_routeCertificate
    ctx w cert.routeCertificate

/-- A chart-only witness refutes any stage-aware certificate. -/
theorem g8StageAware_chartOnlyWitness_refutes_certificate
    (ctx : G8MasterSwitchContext)
    (w : ChartOnlyOffCriticalZeroWitness (g8e4BaseContext ctx)) :
    ¬ Nonempty (G8StageAwarePullbackRouteCertificate ctx) := by
  intro h
  rcases h with ⟨cert⟩
  exact g8e4_chartOnlyWitness_refutes_routeCertificate
    ctx w cert.routeCertificate

/-- A meromorphic-artifact witness refutes any stage-aware certificate. -/
theorem g8StageAware_meromorphicArtifactWitness_refutes_certificate
    (ctx : G8MasterSwitchContext)
    (w : MeromorphicChartArtifactFalsifier ctx.chart) :
    ¬ Nonempty (G8StageAwarePullbackRouteCertificate ctx) := by
  intro h
  rcases h with ⟨cert⟩
  exact g8e4_meromorphicArtifactWitness_refutes_routeCertificate
    ctx w cert.routeCertificate

/-- A no-preimage witness refutes any stage-aware certificate. -/
theorem g8StageAware_noPreimageWitness_refutes_certificate
    (ctx : G8MasterSwitchContext)
    (w : NoTauPreimageForOffAxisShadowWitness ctx.chart.faithfulness) :
    ¬ Nonempty (G8StageAwarePullbackRouteCertificate ctx) := by
  intro h
  rcases h with ⟨cert⟩
  exact g8e4_noPreimageWitness_refutes_routeCertificate
    ctx w cert.routeCertificate

/-- A balanced-preimage witness refutes any stage-aware certificate. -/
theorem g8StageAware_balancedPreimageWitness_refutes_certificate
    (ctx : G8MasterSwitchContext)
    (w : BalancedTauPreimageWitness ctx.chart.faithfulness) :
    ¬ Nonempty (G8StageAwarePullbackRouteCertificate ctx) := by
  intro h
  rcases h with ⟨cert⟩
  exact g8e4_balancedPreimageWitness_refutes_routeCertificate
    ctx w cert.routeCertificate

-- ============================================================
-- FALSIFIER REFUTATIONS: TARGET LEVEL
-- ============================================================

/-- A non-unique-completion witness refutes any stage-aware target. -/
theorem g8StageAware_nonuniqueCompletionWitness_refutes_target
    (ctx : G8MasterSwitchContext)
    (w : G8cNonuniqueCompletionWitness (g8e4CompletionContext ctx)) :
    ¬ Nonempty (G8StageAwareConditionalPullbackTarget ctx) := by
  intro h
  rcases h with ⟨target⟩
  exact g8StageAware_nonuniqueCompletionWitness_refutes_audit
    ctx w ⟨target.stageAwareAudit⟩

/-- A same-tower, different-divisor witness refutes any stage-aware target. -/
theorem g8StageAware_sameTowerDifferentDivisor_refutes_target
    (ctx : G8MasterSwitchContext)
    (w : SameTauTowerDifferentDivisorFalsifier
      (g8e4CompletionContext ctx)) :
    ¬ Nonempty (G8StageAwareConditionalPullbackTarget ctx) := by
  intro h
  rcases h with ⟨target⟩
  exact g8StageAware_sameTowerDifferentDivisor_refutes_audit
    ctx w ⟨target.stageAwareAudit⟩

/-- A lost-zero witness refutes any stage-aware target. -/
theorem g8StageAware_lostZeroWitness_refutes_target
    (ctx : G8MasterSwitchContext)
    (w : LostOrthodoxZeroWitness (g8e4TransferContext ctx)) :
    ¬ Nonempty (G8StageAwareConditionalPullbackTarget ctx) := by
  intro h
  rcases h with ⟨target⟩
  exact g8StageAware_lostZeroWitness_refutes_audit
    ctx w ⟨target.stageAwareAudit⟩

/-- A spurious-zero witness refutes any stage-aware target. -/
theorem g8StageAware_spuriousZeroWitness_refutes_target
    (ctx : G8MasterSwitchContext)
    (w : SpuriousTauZeroWitness (g8e4TransferContext ctx)) :
    ¬ Nonempty (G8StageAwareConditionalPullbackTarget ctx) := by
  intro h
  rcases h with ⟨target⟩
  exact g8StageAware_spuriousZeroWitness_refutes_audit
    ctx w ⟨target.stageAwareAudit⟩

/-- A multiplicity-mismatch witness refutes any stage-aware target. -/
theorem g8StageAware_multiplicityMismatchWitness_refutes_target
    (ctx : G8MasterSwitchContext)
    (w : MultiplicityMismatchWitness (g8e4TransferContext ctx)) :
    ¬ Nonempty (G8StageAwareConditionalPullbackTarget ctx) := by
  intro h
  rcases h with ⟨target⟩
  exact g8StageAware_multiplicityMismatchWitness_refutes_audit
    ctx w ⟨target.stageAwareAudit⟩

/-- A chart-only witness refutes any stage-aware target. -/
theorem g8StageAware_chartOnlyWitness_refutes_target
    (ctx : G8MasterSwitchContext)
    (w : ChartOnlyOffCriticalZeroWitness (g8e4BaseContext ctx)) :
    ¬ Nonempty (G8StageAwareConditionalPullbackTarget ctx) := by
  intro h
  rcases h with ⟨target⟩
  exact g8StageAware_chartOnlyWitness_refutes_audit
    ctx w ⟨target.stageAwareAudit⟩

/-- A meromorphic-artifact witness refutes any stage-aware target. -/
theorem g8StageAware_meromorphicArtifactWitness_refutes_target
    (ctx : G8MasterSwitchContext)
    (w : MeromorphicChartArtifactFalsifier ctx.chart) :
    ¬ Nonempty (G8StageAwareConditionalPullbackTarget ctx) := by
  intro h
  rcases h with ⟨target⟩
  exact g8StageAware_meromorphicArtifactWitness_refutes_audit
    ctx w ⟨target.stageAwareAudit⟩

/-- A no-preimage witness refutes any stage-aware target. -/
theorem g8StageAware_noPreimageWitness_refutes_target
    (ctx : G8MasterSwitchContext)
    (w : NoTauPreimageForOffAxisShadowWitness ctx.chart.faithfulness) :
    ¬ Nonempty (G8StageAwareConditionalPullbackTarget ctx) := by
  intro h
  rcases h with ⟨target⟩
  exact g8StageAware_noPreimageWitness_refutes_audit
    ctx w ⟨target.stageAwareAudit⟩

/-- A balanced-preimage witness refutes any stage-aware target. -/
theorem g8StageAware_balancedPreimageWitness_refutes_target
    (ctx : G8MasterSwitchContext)
    (w : BalancedTauPreimageWitness ctx.chart.faithfulness) :
    ¬ Nonempty (G8StageAwareConditionalPullbackTarget ctx) := by
  intro h
  rcases h with ⟨target⟩
  exact g8StageAware_balancedPreimageWitness_refutes_audit
    ctx w ⟨target.stageAwareAudit⟩

end Tau.BookIII.Bridge
