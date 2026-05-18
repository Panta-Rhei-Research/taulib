import TauLib.BookIII.Bridge.G8NonuniquenessFalsifier

/-!
# TauLib.BookIII.Bridge.G8PullbackRouteAudit

G8e.9 route-audit package for the RH bridge proof program.

The preceding modules expose the off-critical pullback corridor at several
layers: route certificate, assembled conditional target, dependency chain,
falsifier guards, and the non-uniqueness guard interface.  This module packages
those views into one compact audit object for the next proof wave.

The audit object is deliberately conservative.  It does not establish analytic
completion uniqueness, determinant correspondence, zero-divisor transfer, or a
classical RH theorem.  It only preserves the exact assumptions and red-team
failure modes that any future pullback proof must keep visible.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- ROUTE AUDIT
-- ============================================================

/-- Compact audit object for the current G8 off-critical pullback corridor.

The audit record is the handoff object for later proof work: it carries the
route certificate, the assembled local conclusion, the dependency chain, the
falsifier guards, and the non-uniqueness interface in one place. -/
structure G8PullbackRouteAudit
    (ctx : G8MasterSwitchContext) where
  routeCertificate : G8PullbackRouteCertificate ctx
  conditionalTarget : G8ConditionalPullbackTarget ctx
  dependencies : G8PullbackDependencyChain ctx
  falsifierGuards : G8PullbackFalsifierGuards ctx
  nonuniquenessInterface :
    G8NonuniquenessFalsifierInterface (g8e4CompletionContext ctx)
  noOrthodoxOffCriticalZeros :
    G8eNoOrthodoxOffCriticalZeros ctx.chart.faithfulness.test.base

/-- Build the route audit from the explicit G8e.4 route certificate. -/
def g8e4_routeAudit_from_certificate
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    G8PullbackRouteAudit ctx where
  routeCertificate := cert
  conditionalTarget := g8e4_assembleConditionalTarget ctx cert
  dependencies := cert.dependencies
  falsifierGuards := cert.falsifierGuards
  nonuniquenessInterface :=
    g8e4_nonuniquenessInterface_from_routeCertificate ctx cert
  noOrthodoxOffCriticalZeros :=
    g8e4_noOffCriticalZeros_from_routeCertificate ctx cert

-- ============================================================
-- DEPENDENCY PROJECTIONS
-- ============================================================

/-- The audit exposes the G3 zeta-bridge dependency. -/
theorem g8e4_routeAudit_requires_g3ZetaBridge
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx) :
    (g8e4ZetaChartContext ctx).g3ZetaBridge :=
  audit.dependencies.g3ZetaBridge

/-- The audit exposes the G4 analytic-continuation dependency. -/
theorem g8e4_routeAudit_requires_g4AnalyticContinuation
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx) :
    (g8e4ZetaChartContext ctx).g4AnalyticContinuation :=
  audit.dependencies.g4AnalyticContinuation

/-- The audit exposes the G5 operator-carrier dependency. -/
theorem g8e4_routeAudit_requires_g5OperatorCarrier
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx) :
    (g8e4ZetaChartContext ctx).g5OperatorCarrier :=
  audit.dependencies.g5OperatorCarrier

/-- The audit exposes the G6 determinant/O3 bridge dependency. -/
theorem g8e4_routeAudit_requires_g6O3DeterminantBridge
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx) :
    (g8e4ZetaChartContext ctx).g6O3DeterminantBridge :=
  audit.dependencies.g6O3DeterminantBridge

/-- The audit exposes analytic-completion uniqueness. -/
theorem g8e4_routeAudit_requires_completionUnique
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx) :
    tauTower_analyticCompletion_unique (g8e4ZetaChartContext ctx) :=
  audit.dependencies.completionUnique

/-- The audit exposes the same-xi-divisor dependency. -/
theorem g8e4_routeAudit_requires_sameXiDivisor
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx) :
    (g8e4ZetaChartContext ctx).sameXiDivisor :=
  audit.dependencies.sameXiDivisor

/-- The audit exposes no-lost-zero transfer. -/
theorem g8e4_routeAudit_requires_noLost
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx) :
    (g8e4TransferContext ctx).noLostZeros :=
  audit.dependencies.noLost

/-- The audit exposes no-spurious-zero transfer. -/
theorem g8e4_routeAudit_requires_noSpurious
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx) :
    (g8e4TransferContext ctx).noSpuriousZeros :=
  audit.dependencies.noSpurious

/-- The audit exposes multiplicity preservation. -/
theorem g8e4_routeAudit_requires_multiplicityPreserved
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx) :
    (g8e4TransferContext ctx).multiplicityPreserved :=
  audit.dependencies.multiplicityPreserved

/-- The audit exposes the no-two-completions guardrail. -/
theorem g8e4_routeAudit_requires_noTwoCompletionsGuard
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx) :
    noTwoCompletions_sameTauTower_differentDivisor
      (g8e4ZetaChartContext ctx) :=
  audit.nonuniquenessInterface.noTwoCompletionsGuard

/-- The audit exposes the non-unique-completion witness guard. -/
theorem g8e4_routeAudit_requires_noNonuniqueCompletion
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx) :
    G8cNoNonuniqueCompletion (g8e4CompletionContext ctx) :=
  audit.falsifierGuards.noNonuniqueCompletion

/-- The audit carries the falsifier guard suite. -/
theorem g8e4_routeAudit_carries_falsifierGuards
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx) :
    G8PullbackFalsifierGuards ctx :=
  audit.falsifierGuards

/-- The audit carries the non-uniqueness guard interface. -/
theorem g8e4_routeAudit_carries_nonuniquenessInterface
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx) :
    G8NonuniquenessFalsifierInterface (g8e4CompletionContext ctx) :=
  audit.nonuniquenessInterface

/-- The audit exposes the local no-off-critical-zero conclusion. -/
theorem g8e4_routeAudit_noOffCriticalZeros
    (ctx : G8MasterSwitchContext)
    (audit : G8PullbackRouteAudit ctx) :
    G8eNoOrthodoxOffCriticalZeros ctx.chart.faithfulness.test.base :=
  audit.noOrthodoxOffCriticalZeros

-- ============================================================
-- FALSIFIERS REFUTE AUDITS
-- ============================================================

/-- A non-unique-completion witness refutes a route audit. -/
theorem g8e4_nonuniqueCompletionWitness_refutes_routeAudit
    (ctx : G8MasterSwitchContext)
    (w : G8cNonuniqueCompletionWitness (g8e4CompletionContext ctx)) :
    ¬ G8PullbackRouteAudit ctx := by
  intro audit
  exact audit.falsifierGuards.noNonuniqueCompletion ⟨w⟩

/-- A same-tower, different-divisor witness refutes a route audit through the
    dedicated non-uniqueness interface. -/
theorem g8e4_sameTowerDifferentDivisor_refutes_routeAudit
    (ctx : G8MasterSwitchContext)
    (w : SameTauTowerDifferentDivisorFalsifier
      (g8e4CompletionContext ctx)) :
    ¬ G8PullbackRouteAudit ctx := by
  intro audit
  exact audit.nonuniquenessInterface.noSameTowerDifferentDivisor ⟨w⟩

/-- A lost-zero witness refutes a route audit. -/
theorem g8e4_lostZeroWitness_refutes_routeAudit
    (ctx : G8MasterSwitchContext)
    (w : LostOrthodoxZeroWitness (g8e4TransferContext ctx)) :
    ¬ G8PullbackRouteAudit ctx := by
  intro audit
  exact audit.falsifierGuards.noLostZero ⟨w⟩

/-- A spurious-zero witness refutes a route audit. -/
theorem g8e4_spuriousZeroWitness_refutes_routeAudit
    (ctx : G8MasterSwitchContext)
    (w : SpuriousTauZeroWitness (g8e4TransferContext ctx)) :
    ¬ G8PullbackRouteAudit ctx := by
  intro audit
  exact audit.falsifierGuards.noSpuriousZero ⟨w⟩

/-- A multiplicity-mismatch witness refutes a route audit. -/
theorem g8e4_multiplicityMismatchWitness_refutes_routeAudit
    (ctx : G8MasterSwitchContext)
    (w : MultiplicityMismatchWitness (g8e4TransferContext ctx)) :
    ¬ G8PullbackRouteAudit ctx := by
  intro audit
  exact audit.falsifierGuards.noMultiplicityMismatch ⟨w⟩

/-- A chart-only witness refutes a route audit. -/
theorem g8e4_chartOnlyWitness_refutes_routeAudit
    (ctx : G8MasterSwitchContext)
    (w : ChartOnlyOffCriticalZeroWitness (g8e4BaseContext ctx)) :
    ¬ G8PullbackRouteAudit ctx := by
  intro audit
  exact audit.falsifierGuards.noChartOnly ⟨w⟩

/-- A meromorphic-artifact witness refutes a route audit. -/
theorem g8e4_meromorphicArtifactWitness_refutes_routeAudit
    (ctx : G8MasterSwitchContext)
    (w : MeromorphicChartArtifactFalsifier ctx.chart) :
    ¬ G8PullbackRouteAudit ctx := by
  intro audit
  exact audit.falsifierGuards.noMeromorphicArtifact ⟨w⟩

/-- A no-preimage witness refutes a route audit. -/
theorem g8e4_noPreimageWitness_refutes_routeAudit
    (ctx : G8MasterSwitchContext)
    (w : NoTauPreimageForOffAxisShadowWitness ctx.chart.faithfulness) :
    ¬ G8PullbackRouteAudit ctx := by
  intro audit
  exact audit.falsifierGuards.noNoPreimage ⟨w⟩

/-- A balanced-preimage witness refutes a route audit. -/
theorem g8e4_balancedPreimageWitness_refutes_routeAudit
    (ctx : G8MasterSwitchContext)
    (w : BalancedTauPreimageWitness ctx.chart.faithfulness) :
    ¬ G8PullbackRouteAudit ctx := by
  intro audit
  exact audit.falsifierGuards.noBalancedPreimage ⟨w⟩

end Tau.BookIII.Bridge
