import TauLib.BookIII.Bridge.G8PullbackRouteCertificate

/-!
# TauLib.BookIII.Bridge.G8PullbackAssembly

G8e.8 assembly layer for the RH bridge proof program.

The route-certificate module gives future work one explicit object containing
the G8e.4 off-critical pullback package, the G8c/G8d dependency chain, and
the red-team falsifier guards.  This module is the first consumer of that
certificate: it packages the conditional no-off-critical-zero conclusion
together with those same obligations.

This is intentionally still a context-local target.  It does not state the
classical Riemann Hypothesis in Mathlib terms, does not prove zero-divisor
transfer, and does not close G8.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CONDITIONAL TARGET
-- ============================================================

/-- Context-local conditional RH-facing target for the off-critical pullback
    route.

The first field is the local no-off-critical-zero conclusion.  The remaining
fields keep the proof-program obligations visible: any consumer of this target
can immediately inspect which G8c/G8d dependencies and falsifier guardrails
were needed to reach it. -/
structure G8ConditionalPullbackTarget
    (ctx : G8MasterSwitchContext) where
  noOrthodoxOffCriticalZeros :
    G8eNoOrthodoxOffCriticalZeros ctx.chart.faithfulness.test.base
  dependencies : G8PullbackDependencyChain ctx
  falsifierGuards : G8PullbackFalsifierGuards ctx

/-- Assemble the conditional target from an explicit route certificate. -/
def g8e4_assembleConditionalTarget
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    G8ConditionalPullbackTarget ctx where
  noOrthodoxOffCriticalZeros :=
    g8e4_noOffCriticalZeros_from_routeCertificate ctx cert
  dependencies := cert.dependencies
  falsifierGuards := cert.falsifierGuards

-- ============================================================
-- TARGET PROJECTIONS
-- ============================================================

/-- The assembled target exposes the local no-off-critical-zero conclusion. -/
theorem g8e4_target_noOffCriticalZeros
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    G8eNoOrthodoxOffCriticalZeros ctx.chart.faithfulness.test.base :=
  target.noOrthodoxOffCriticalZeros

/-- The assembled target still exposes analytic-completion uniqueness. -/
theorem g8e4_target_requires_completionUnique
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    tauTower_analyticCompletion_unique (g8e4ZetaChartContext ctx) :=
  target.dependencies.completionUnique

/-- The assembled target still exposes the G3 zeta bridge dependency. -/
theorem g8e4_target_requires_g3ZetaBridge
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    (g8e4ZetaChartContext ctx).g3ZetaBridge :=
  target.dependencies.g3ZetaBridge

/-- The assembled target still exposes the G4 analytic-continuation
    dependency. -/
theorem g8e4_target_requires_g4AnalyticContinuation
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    (g8e4ZetaChartContext ctx).g4AnalyticContinuation :=
  target.dependencies.g4AnalyticContinuation

/-- The assembled target still exposes the G5 operator-carrier dependency. -/
theorem g8e4_target_requires_g5OperatorCarrier
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    (g8e4ZetaChartContext ctx).g5OperatorCarrier :=
  target.dependencies.g5OperatorCarrier

/-- The assembled target still exposes the G6 determinant/O3 bridge
    dependency. -/
theorem g8e4_target_requires_g6O3DeterminantBridge
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    (g8e4ZetaChartContext ctx).g6O3DeterminantBridge :=
  target.dependencies.g6O3DeterminantBridge

/-- The assembled target still exposes the same-xi-divisor dependency. -/
theorem g8e4_target_requires_sameXiDivisor
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    (g8e4ZetaChartContext ctx).sameXiDivisor :=
  target.dependencies.sameXiDivisor

/-- The assembled target still exposes no-lost-zero transfer. -/
theorem g8e4_target_requires_noLost
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    (g8e4TransferContext ctx).noLostZeros :=
  target.dependencies.noLost

/-- The assembled target still exposes no-spurious-zero transfer. -/
theorem g8e4_target_requires_noSpurious
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    (g8e4TransferContext ctx).noSpuriousZeros :=
  target.dependencies.noSpurious

/-- The assembled target still exposes multiplicity preservation. -/
theorem g8e4_target_requires_multiplicityPreserved
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    (g8e4TransferContext ctx).multiplicityPreserved :=
  target.dependencies.multiplicityPreserved

/-- The assembled target carries the red-team falsifier guards. -/
theorem g8e4_target_carries_falsifierGuards
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    G8PullbackFalsifierGuards ctx :=
  target.falsifierGuards

/-- The assembled target rules out the non-unique-completion falsifier. -/
theorem g8e4_target_rulesOut_nonuniqueCompletion
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    G8cNoNonuniqueCompletion (g8e4CompletionContext ctx) :=
  target.falsifierGuards.noNonuniqueCompletion

/-- The assembled target rules out concrete lost-zero witnesses. -/
theorem g8e4_target_rulesOut_lostZero
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    G8dNoLostZeros (g8e4TransferContext ctx) :=
  target.falsifierGuards.noLostZero

/-- The assembled target rules out concrete spurious-zero witnesses. -/
theorem g8e4_target_rulesOut_spuriousZero
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    G8dNoSpuriousZeros (g8e4TransferContext ctx) :=
  target.falsifierGuards.noSpuriousZero

/-- The assembled target rules out concrete multiplicity-mismatch witnesses. -/
theorem g8e4_target_rulesOut_multiplicityMismatch
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    G8dNoMultiplicityMismatch (g8e4TransferContext ctx) :=
  target.falsifierGuards.noMultiplicityMismatch

/-- The assembled target rules out chart-only off-critical-zero witnesses. -/
theorem g8e4_target_rulesOut_chartOnly
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    G8e1NoChartOnlyOffCriticalZero (g8e4TestContext ctx) :=
  target.falsifierGuards.noChartOnly

/-- The assembled target rules out meromorphic-artifact falsifiers. -/
theorem g8e4_target_rulesOut_meromorphicArtifact
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    ¬ Nonempty (MeromorphicChartArtifactFalsifier ctx.chart) :=
  target.falsifierGuards.noMeromorphicArtifact

/-- The assembled target rules out no-preimage falsifiers. -/
theorem g8e4_target_rulesOut_noPreimage
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    G8e2NoTauPreimageFalsifier ctx.chart.faithfulness :=
  target.falsifierGuards.noNoPreimage

/-- The assembled target rules out balanced-preimage falsifiers. -/
theorem g8e4_target_rulesOut_balancedPreimage
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    G8e2NoBalancedPreimageFalsifier ctx.chart.faithfulness :=
  target.falsifierGuards.noBalancedPreimage

/-- A non-unique-completion witness refutes the assembled target. -/
theorem g8e4_nonuniqueCompletionWitness_refutes_conditionalTarget
    (ctx : G8MasterSwitchContext)
    (w : G8cNonuniqueCompletionWitness (g8e4CompletionContext ctx)) :
    ¬ G8ConditionalPullbackTarget ctx := by
  intro target
  exact target.falsifierGuards.noNonuniqueCompletion ⟨w⟩

/-- A lost-zero witness refutes the assembled target. -/
theorem g8e4_lostZeroWitness_refutes_conditionalTarget
    (ctx : G8MasterSwitchContext)
    (w : LostOrthodoxZeroWitness (g8e4TransferContext ctx)) :
    ¬ G8ConditionalPullbackTarget ctx := by
  intro target
  exact target.falsifierGuards.noLostZero ⟨w⟩

/-- A spurious-zero witness refutes the assembled target. -/
theorem g8e4_spuriousZeroWitness_refutes_conditionalTarget
    (ctx : G8MasterSwitchContext)
    (w : SpuriousTauZeroWitness (g8e4TransferContext ctx)) :
    ¬ G8ConditionalPullbackTarget ctx := by
  intro target
  exact target.falsifierGuards.noSpuriousZero ⟨w⟩

/-- A multiplicity-mismatch witness refutes the assembled target. -/
theorem g8e4_multiplicityMismatchWitness_refutes_conditionalTarget
    (ctx : G8MasterSwitchContext)
    (w : MultiplicityMismatchWitness (g8e4TransferContext ctx)) :
    ¬ G8ConditionalPullbackTarget ctx := by
  intro target
  exact target.falsifierGuards.noMultiplicityMismatch ⟨w⟩

/-- A chart-only witness refutes the assembled target. -/
theorem g8e4_chartOnlyWitness_refutes_conditionalTarget
    (ctx : G8MasterSwitchContext)
    (w : ChartOnlyOffCriticalZeroWitness (g8e4BaseContext ctx)) :
    ¬ G8ConditionalPullbackTarget ctx := by
  intro target
  exact target.falsifierGuards.noChartOnly ⟨w⟩

/-- A meromorphic-artifact witness refutes the assembled target. -/
theorem g8e4_meromorphicArtifactWitness_refutes_conditionalTarget
    (ctx : G8MasterSwitchContext)
    (w : MeromorphicChartArtifactFalsifier ctx.chart) :
    ¬ G8ConditionalPullbackTarget ctx := by
  intro target
  exact target.falsifierGuards.noMeromorphicArtifact ⟨w⟩

/-- A no-preimage witness refutes the assembled target. -/
theorem g8e4_noPreimageWitness_refutes_conditionalTarget
    (ctx : G8MasterSwitchContext)
    (w : NoTauPreimageForOffAxisShadowWitness ctx.chart.faithfulness) :
    ¬ G8ConditionalPullbackTarget ctx := by
  intro target
  exact target.falsifierGuards.noNoPreimage ⟨w⟩

/-- A balanced-preimage witness refutes the assembled target. -/
theorem g8e4_balancedPreimageWitness_refutes_conditionalTarget
    (ctx : G8MasterSwitchContext)
    (w : BalancedTauPreimageWitness ctx.chart.faithfulness) :
    ¬ G8ConditionalPullbackTarget ctx := by
  intro target
  exact target.falsifierGuards.noBalancedPreimage ⟨w⟩

-- ============================================================
-- CERTIFICATE-TO-TARGET CONVENIENCE THEOREM
-- ============================================================

/-- Direct certificate-to-target theorem for future theorem-facing modules.

This theorem packages the existing conditional route but adds no new
mathematical strength.  Its value is interface hygiene: future consumers can
take a `G8ConditionalPullbackTarget` instead of reaching into the lower-level
G8e.4 admissibility package. -/
theorem g8e4_conditionalTarget_from_routeCertificate
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    G8ConditionalPullbackTarget ctx :=
  g8e4_assembleConditionalTarget ctx cert

end Tau.BookIII.Bridge
