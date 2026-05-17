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
