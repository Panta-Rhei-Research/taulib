import TauLib.BookIII.Bridge.G8PullbackAssembly

/-!
# TauLib.BookIII.Bridge.G8NonuniquenessFalsifier

G8c/G8e non-uniqueness falsifier interface for the RH bridge proof program.

The standing red-team question for G8 is whether the same tau tower and finite
approximant data can admit two admissible receiving-side analytic completions
with different zero divisors.  If such a witness exists, the pullback route is
not merely incomplete: its zero-divisor-transfer assumptions are refuted.

This module makes that pressure executable.  It proves only refutation and
guardrail facts.  It does not prove analytic-completion uniqueness, construct
an analytic completion, or close any part of RH.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- STANDING FALSIFIER NAME
-- ============================================================

/-- The standing G8 non-uniqueness falsifier: two admissible completions with
    the same tau tower and finite approximants but different receiving
    divisors. -/
abbrev SameTauTowerDifferentDivisorFalsifier
    (ctx : G8cCompletionUniquenessContext) : Type 2 :=
  G8cNonuniqueCompletionWitness ctx

/-- Non-uniqueness pressure is the existence of a concrete same-tower,
    different-divisor witness. -/
def G8cNonuniquenessPressure
    (ctx : G8cCompletionUniquenessContext) : Prop :=
  Nonempty (SameTauTowerDifferentDivisorFalsifier ctx)

/-- A guard interface for the decisive G8c non-uniqueness test.

This record is intentionally small: it records exactly the facts needed to
rule out the standing falsifier while preserving the analytic-completion
uniqueness obligation exposed by the zeta-as-chart context. -/
structure G8NonuniquenessFalsifierInterface
    (ctx : G8cCompletionUniquenessContext) where
  completionUnique : tauTower_analyticCompletion_unique ctx.chart
  g3ZetaBridge : ctx.chart.g3ZetaBridge
  g4AnalyticContinuation : ctx.chart.g4AnalyticContinuation
  g5OperatorCarrier : ctx.chart.g5OperatorCarrier
  g6O3DeterminantBridge : ctx.chart.g6O3DeterminantBridge
  sameXiDivisor : ctx.chart.sameXiDivisor
  noLostZeros : ctx.chart.noLostZeros
  noSpuriousZeros : ctx.chart.noSpuriousZeros
  multiplicityPreserved : ctx.chart.multiplicityPreserved
  noTwoCompletionsGuard :
    noTwoCompletions_sameTauTower_differentDivisor ctx.chart
  noSameTowerDifferentDivisor : G8cNoNonuniqueCompletion ctx

/-- Build the non-uniqueness guard interface from G8c-admissible transfer. -/
def g8c_nonuniquenessInterface_from_transfer
    (ctx : G8cCompletionUniquenessContext)
    (h : G8cZeroDivisorTransferAdmissible ctx) :
    G8NonuniquenessFalsifierInterface ctx where
  completionUnique := g8c_transfer_requires_completionUnique ctx h
  g3ZetaBridge :=
    zeroDivisorClaimsAdmissible_g3ZetaBridge ctx.chart h.left
  g4AnalyticContinuation :=
    zeroDivisorClaimsAdmissible_g4AnalyticContinuation ctx.chart h.left
  g5OperatorCarrier :=
    zeroDivisorClaimsAdmissible_g5OperatorCarrier ctx.chart h.left
  g6O3DeterminantBridge :=
    zeroDivisorClaimsAdmissible_g6O3DeterminantBridge ctx.chart h.left
  sameXiDivisor :=
    zeroDivisorClaimsAdmissible_sameXiDivisor ctx.chart h.left
  noLostZeros :=
    zeroDivisorClaimsAdmissible_noLostZeros ctx.chart h.left
  noSpuriousZeros :=
    zeroDivisorClaimsAdmissible_noSpuriousZeros ctx.chart h.left
  multiplicityPreserved :=
    zeroDivisorClaimsAdmissible_multiplicityPreserved ctx.chart h.left
  noTwoCompletionsGuard :=
    zeroDivisorClaimsAdmissible_noTwoCompletionsGuard ctx.chart h.left
  noSameTowerDifferentDivisor :=
    g8c_transfer_requires_noNonuniqueCompletion ctx h

-- ============================================================
-- FALSIFIER REFUTATIONS AT EACH LEVEL
-- ============================================================

/-- A same-tower, different-divisor witness refutes G8c transfer
    admissibility. -/
theorem g8c_nonuniquenessPressure_refutes_transfer
    (ctx : G8cCompletionUniquenessContext)
    (p : G8cNonuniquenessPressure ctx) :
    ¬ G8cZeroDivisorTransferAdmissible ctx := by
  intro h
  exact (g8c_transfer_requires_noNonuniqueCompletion ctx h) p

/-- A concrete same-tower, different-divisor witness refutes G8c transfer
    admissibility. -/
theorem g8c_sameTowerDifferentDivisor_refutes_transfer
    (ctx : G8cCompletionUniquenessContext)
    (w : SameTauTowerDifferentDivisorFalsifier ctx) :
    ¬ G8cZeroDivisorTransferAdmissible ctx :=
  g8c_nonuniquenessPressure_refutes_transfer ctx ⟨w⟩

/-- A same-tower, different-divisor witness refutes the guard interface
    itself. -/
theorem g8c_sameTowerDifferentDivisor_refutes_interface
    (ctx : G8cCompletionUniquenessContext)
    (w : SameTauTowerDifferentDivisorFalsifier ctx) :
    ¬ G8NonuniquenessFalsifierInterface ctx := by
  intro h
  exact h.noSameTowerDifferentDivisor ⟨w⟩

/-- The same witness refutes G8d transfer whenever it appears in the G8c
    completion context carried by the G8d context. -/
theorem g8d_sameTowerDifferentDivisor_refutes_transfer
    (ctx : G8dZeroDivisorTransferContext)
    (w : SameTauTowerDifferentDivisorFalsifier ctx.completion) :
    ¬ G8dZeroDivisorTransferAdmissible ctx := by
  intro h
  exact g8c_sameTowerDifferentDivisor_refutes_transfer
    ctx.completion w (g8d_transfer_requires_g8c ctx h)

/-- At the G8e.4 master-switch layer, a same-tower, different-divisor witness
    refutes the route certificate. -/
theorem g8e4_sameTowerDifferentDivisor_refutes_routeCertificate
    (ctx : G8MasterSwitchContext)
    (w : SameTauTowerDifferentDivisorFalsifier
      (g8e4CompletionContext ctx)) :
    ¬ G8PullbackRouteCertificate ctx := by
  intro cert
  exact cert.dependencies.noNonuniqueCompletion ⟨w⟩

/-- The same witness also refutes the assembled conditional pullback target. -/
theorem g8e4_sameTowerDifferentDivisor_refutes_conditionalTarget
    (ctx : G8MasterSwitchContext)
    (w : SameTauTowerDifferentDivisorFalsifier
      (g8e4CompletionContext ctx)) :
    ¬ G8ConditionalPullbackTarget ctx := by
  intro target
  exact target.dependencies.noNonuniqueCompletion ⟨w⟩

-- ============================================================
-- CERTIFICATE GUARD EXTRACTION
-- ============================================================

/-- A route certificate carries the decisive non-uniqueness guard interface. -/
def g8e4_nonuniquenessInterface_from_routeCertificate
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    G8NonuniquenessFalsifierInterface (g8e4CompletionContext ctx) where
  completionUnique := cert.dependencies.completionUnique
  g3ZetaBridge := cert.dependencies.g3ZetaBridge
  g4AnalyticContinuation := cert.dependencies.g4AnalyticContinuation
  g5OperatorCarrier := cert.dependencies.g5OperatorCarrier
  g6O3DeterminantBridge := cert.dependencies.g6O3DeterminantBridge
  sameXiDivisor := cert.dependencies.sameXiDivisor
  noLostZeros :=
    zeroDivisorClaimsAdmissible_noLostZeros
      (g8e4ZetaChartContext ctx)
      cert.dependencies.zeroDivisorClaims
  noSpuriousZeros :=
    zeroDivisorClaimsAdmissible_noSpuriousZeros
      (g8e4ZetaChartContext ctx)
      cert.dependencies.zeroDivisorClaims
  multiplicityPreserved :=
    zeroDivisorClaimsAdmissible_multiplicityPreserved
      (g8e4ZetaChartContext ctx)
      cert.dependencies.zeroDivisorClaims
  noTwoCompletionsGuard :=
    zeroDivisorClaimsAdmissible_noTwoCompletionsGuard
      (g8e4ZetaChartContext ctx)
      cert.dependencies.zeroDivisorClaims
  noSameTowerDifferentDivisor := cert.dependencies.noNonuniqueCompletion

/-- An assembled target also carries the decisive non-uniqueness guard
    interface. -/
def g8e4_nonuniquenessInterface_from_target
    (ctx : G8MasterSwitchContext)
    (target : G8ConditionalPullbackTarget ctx) :
    G8NonuniquenessFalsifierInterface (g8e4CompletionContext ctx) where
  completionUnique := target.dependencies.completionUnique
  g3ZetaBridge := target.dependencies.g3ZetaBridge
  g4AnalyticContinuation := target.dependencies.g4AnalyticContinuation
  g5OperatorCarrier := target.dependencies.g5OperatorCarrier
  g6O3DeterminantBridge := target.dependencies.g6O3DeterminantBridge
  sameXiDivisor := target.dependencies.sameXiDivisor
  noLostZeros :=
    zeroDivisorClaimsAdmissible_noLostZeros
      (g8e4ZetaChartContext ctx)
      target.dependencies.zeroDivisorClaims
  noSpuriousZeros :=
    zeroDivisorClaimsAdmissible_noSpuriousZeros
      (g8e4ZetaChartContext ctx)
      target.dependencies.zeroDivisorClaims
  multiplicityPreserved :=
    zeroDivisorClaimsAdmissible_multiplicityPreserved
      (g8e4ZetaChartContext ctx)
      target.dependencies.zeroDivisorClaims
  noTwoCompletionsGuard :=
    zeroDivisorClaimsAdmissible_noTwoCompletionsGuard
      (g8e4ZetaChartContext ctx)
      target.dependencies.zeroDivisorClaims
  noSameTowerDifferentDivisor := target.dependencies.noNonuniqueCompletion

end Tau.BookIII.Bridge
