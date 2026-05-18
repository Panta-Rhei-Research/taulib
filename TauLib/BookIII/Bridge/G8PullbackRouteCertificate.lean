import TauLib.BookIII.Bridge.G8PullbackFalsifierPressure

/-!
# TauLib.BookIII.Bridge.G8PullbackRouteCertificate

G8e.7 route-certificate packaging for the RH bridge proof program.

The previous two modules expose what an admissible off-critical pullback route
depends on and which red-team falsifiers would refute it.  This module packages
those views into one explicit certificate.  It is deliberately conservative:
the certificate contains the original hypothesis-driven admissibility package
and its derived dependency/falsifier views.

Nothing here proves analytic completion uniqueness, zero-divisor transfer, O3,
or the Riemann Hypothesis.  The point is to give downstream work a single
interface that cannot hide the G8c/G8d/G8e obligations.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- ROUTE CERTIFICATE
-- ============================================================

/-- A fully explicit certificate for the current G8e.4 off-critical pullback
    route.

The `admissible` field is the hypothesis-driven route package.  The remaining
fields are derived views that make the analytic-completion, zero-divisor, and
red-team guardrail commitments visible to future consumers. -/
structure G8PullbackRouteCertificate
    (ctx : G8MasterSwitchContext) where
  admissible : G8e4ContradictionTestAdmissible ctx
  dependencies : G8PullbackDependencyChain ctx
  falsifierGuards : G8PullbackFalsifierGuards ctx

/-- Build the explicit route certificate from a G8e.4 admissible route. -/
def g8e4_routeCertificate
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    G8PullbackRouteCertificate ctx where
  admissible := h
  dependencies := g8e4_dependencyChain ctx h
  falsifierGuards := g8e4_falsifierGuards ctx h

-- ============================================================
-- CERTIFICATE PROJECTIONS
-- ============================================================

/-- A certificate still exposes analytic-completion uniqueness as a named
    dependency, not as hidden background. -/
theorem g8e4_certificate_requires_completionUnique
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    tauTower_analyticCompletion_unique (g8e4ZetaChartContext ctx) :=
  cert.dependencies.completionUnique

/-- A certificate still exposes the G3 zeta bridge dependency. -/
theorem g8e4_certificate_requires_g3ZetaBridge
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    (g8e4ZetaChartContext ctx).g3ZetaBridge :=
  cert.dependencies.g3ZetaBridge

/-- A certificate still exposes the G4 analytic-continuation dependency. -/
theorem g8e4_certificate_requires_g4AnalyticContinuation
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    (g8e4ZetaChartContext ctx).g4AnalyticContinuation :=
  cert.dependencies.g4AnalyticContinuation

/-- A certificate still exposes the G5 operator-carrier dependency. -/
theorem g8e4_certificate_requires_g5OperatorCarrier
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    (g8e4ZetaChartContext ctx).g5OperatorCarrier :=
  cert.dependencies.g5OperatorCarrier

/-- A certificate still exposes the G6 determinant/O3 bridge dependency. -/
theorem g8e4_certificate_requires_g6O3DeterminantBridge
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    (g8e4ZetaChartContext ctx).g6O3DeterminantBridge :=
  cert.dependencies.g6O3DeterminantBridge

/-- A certificate still exposes the same-xi-divisor dependency. -/
theorem g8e4_certificate_requires_sameXiDivisor
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    (g8e4ZetaChartContext ctx).sameXiDivisor :=
  cert.dependencies.sameXiDivisor

/-- A certificate still exposes no-lost-zero transfer. -/
theorem g8e4_certificate_requires_noLost
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    (g8e4TransferContext ctx).noLostZeros :=
  cert.dependencies.noLost

/-- A certificate still exposes no-spurious-zero transfer. -/
theorem g8e4_certificate_requires_noSpurious
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    (g8e4TransferContext ctx).noSpuriousZeros :=
  cert.dependencies.noSpurious

/-- A certificate still exposes multiplicity preservation. -/
theorem g8e4_certificate_requires_multiplicityPreserved
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    (g8e4TransferContext ctx).multiplicityPreserved :=
  cert.dependencies.multiplicityPreserved

/-- A certificate carries the concrete red-team falsifier guards. -/
theorem g8e4_certificate_carries_falsifierGuards
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    G8PullbackFalsifierGuards ctx :=
  cert.falsifierGuards

/-- A certificate rules out the non-unique-completion falsifier. -/
theorem g8e4_certificate_rulesOut_nonuniqueCompletion
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    G8cNoNonuniqueCompletion (g8e4CompletionContext ctx) :=
  cert.falsifierGuards.noNonuniqueCompletion

/-- A certificate rules out concrete lost-zero witnesses. -/
theorem g8e4_certificate_rulesOut_lostZero
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    G8dNoLostZeros (g8e4TransferContext ctx) :=
  cert.falsifierGuards.noLostZero

/-- A certificate rules out concrete spurious-zero witnesses. -/
theorem g8e4_certificate_rulesOut_spuriousZero
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    G8dNoSpuriousZeros (g8e4TransferContext ctx) :=
  cert.falsifierGuards.noSpuriousZero

/-- A certificate rules out concrete multiplicity-mismatch witnesses. -/
theorem g8e4_certificate_rulesOut_multiplicityMismatch
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    G8dNoMultiplicityMismatch (g8e4TransferContext ctx) :=
  cert.falsifierGuards.noMultiplicityMismatch

/-- A certificate rules out chart-only off-critical-zero witnesses. -/
theorem g8e4_certificate_rulesOut_chartOnly
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    G8e1NoChartOnlyOffCriticalZero (g8e4TestContext ctx) :=
  cert.falsifierGuards.noChartOnly

/-- A certificate rules out meromorphic-artifact falsifiers. -/
theorem g8e4_certificate_rulesOut_meromorphicArtifact
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    ¬ Nonempty (MeromorphicChartArtifactFalsifier ctx.chart) :=
  cert.falsifierGuards.noMeromorphicArtifact

/-- A certificate rules out no-preimage falsifiers. -/
theorem g8e4_certificate_rulesOut_noPreimage
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    G8e2NoTauPreimageFalsifier ctx.chart.faithfulness :=
  cert.falsifierGuards.noNoPreimage

/-- A certificate rules out balanced-preimage falsifiers. -/
theorem g8e4_certificate_rulesOut_balancedPreimage
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    G8e2NoBalancedPreimageFalsifier ctx.chart.faithfulness :=
  cert.falsifierGuards.noBalancedPreimage

/-- A non-unique-completion witness refutes the route certificate. -/
theorem g8e4_nonuniqueCompletionWitness_refutes_routeCertificate
    (ctx : G8MasterSwitchContext)
    (w : G8cNonuniqueCompletionWitness (g8e4CompletionContext ctx)) :
    ¬ G8PullbackRouteCertificate ctx := by
  intro cert
  exact cert.falsifierGuards.noNonuniqueCompletion ⟨w⟩

/-- A lost-zero witness refutes the route certificate. -/
theorem g8e4_lostZeroWitness_refutes_routeCertificate
    (ctx : G8MasterSwitchContext)
    (w : LostOrthodoxZeroWitness (g8e4TransferContext ctx)) :
    ¬ G8PullbackRouteCertificate ctx := by
  intro cert
  exact cert.falsifierGuards.noLostZero ⟨w⟩

/-- A spurious-zero witness refutes the route certificate. -/
theorem g8e4_spuriousZeroWitness_refutes_routeCertificate
    (ctx : G8MasterSwitchContext)
    (w : SpuriousTauZeroWitness (g8e4TransferContext ctx)) :
    ¬ G8PullbackRouteCertificate ctx := by
  intro cert
  exact cert.falsifierGuards.noSpuriousZero ⟨w⟩

/-- A multiplicity-mismatch witness refutes the route certificate. -/
theorem g8e4_multiplicityMismatchWitness_refutes_routeCertificate
    (ctx : G8MasterSwitchContext)
    (w : MultiplicityMismatchWitness (g8e4TransferContext ctx)) :
    ¬ G8PullbackRouteCertificate ctx := by
  intro cert
  exact cert.falsifierGuards.noMultiplicityMismatch ⟨w⟩

/-- A chart-only witness refutes the route certificate. -/
theorem g8e4_chartOnlyWitness_refutes_routeCertificate
    (ctx : G8MasterSwitchContext)
    (w : ChartOnlyOffCriticalZeroWitness (g8e4BaseContext ctx)) :
    ¬ G8PullbackRouteCertificate ctx := by
  intro cert
  exact cert.falsifierGuards.noChartOnly ⟨w⟩

/-- A meromorphic-artifact witness refutes the route certificate. -/
theorem g8e4_meromorphicArtifactWitness_refutes_routeCertificate
    (ctx : G8MasterSwitchContext)
    (w : MeromorphicChartArtifactFalsifier ctx.chart) :
    ¬ G8PullbackRouteCertificate ctx := by
  intro cert
  exact cert.falsifierGuards.noMeromorphicArtifact ⟨w⟩

/-- A no-preimage witness refutes the route certificate. -/
theorem g8e4_noPreimageWitness_refutes_routeCertificate
    (ctx : G8MasterSwitchContext)
    (w : NoTauPreimageForOffAxisShadowWitness ctx.chart.faithfulness) :
    ¬ G8PullbackRouteCertificate ctx := by
  intro cert
  exact cert.falsifierGuards.noNoPreimage ⟨w⟩

/-- A balanced-preimage witness refutes the route certificate. -/
theorem g8e4_balancedPreimageWitness_refutes_routeCertificate
    (ctx : G8MasterSwitchContext)
    (w : BalancedTauPreimageWitness ctx.chart.faithfulness) :
    ¬ G8PullbackRouteCertificate ctx := by
  intro cert
  exact cert.falsifierGuards.noBalancedPreimage ⟨w⟩

-- ============================================================
-- CONDITIONAL CONCLUSION
-- ============================================================

/-- If a future proof supplies the full explicit certificate, the existing
    G8e.4 conditional conclusion may be consumed through that certificate.

This is still entirely conditional: the certificate itself contains the named
G3/G4/G5/G6/G8 obligations through the underlying contexts. -/
theorem g8e4_noOffCriticalZeros_from_routeCertificate
    (ctx : G8MasterSwitchContext)
    (cert : G8PullbackRouteCertificate ctx) :
    G8eNoOrthodoxOffCriticalZeros ctx.chart.faithfulness.test.base :=
  g8e4_noOffCriticalZeros_from_testAdmissible ctx cert.admissible

end Tau.BookIII.Bridge
