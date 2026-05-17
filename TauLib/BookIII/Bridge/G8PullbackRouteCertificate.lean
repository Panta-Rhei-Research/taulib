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
