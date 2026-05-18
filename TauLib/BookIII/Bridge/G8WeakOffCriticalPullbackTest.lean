import TauLib.BookIII.Bridge.G8OffCriticalPullbackTest
import TauLib.BookIII.Bridge.G8OffCriticalExclusionTransfer

/-!
# TauLib.BookIII.Bridge.G8WeakOffCriticalPullbackTest

Weak G8 off-critical pullback test.

The older `G8OffCriticalPullbackTest` deliberately keeps the full G8d
zero-divisor-transfer stack visible.  This module records the weaker route
needed for off-critical exclusion only: local fold readability, off-axis chart
faithfulness, tau witness realization, and the chart-only guard.

The resulting theorem is local and conditional.  It does not prove analytic
completion uniqueness, full zero-divisor transfer, O3, or any classical RH
statement.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- WEAK TEST CONTEXT
-- ============================================================

/-- Weak off-critical pullback test context.

The underlying `test` supplies the orthodox shadow map and tau normal form
from the existing G8e.1 harness.  Finite-stage guardrails remain attached, but
the full G8d transfer stack is not part of this weak test. -/
structure G8WeakOffCriticalPullbackTestContext where
  test : OffCriticalPullbackTestContext
  finiteGuardrails : G8bFiniteOnlyGuardrails finiteG8bContext :=
    finiteG8bContext_guardrails
  status : G8OffCriticalExclusionStatus := .openObligation

/-- Weak subobligations for off-critical exclusion.

This is the G8e.1 package with the full `transfer` field removed.  It is
sufficient for the one-sided off-critical pullback used by
`G8OffCriticalExclusionTransfer`, but it does not license any full divisor
equivalence claim. -/
structure G8WeakOffCriticalPullbackSubobligations
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  localFold : G8e1LocalFoldReadable ctx.test
  chartFaithful : G8e1ChartFaithfulToTauImbalance ctx.test
  tauWitness : G8e1TauImbalanceRealizesWitness ctx.test
  noChartOnly : G8e1NoChartOnlyOffCriticalZero ctx.test

/-- Weak subobligations imply the one-sided pullback obligation. -/
theorem g8WeakOffCritical_subobligations_yield_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (h : G8WeakOffCriticalPullbackSubobligations ctx) :
    G8eOffCriticalPullback ctx.test.base := by
  intro z hz
  have hShadow : ShadowOffAxis (ctx.test.orthodoxShadow z) :=
    h.localFold z hz
  obtain ⟨w, hImbalance⟩ := h.chartFaithful z hShadow
  exact ⟨w, h.tauWitness w hImbalance⟩

/-- Weak subobligations expose the chart-only guard. -/
theorem g8WeakOffCritical_subobligations_noChartOnly
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (h : G8WeakOffCriticalPullbackSubobligations ctx) :
    G8e1NoChartOnlyOffCriticalZero ctx.test :=
  h.noChartOnly

/-- Weak subobligations keep finite-stage support below orthodox zero-divisor
    claims. -/
theorem g8WeakOffCritical_noXiDivisorClaim_from_finiteStage
    (ctx : G8WeakOffCriticalPullbackTestContext) :
    finiteG8bContext.noXiDivisorClaim :=
  ctx.finiteGuardrails.right.left

/-- Weak subobligations keep finite-stage support below analytic-completion
    claims. -/
theorem g8WeakOffCritical_noAnalyticCompletionClaim_from_finiteStage
    (ctx : G8WeakOffCriticalPullbackTestContext) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  ctx.finiteGuardrails.right.right

-- ============================================================
-- HANDOFF TO OFF-CRITICAL EXCLUSION TRANSFER
-- ============================================================

/-- Build the weak off-critical exclusion-transfer context from weak
    subobligations and tau-side purity. -/
def g8WeakOffCritical_to_exclusionTransferContext
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (h : G8WeakOffCriticalPullbackSubobligations ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8OffCriticalExclusionTransferContext where
  base := ctx.test.base
  offCriticalChartAdmissible :=
    G8e1NoChartOnlyOffCriticalZero ctx.test
  offCriticalPullback :=
    g8WeakOffCritical_subobligations_yield_pullback ctx h
  tauPurity := tauPurity
  finiteGuardrails := ctx.finiteGuardrails
  status := .conditionalExclusionAvailable

/-- The context produced from weak subobligations is admissible for the weak
    off-critical exclusion theorem. -/
theorem g8WeakOffCritical_exclusionTransferAdmissible
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (h : G8WeakOffCriticalPullbackSubobligations ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8OffCriticalExclusionTransferAdmissible
      (g8WeakOffCritical_to_exclusionTransferContext ctx h tauPurity) :=
  h.noChartOnly

/-- Weak pullback test plus tau purity yields the local no-off-critical-zero
    conclusion. -/
theorem g8WeakOffCritical_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (h : G8WeakOffCriticalPullbackSubobligations ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OffCriticalExclusion_noOffCriticalZeros
    (g8WeakOffCritical_to_exclusionTransferContext ctx h tauPurity)
    (g8WeakOffCritical_exclusionTransferAdmissible ctx h tauPurity)

end Tau.BookIII.Bridge
