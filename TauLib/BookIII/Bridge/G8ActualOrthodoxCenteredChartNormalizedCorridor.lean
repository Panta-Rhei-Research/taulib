import TauLib.BookIII.Bridge.G8ActualOrthodoxCenteredChart
import TauLib.BookIII.Bridge.G8OrthodoxNormalizedAxisClass

/-!
# TauLib.BookIII.Bridge.G8ActualOrthodoxCenteredChartNormalizedCorridor

Normalized-axis corridor for an actual centered orthodox chart.

This module packages the actual centered chart together with exactly the
positive G8f ingredients needed by the existing normalized-axis corridor:
unit tau preimages, tau-witness realization, and the no-off-axis-chart-only
ghost guard.  It deliberately uses the binary normalized axis class, not raw
axis-offset equality.

No full zero-divisor transfer, analytic-completion theorem, O3 theorem, or
final global target is established here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- NORMALIZED CORRIDOR
-- ============================================================

/-- Actual centered chart plus the normalized-axis proof fields consumed by
    the weak G8f corridor. -/
structure G8ActualOrthodoxCenteredChartNormalizedCorridor
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  actual : G8ActualOrthodoxCenteredChart ctx
  unitTauPreimages :
    G8OrthodoxTauUnitAxisPreimagesExist
      actual.shadowAxisSource
  tauWitness :
    G8OffAxisTauWitnessRealization
      (g8ActualOrthodoxCenteredChart_to_chart actual)
  offAxisGuard :
    G8ActualOrthodoxCenteredChartNoOffAxisGhosts actual

/-- The actual normalized corridor as the existing normalized preimage
    context. -/
def
    g8ActualOrthodoxCenteredChartNormalizedCorridor_to_preimageContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (corridor :
      G8ActualOrthodoxCenteredChartNormalizedCorridor ctx) :
    G8OrthodoxNormalizedAxisPreimageContext ctx where
  source := corridor.actual.shadowAxisSource
  unitTauPreimages := corridor.unitTauPreimages
  tauWitness := corridor.tauWitness
  offAxisGuard := corridor.offAxisGuard

/-- The actual normalized corridor supplies decomposed chart faithfulness. -/
def
    g8ActualOrthodoxCenteredChartNormalizedCorridor_to_decomposition
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (corridor :
      G8ActualOrthodoxCenteredChartNormalizedCorridor ctx) :
    G8OffAxisChartFaithfulnessDecomposition
      (g8ActualOrthodoxCenteredChart_to_chart corridor.actual) :=
  g8OrthodoxNormalizedAxisPreimage_to_decomposition
    (g8ActualOrthodoxCenteredChartNormalizedCorridor_to_preimageContext
      corridor)

-- ============================================================
-- SELECTORS
-- ============================================================

/-- The actual normalized corridor exposes the actual centered chart. -/
def g8ActualOrthodoxCenteredChartNormalizedCorridor_actual
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (corridor :
      G8ActualOrthodoxCenteredChartNormalizedCorridor ctx) :
    G8ActualOrthodoxCenteredChart ctx :=
  corridor.actual

/-- The actual normalized corridor exposes unit tau preimages. -/
theorem
    g8ActualOrthodoxCenteredChartNormalizedCorridor_unitPreimages
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (corridor :
      G8ActualOrthodoxCenteredChartNormalizedCorridor ctx) :
    G8OrthodoxTauUnitAxisPreimagesExist
      corridor.actual.shadowAxisSource :=
  corridor.unitTauPreimages

/-- The actual normalized corridor exposes normalized preimages. -/
theorem
    g8ActualOrthodoxCenteredChartNormalizedCorridor_normalizedPreimages
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (corridor :
      G8ActualOrthodoxCenteredChartNormalizedCorridor ctx) :
    G8OrthodoxTauNormalizedAxisPreimagesExist
      corridor.actual.shadowAxisSource :=
  g8OrthodoxTauUnitPreimages_to_normalizedPreimages
    corridor.actual.shadowAxisSource
    corridor.unitTauPreimages

/-- The actual normalized corridor exposes the no-ghost guard. -/
theorem
    g8ActualOrthodoxCenteredChartNormalizedCorridor_noGhosts
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (corridor :
      G8ActualOrthodoxCenteredChartNormalizedCorridor ctx) :
    G8ActualOrthodoxCenteredChartNoOffAxisGhosts
      corridor.actual :=
  corridor.offAxisGuard

/-- The actual normalized corridor exposes G3 chart readout. -/
theorem
    g8ActualOrthodoxCenteredChartNormalizedCorridor_requires_g3ZetaBridge
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (corridor :
      G8ActualOrthodoxCenteredChartNormalizedCorridor ctx) :
    ctx.test.base.transfer.completion.chart.g3ZetaBridge :=
  g8ActualOrthodoxCenteredChart_requires_g3ZetaBridge
    corridor.actual

/-- The actual normalized corridor exposes G4 completed-xi readout. -/
theorem
    g8ActualOrthodoxCenteredChartNormalizedCorridor_requires_g4AnalyticContinuation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (corridor :
      G8ActualOrthodoxCenteredChartNormalizedCorridor ctx) :
    ctx.test.base.transfer.completion.chart.g4AnalyticContinuation :=
  g8ActualOrthodoxCenteredChart_requires_g4AnalyticContinuation
    corridor.actual

-- ============================================================
-- LOCAL PULLBACK AND EXCLUSION
-- ============================================================

/-- The actual normalized corridor yields the local one-sided pullback. -/
theorem g8ActualOrthodoxCenteredChartNormalizedCorridor_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (corridor :
      G8ActualOrthodoxCenteredChartNormalizedCorridor ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8OrthodoxNormalizedAxisPreimage_yields_pullback
    ctx
    (g8ActualOrthodoxCenteredChartNormalizedCorridor_to_preimageContext
      corridor)

/-- The actual normalized corridor plus tau-side purity yields local
    no-off-critical orthodox zeros. -/
theorem g8ActualOrthodoxCenteredChartNormalizedCorridor_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (corridor :
      G8ActualOrthodoxCenteredChartNormalizedCorridor ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OrthodoxNormalizedAxisPreimage_noOffCriticalZeros
    ctx
    (g8ActualOrthodoxCenteredChartNormalizedCorridor_to_preimageContext
      corridor)
    tauPurity

-- ============================================================
-- FINITE-STAGE GUARDRAILS
-- ============================================================

/-- The actual normalized corridor remains finite-only at G8b. -/
theorem g8ActualOrthodoxCenteredChartNormalizedCorridor_finiteOnly
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (corridor :
      G8ActualOrthodoxCenteredChartNormalizedCorridor ctx) :
    finiteG8bContext.finiteOnly :=
  g8ActualOrthodoxCenteredChart_finiteOnly corridor.actual

/-- The actual normalized corridor carries no xi-divisor claim from finite
    stages. -/
theorem g8ActualOrthodoxCenteredChartNormalizedCorridor_noXiDivisorClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (corridor :
      G8ActualOrthodoxCenteredChartNormalizedCorridor ctx) :
    finiteG8bContext.noXiDivisorClaim :=
  g8ActualOrthodoxCenteredChart_noXiDivisorClaim corridor.actual

/-- The actual normalized corridor carries no analytic-completion claim from
    finite stages. -/
theorem
    g8ActualOrthodoxCenteredChartNormalizedCorridor_noAnalyticCompletionClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (corridor :
      G8ActualOrthodoxCenteredChartNormalizedCorridor ctx) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8ActualOrthodoxCenteredChart_noAnalyticCompletionClaim
    corridor.actual

/-- Finite stages in the actual normalized corridor carry neither xi-divisor
    nor analytic-completion claims. -/
theorem
    g8ActualOrthodoxCenteredChartNormalizedCorridor_noFiniteDivisorOrCompletionClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (corridor :
      G8ActualOrthodoxCenteredChartNormalizedCorridor ctx) :
    finiteG8bContext.noXiDivisorClaim ∧
      finiteG8bContext.noAnalyticCompletionClaim :=
  ⟨g8ActualOrthodoxCenteredChartNormalizedCorridor_noXiDivisorClaim
      corridor,
    g8ActualOrthodoxCenteredChartNormalizedCorridor_noAnalyticCompletionClaim
      corridor⟩

end Tau.BookIII.Bridge
