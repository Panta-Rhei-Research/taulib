import TauLib.BookIII.Bridge.G8ActualXiZetaSource
import TauLib.BookIII.Bridge.G8ActualOrthodoxCenteredChartNormalizedCorridor

/-!
# TauLib.BookIII.Bridge.G8ActualXiZetaCorridor

Conditional G8f corridor for the actual Mathlib-backed orthodox `xi` chart.

This module connects the real receiving-side `xi` zero object to the existing
actual centered-chart corridor.  It still takes tau preimage supply, tau witness
realization, the off-axis ghost guard, tau purity, and Mathlib-zeta coverage as
explicit inputs.  No bridge theorem is hidden here.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- ACTUAL XI/ZETA CORRIDOR
-- ============================================================

/-- Actual `xi`/`zeta` corridor package.

The Mathlib receiving chart is concrete, but the tau preimage and no-ghost
fields remain the explicit hard G8f obligations. -/
structure G8ActualXiZetaCorridor
    (source : G8ActualXiZetaSourceContext) where
  unitTauPreimages :
    G8OrthodoxTauUnitAxisPreimagesExist
      (g8ActualXiZeta_shadowAxisSource source)
  tauWitness :
    G8OffAxisTauWitnessRealization
      (g8ActualXiZeta_chart source)
  offAxisGuard :
    G8ActualOrthodoxCenteredChartNoOffAxisGhosts
      (g8ActualXiZeta_actualCenteredChart source)

/-- The actual `xi`/`zeta` corridor as the existing actual centered-chart
    normalized corridor. -/
def g8ActualXiZetaCorridor_to_normalizedCorridor
    {source : G8ActualXiZetaSourceContext}
    (corridor : G8ActualXiZetaCorridor source) :
    G8ActualOrthodoxCenteredChartNormalizedCorridor
      (g8ActualXiZeta_weak source) where
  actual := g8ActualXiZeta_actualCenteredChart source
  unitTauPreimages := corridor.unitTauPreimages
  tauWitness := corridor.tauWitness
  offAxisGuard := corridor.offAxisGuard

-- ============================================================
-- SELECTORS
-- ============================================================

/-- The actual `xi`/`zeta` corridor exposes unit tau preimages. -/
theorem g8ActualXiZetaCorridor_unitPreimages
    {source : G8ActualXiZetaSourceContext}
    (corridor : G8ActualXiZetaCorridor source) :
    G8OrthodoxTauUnitAxisPreimagesExist
      (g8ActualXiZeta_shadowAxisSource source) :=
  corridor.unitTauPreimages

/-- The actual `xi`/`zeta` corridor exposes tau witness realization. -/
theorem g8ActualXiZetaCorridor_tauWitness
    {source : G8ActualXiZetaSourceContext}
    (corridor : G8ActualXiZetaCorridor source) :
    G8OffAxisTauWitnessRealization
      (g8ActualXiZeta_chart source) :=
  corridor.tauWitness

/-- The actual `xi`/`zeta` corridor exposes the off-axis ghost guard. -/
theorem g8ActualXiZetaCorridor_noGhosts
    {source : G8ActualXiZetaSourceContext}
    (corridor : G8ActualXiZetaCorridor source) :
    G8ActualOrthodoxCenteredChartNoOffAxisGhosts
      (g8ActualXiZeta_actualCenteredChart source) :=
  corridor.offAxisGuard

/-- The actual `xi`/`zeta` corridor exposes the G3 zeta-chart readout guard. -/
theorem g8ActualXiZetaCorridor_requires_g3ZetaBridge
    {source : G8ActualXiZetaSourceContext}
    (_corridor : G8ActualXiZetaCorridor source) :
    source.transfer.completion.chart.g3ZetaBridge :=
  source.g3ZetaChartReadout

/-- The actual `xi`/`zeta` corridor exposes the G4 analytic-continuation guard. -/
theorem g8ActualXiZetaCorridor_requires_g4AnalyticContinuation
    {source : G8ActualXiZetaSourceContext}
    (_corridor : G8ActualXiZetaCorridor source) :
    source.transfer.completion.chart.g4AnalyticContinuation :=
  source.g4CompletedXiReadout

-- ============================================================
-- LOCAL PULLBACK, EXCLUSION, AND MATHLIB TARGET HANDOFF
-- ============================================================

/-- The actual `xi`/`zeta` corridor yields the local one-sided G8f pullback. -/
theorem g8ActualXiZetaCorridor_yields_pullback
    (source : G8ActualXiZetaSourceContext)
    (corridor : G8ActualXiZetaCorridor source) :
    G8eOffCriticalPullback (g8ActualXiZeta_base source) :=
  g8ActualOrthodoxCenteredChartNormalizedCorridor_yields_pullback
    (g8ActualXiZeta_weak source)
    (g8ActualXiZetaCorridor_to_normalizedCorridor corridor)

/-- The actual `xi`/`zeta` corridor plus tau-side purity yields local exclusion
    of off-critical orthodox `xi` zeros. -/
theorem g8ActualXiZetaCorridor_noOffCriticalXiZeros
    (source : G8ActualXiZetaSourceContext)
    (corridor : G8ActualXiZetaCorridor source)
    (tauPurity :
      G8eTauPurityExcludesOffCritical
        (g8ActualXiZeta_base source)) :
    G8eNoOrthodoxOffCriticalZeros
      (g8ActualXiZeta_base source) :=
  g8ActualOrthodoxCenteredChartNormalizedCorridor_noOffCriticalZeros
    (g8ActualXiZeta_weak source)
    (g8ActualXiZetaCorridor_to_normalizedCorridor corridor)
    tauPurity

/-- Conditional handoff to Mathlib's formal `RiemannHypothesis` target.

The extra `coverage` hypothesis is the receiving-side zeta-to-xi coverage
obligation.  This theorem does not prove that coverage, and it does not provide
the tau-side corridor obligations. -/
theorem g8ActualXiZetaCorridor_to_mathlibRiemannHypothesis
    (source : G8ActualXiZetaSourceContext)
    (corridor : G8ActualXiZetaCorridor source)
    (tauPurity :
      G8eTauPurityExcludesOffCritical
        (g8ActualXiZeta_base source))
    (coverage : G8XiCoversMathlibNontrivialZetaZeros) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_from_noOffCriticalXiZeros coverage (by
    intro z hz
    exact
      (g8ActualXiZetaCorridor_noOffCriticalXiZeros
        source corridor tauPurity) z.toCarrier hz)

-- ============================================================
-- FINITE-STAGE GUARDRAILS
-- ============================================================

/-- The actual `xi`/`zeta` corridor remains finite-only at G8b. -/
theorem g8ActualXiZetaCorridor_finiteOnly
    {source : G8ActualXiZetaSourceContext}
    (corridor : G8ActualXiZetaCorridor source) :
    finiteG8bContext.finiteOnly :=
  g8ActualOrthodoxCenteredChartNormalizedCorridor_finiteOnly
    (g8ActualXiZetaCorridor_to_normalizedCorridor corridor)

/-- The actual `xi`/`zeta` corridor carries no `xi` divisor claim from finite
    stages. -/
theorem g8ActualXiZetaCorridor_noXiDivisorClaim
    {source : G8ActualXiZetaSourceContext}
    (corridor : G8ActualXiZetaCorridor source) :
    finiteG8bContext.noXiDivisorClaim :=
  g8ActualOrthodoxCenteredChartNormalizedCorridor_noXiDivisorClaim
    (g8ActualXiZetaCorridor_to_normalizedCorridor corridor)

/-- The actual `xi`/`zeta` corridor carries no analytic-completion claim from
    finite stages. -/
theorem g8ActualXiZetaCorridor_noAnalyticCompletionClaim
    {source : G8ActualXiZetaSourceContext}
    (corridor : G8ActualXiZetaCorridor source) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8ActualOrthodoxCenteredChartNormalizedCorridor_noAnalyticCompletionClaim
    (g8ActualXiZetaCorridor_to_normalizedCorridor corridor)

end Tau.BookIII.Bridge
