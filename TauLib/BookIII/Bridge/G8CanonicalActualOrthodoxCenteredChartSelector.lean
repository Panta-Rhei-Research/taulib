import TauLib.BookIII.Bridge.G8ActualOrthodoxCenteredChartNormalizedCorridor
import TauLib.BookIII.Bridge.G8CanonicalTauWitnessSelector

/-!
# TauLib.BookIII.Bridge.G8CanonicalActualOrthodoxCenteredChartSelector

Canonical selector adapter for an actual centered orthodox chart.

This module plugs the actual-centered-chart naming layer into the pointwise
canonical tau-witness selector.  It is intentionally an adapter layer: the
actual xi/zeta chart still has to be instantiated upstream, and tau-side purity
remains an explicit input to the local exclusion theorem.

No analytic xi chart, O3 correspondence, full divisor transfer, or final
global target is established here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- ACTUAL CHART INDUCED BY THE CANONICAL SOURCE
-- ============================================================

/-- A canonical tau-witness source induces an actual centered chart source for
    its weak G8f context. -/
def g8CanonicalTauWitness_to_actualCenteredChart
    (source : G8CanonicalTauWitnessSource) :
    G8ActualOrthodoxCenteredChart
      (g8CanonicalTauWitness_weak source) where
  shadowAxisSource := g8CanonicalTauWitness_shadowAxisSource source

/-- The chart induced by a canonical source is the canonical selector chart. -/
theorem g8CanonicalTauWitness_actualChart_eq_canonicalChart
    (source : G8CanonicalTauWitnessSource) :
    g8ActualOrthodoxCenteredChart_to_chart
        (g8CanonicalTauWitness_to_actualCenteredChart source) =
      g8CanonicalTauWitness_chart source :=
  rfl

/-- The actual chart induced by a canonical source exposes the same shadow-axis
    source as the canonical source. -/
theorem g8CanonicalTauWitness_actualShadowAxisSource_eq
    (source : G8CanonicalTauWitnessSource) :
    (g8CanonicalTauWitness_to_actualCenteredChart source).shadowAxisSource =
      g8CanonicalTauWitness_shadowAxisSource source :=
  rfl

-- ============================================================
-- POINTWISE NO-GHOST GUARD
-- ============================================================

/-- The canonical pointwise selector rules out off-axis chart-only ghosts for
    the induced actual centered chart. -/
theorem g8CanonicalTauWitness_actual_noOffAxisChartOnlyGhost
    (source : G8CanonicalTauWitnessSource) :
    G8ActualOrthodoxCenteredChartNoOffAxisGhosts
      (g8CanonicalTauWitness_to_actualCenteredChart source) :=
  g8CanonicalTauWitness_offAxisGuard_pointwise source

/-- Missing selected witnesses for the induced actual chart are refuted by the
    pointwise canonical selector. -/
theorem
    g8CanonicalTauWitness_actual_selectedWitnessUnavailable_refutes
    {source : G8CanonicalTauWitnessSource}
    (w : G8CanonicalSelectedWitnessUnavailable source) :
    False :=
  g8CanonicalSelectedWitnessUnavailable_refutes_selector w

/-- Missing normalized preimages for the induced actual chart are refuted by
    the pointwise canonical selector. -/
theorem
    g8CanonicalTauWitness_actual_normalizedPreimageUnavailable_refutes
    {source : G8CanonicalTauWitnessSource}
    (w : G8CanonicalNormalizedPreimageUnavailable source) :
    False :=
  g8CanonicalNormalizedPreimageUnavailable_refutes_selector w

-- ============================================================
-- NORMALIZED CORRIDOR ADAPTER
-- ============================================================

/-- The canonical pointwise selector supplies the normalized actual-chart
    corridor. -/
def g8CanonicalTauWitness_actual_to_normalizedCorridor
    (source : G8CanonicalTauWitnessSource) :
    G8ActualOrthodoxCenteredChartNormalizedCorridor
      (g8CanonicalTauWitness_weak source) where
  actual := g8CanonicalTauWitness_to_actualCenteredChart source
  unitTauPreimages :=
    g8CanonicalTauWitness_selector_to_unitPreimages source
  tauWitness := g8CanonicalTauWitness_tauWitnessRealization source
  offAxisGuard :=
    g8CanonicalTauWitness_actual_noOffAxisChartOnlyGhost source

/-- The canonical actual-chart corridor exposes normalized preimages. -/
theorem
    g8CanonicalTauWitness_actual_to_normalizedPreimages
    (source : G8CanonicalTauWitnessSource) :
    G8OrthodoxTauNormalizedAxisPreimagesExist
      (g8CanonicalTauWitness_shadowAxisSource source) :=
  g8ActualOrthodoxCenteredChartNormalizedCorridor_normalizedPreimages
    (g8CanonicalTauWitness_actual_to_normalizedCorridor source)

/-- The canonical actual-chart corridor exposes the no-ghost guard. -/
theorem
    g8CanonicalTauWitness_actual_to_noGhosts
    (source : G8CanonicalTauWitnessSource) :
    G8ActualOrthodoxCenteredChartNoOffAxisGhosts
      (g8CanonicalTauWitness_to_actualCenteredChart source) :=
  g8ActualOrthodoxCenteredChartNormalizedCorridor_noGhosts
    (g8CanonicalTauWitness_actual_to_normalizedCorridor source)

-- ============================================================
-- LOCAL PULLBACK AND EXCLUSION
-- ============================================================

/-- The canonical actual-chart selector yields the local one-sided pullback. -/
theorem g8CanonicalTauWitness_actual_yields_pullback
    (source : G8CanonicalTauWitnessSource) :
    G8eOffCriticalPullback
      (g8CanonicalTauWitness_base source) :=
  g8ActualOrthodoxCenteredChartNormalizedCorridor_yields_pullback
    (g8CanonicalTauWitness_weak source)
    (g8CanonicalTauWitness_actual_to_normalizedCorridor source)

/-- The canonical actual-chart selector plus tau-side purity yields local
    no-off-critical orthodox zeros. -/
theorem g8CanonicalTauWitness_actual_noOffCriticalZeros
    (source : G8CanonicalTauWitnessSource)
    (tauPurity :
      G8eTauPurityExcludesOffCritical
        (g8CanonicalTauWitness_base source)) :
    G8eNoOrthodoxOffCriticalZeros
      (g8CanonicalTauWitness_base source) :=
  g8ActualOrthodoxCenteredChartNormalizedCorridor_noOffCriticalZeros
    (g8CanonicalTauWitness_weak source)
    (g8CanonicalTauWitness_actual_to_normalizedCorridor source)
    tauPurity

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- The canonical actual-chart selector remains finite-only at G8b. -/
theorem g8CanonicalTauWitness_actual_finiteOnly
    (source : G8CanonicalTauWitnessSource) :
    finiteG8bContext.finiteOnly :=
  g8ActualOrthodoxCenteredChartNormalizedCorridor_finiteOnly
    (g8CanonicalTauWitness_actual_to_normalizedCorridor source)

/-- The canonical actual-chart selector carries no xi-divisor claim from
    finite stages. -/
theorem g8CanonicalTauWitness_actual_noXiDivisorClaim
    (source : G8CanonicalTauWitnessSource) :
    finiteG8bContext.noXiDivisorClaim :=
  g8ActualOrthodoxCenteredChartNormalizedCorridor_noXiDivisorClaim
    (g8CanonicalTauWitness_actual_to_normalizedCorridor source)

/-- The canonical actual-chart selector carries no analytic-completion claim
    from finite stages. -/
theorem g8CanonicalTauWitness_actual_noAnalyticCompletionClaim
    (source : G8CanonicalTauWitnessSource) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8ActualOrthodoxCenteredChartNormalizedCorridor_noAnalyticCompletionClaim
    (g8CanonicalTauWitness_actual_to_normalizedCorridor source)

end Tau.BookIII.Bridge
