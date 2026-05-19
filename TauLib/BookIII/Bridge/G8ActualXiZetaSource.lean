import TauLib.BookIII.Bridge.G8ActualXiZetaCore

/-!
# TauLib.BookIII.Bridge.G8ActualXiZetaSource

Source adapter from the actual Mathlib-backed `xi` zero object into the G8f
orthodox centered-chart corridor.

The receiving side is Mathlib-native.  The tau side remains abstract through a
declared tau-witness carrier and normal-form map.  This module does not prove a
tau preimage theorem, O3, full divisor transfer, or any global target.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- ACTUAL XI/ZETA SOURCE CONTEXT
-- ============================================================

/-- Actual orthodox `xi`/`zeta` source context for the weak G8f corridor.

`transfer` carries the existing G3-G8 obligation stack.  The two readout fields
select the G3 zeta-chart and G4 analytic-continuation guards from that stack,
without asserting any divisor-transfer theorem. -/
structure G8ActualXiZetaSourceContext where
  transfer : G8dZeroDivisorTransferContext
  tauWitness : Type 2
  tauNormalForm : tauWitness → BoundaryNF
  g3ZetaChartReadout :
    transfer.completion.chart.g3ZetaBridge
  g4CompletedXiReadout :
    transfer.completion.chart.g4AnalyticContinuation
  status : G8OffCriticalExclusionStatus := .openObligation

/-- The actual `xi` source as an off-critical pullback base. -/
def g8ActualXiZeta_base
    (source : G8ActualXiZetaSourceContext) :
    OffCriticalZeroPullbackContext where
  transfer := source.transfer
  orthodoxZero := OrthodoxXiZeroCarrier
  tauWitness := source.tauWitness
  isOrthodoxOffCriticalZero := OrthodoxXiCarrierOffCritical
  isTauOffCriticalWitness :=
    fun w => TauCriticalImbalance (source.tauNormalForm w)
  status := .conditionalInterface

/-- The actual `xi` source as a weak off-critical pullback test context. -/
def g8ActualXiZeta_weak
    (source : G8ActualXiZetaSourceContext) :
    G8WeakOffCriticalPullbackTestContext where
  test := {
    base := g8ActualXiZeta_base source
    orthodoxShadow := orthodoxXiCarrierCenteredShadow
    tauNormalForm := source.tauNormalForm
    status := .localFoldOnly
  }
  finiteGuardrails := finiteG8bContext_guardrails
  status := source.status

/-- The actual `xi` source supplies the shadow-axis source required by the
    centered chart corridor. -/
def g8ActualXiZeta_shadowAxisSource
    (source : G8ActualXiZetaSourceContext) :
    G8OrthodoxShadowAxisSource (g8ActualXiZeta_weak source) where
  centeredShadow := orthodoxXiCarrierCenteredShadow
  shadowAgrees := by
    intro z
    rfl
  offCritical_iff_notShadowAxis := by
    intro z
    exact orthodoxXiCarrierOffCritical_iff_notOnAxis z
  g3ZetaChartReadout := source.g3ZetaChartReadout
  g4CompletedXiReadout := source.g4CompletedXiReadout
  finiteGuardrails := finiteG8bContext_guardrails

/-- The actual `xi` source as the actual centered orthodox chart. -/
def g8ActualXiZeta_actualCenteredChart
    (source : G8ActualXiZetaSourceContext) :
    G8ActualOrthodoxCenteredChart
      (g8ActualXiZeta_weak source) where
  shadowAxisSource := g8ActualXiZeta_shadowAxisSource source

/-- The actual `xi` source as an explicit off-axis chart object. -/
def g8ActualXiZeta_chart
    (source : G8ActualXiZetaSourceContext) :
    G8OffAxisChartObject (g8ActualXiZeta_weak source) :=
  g8ActualOrthodoxCenteredChart_to_chart
    (g8ActualXiZeta_actualCenteredChart source)

-- ============================================================
-- SELECTORS AND LOCAL CHART THEOREMS
-- ============================================================

/-- The actual `xi` source exposes the G3 zeta-chart readout guard. -/
theorem g8ActualXiZeta_requires_g3ZetaBridge
    (source : G8ActualXiZetaSourceContext) :
    source.transfer.completion.chart.g3ZetaBridge :=
  source.g3ZetaChartReadout

/-- The actual `xi` source exposes the G4 completed-`xi` readout guard. -/
theorem g8ActualXiZeta_requires_g4AnalyticContinuation
    (source : G8ActualXiZetaSourceContext) :
    source.transfer.completion.chart.g4AnalyticContinuation :=
  source.g4CompletedXiReadout

/-- The actual `xi` source remains finite-only at G8b. -/
theorem g8ActualXiZeta_finiteOnly
    (_source : G8ActualXiZetaSourceContext) :
    finiteG8bContext.finiteOnly :=
  finiteG8bContext_guardrails.left

/-- The actual `xi` source carries no orthodox divisor claim from finite stages. -/
theorem g8ActualXiZeta_noXiDivisorClaim
    (_source : G8ActualXiZetaSourceContext) :
    finiteG8bContext.noXiDivisorClaim :=
  finiteG8bContext_guardrails.right.left

/-- The actual `xi` source carries no analytic-completion claim from finite
    stages. -/
theorem g8ActualXiZeta_noAnalyticCompletionClaim
    (_source : G8ActualXiZetaSourceContext) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  finiteG8bContext_guardrails.right.right

/-- Actual `xi` off-criticality is exactly off-axis readability in the source
    shadow. -/
theorem g8ActualXiZeta_offCritical_iff_offAxis
    (source : G8ActualXiZetaSourceContext)
    (z : OrthodoxXiZeroCarrier) :
    ClassicalOffCriticalZero (g8ActualXiZeta_base source) z ↔
      ShadowOffAxis (orthodoxXiCarrierCenteredShadow z) :=
  orthodoxXiCarrierOffCritical_iff_shadowOffAxis z

/-- An actual orthodox `xi` off-critical zero is readable as an off-axis chart
    shadow. -/
theorem g8ActualXiZeta_offCritical_to_chartOffAxis
    (source : G8ActualXiZetaSourceContext)
    (z : OrthodoxXiZeroCarrier)
    (hz : ClassicalOffCriticalZero (g8ActualXiZeta_base source) z) :
    G8ChartOffAxis (g8ActualXiZeta_chart source) z :=
  g8ActualOrthodoxCenteredChart_offCritical_to_chartOffAxis
    (g8ActualXiZeta_actualCenteredChart source) z hz

/-- The actual `xi` source supplies local fold readability for G8f. -/
theorem g8ActualXiZeta_localFold
    (source : G8ActualXiZetaSourceContext) :
    G8e1LocalFoldReadable (g8ActualXiZeta_weak source).test :=
  g8ActualOrthodoxCenteredChart_localFold
    (g8ActualXiZeta_weak source)
    (g8ActualXiZeta_actualCenteredChart source)

end Tau.BookIII.Bridge
