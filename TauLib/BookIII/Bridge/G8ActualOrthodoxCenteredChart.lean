import TauLib.BookIII.Bridge.G8OrthodoxShadowAxisSource

/-!
# TauLib.BookIII.Bridge.G8ActualOrthodoxCenteredChart

Named actual centered orthodox chart source for the G8f corridor.

The previous shadow-axis source already contains the proof-facing chart
hygiene fields needed by the weak off-axis route: a centered shadow, agreement
with the weak test context, the off-critical iff not-on-axis law, and the G3/G4
readout guards.  This module gives that source a stable "actual centered
orthodox chart" name so later modules can instantiate the real xi/zeta chart
without changing the local corridor.

No tau preimage, O3 theorem, analytic-completion theorem, full divisor
transfer, or final global target is established here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- ACTUAL CENTERED CHART SOURCE
-- ============================================================

/-- Actual centered orthodox chart source for the weak G8f corridor.

For now this is a thin wrapper around `G8OrthodoxShadowAxisSource`.  The name
marks the intended future instantiation point for the concrete centered
xi/zeta chart. -/
structure G8ActualOrthodoxCenteredChart
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  shadowAxisSource : G8OrthodoxShadowAxisSource ctx

/-- Extract the underlying shadow-axis source. -/
def g8ActualOrthodoxCenteredChart_to_shadowAxisSource
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx) :
    G8OrthodoxShadowAxisSource ctx :=
  actual.shadowAxisSource

/-- The centered shadow of the actual chart. -/
def g8ActualOrthodoxCenteredChart_centeredShadow
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx) :
    ctx.test.base.orthodoxZero → CriticalAxisShadow :=
  actual.shadowAxisSource.centeredShadow

/-- The actual chart as an explicit off-axis chart object. -/
def g8ActualOrthodoxCenteredChart_to_chart
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx) :
    G8OffAxisChartObject ctx :=
  g8OrthodoxShadowAxisSource_to_chart actual.shadowAxisSource

/-- The actual chart as centered chart hygiene. -/
def g8ActualOrthodoxCenteredChart_to_centeredHygiene
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx) :
    G8OrthodoxCenteredChartHygiene ctx :=
  g8OrthodoxShadowAxisSource_to_centeredHygiene
    actual.shadowAxisSource

/-- The actual chart as the older orthodox shadow-source package. -/
def g8ActualOrthodoxCenteredChart_to_shadowSource
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx) :
    G8OrthodoxShadowSource ctx :=
  g8OrthodoxShadowAxisSource_to_shadowSource
    actual.shadowAxisSource

/-- The actual chart's no-off-axis-chart-only-ghost guard. -/
def G8ActualOrthodoxCenteredChartNoOffAxisGhosts
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx) : Prop :=
  G8OffAxisChartOnlyGhostGuard
    (g8ActualOrthodoxCenteredChart_to_chart actual)

-- ============================================================
-- SELECTORS AND GUARDRAILS
-- ============================================================

/-- The actual chart exposes the G3 zeta-chart readout guard. -/
theorem g8ActualOrthodoxCenteredChart_requires_g3ZetaBridge
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx) :
    ctx.test.base.transfer.completion.chart.g3ZetaBridge :=
  g8OrthodoxShadowAxisSource_requires_g3ZetaBridge
    actual.shadowAxisSource

/-- The actual chart exposes the G4 completed-xi/continuation readout guard. -/
theorem g8ActualOrthodoxCenteredChart_requires_g4AnalyticContinuation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx) :
    ctx.test.base.transfer.completion.chart.g4AnalyticContinuation :=
  g8OrthodoxShadowAxisSource_requires_g4AnalyticContinuation
    actual.shadowAxisSource

/-- The actual chart remains finite-only at the G8b layer. -/
theorem g8ActualOrthodoxCenteredChart_finiteOnly
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx) :
    finiteG8bContext.finiteOnly :=
  g8OrthodoxShadowAxisSource_finiteOnly actual.shadowAxisSource

/-- The actual chart carries no xi-divisor claim from finite stages. -/
theorem g8ActualOrthodoxCenteredChart_noXiDivisorClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx) :
    finiteG8bContext.noXiDivisorClaim :=
  g8OrthodoxShadowAxisSource_noXiDivisorClaim
    actual.shadowAxisSource

/-- The actual chart carries no analytic-completion claim from finite stages. -/
theorem g8ActualOrthodoxCenteredChart_noAnalyticCompletionClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8OrthodoxShadowAxisSource_noAnalyticCompletionClaim
    actual.shadowAxisSource

-- ============================================================
-- LOCAL CHART HYGIENE
-- ============================================================

/-- Off-criticality is exactly failure of the actual centered shadow axis. -/
theorem g8ActualOrthodoxCenteredChart_offCritical_iff_offAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx)
    (z : ctx.test.base.orthodoxZero) :
    ClassicalOffCriticalZero ctx.test.base z ↔
      ShadowOffAxis
        (g8ActualOrthodoxCenteredChart_centeredShadow actual z) :=
  g8OrthodoxShadowAxisSource_offCritical_iff_offAxis
    actual.shadowAxisSource z

/-- An orthodox off-critical candidate is readable as off-axis in the actual
    centered shadow. -/
theorem g8ActualOrthodoxCenteredChart_offCritical_to_offAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    ShadowOffAxis
      (g8ActualOrthodoxCenteredChart_centeredShadow actual z) :=
  g8OrthodoxShadowAxisSource_offCritical_to_offAxis
    actual.shadowAxisSource z hz

/-- An orthodox off-critical candidate is readable as off-axis in the explicit
    actual chart object. -/
theorem g8ActualOrthodoxCenteredChart_offCritical_to_chartOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    G8ChartOffAxis
      (g8ActualOrthodoxCenteredChart_to_chart actual) z :=
  g8OrthodoxShadowAxisSource_offCritical_to_chartOffAxis
    actual.shadowAxisSource z hz

/-- The actual centered chart supplies local fold readability for the weak
    corridor. -/
theorem g8ActualOrthodoxCenteredChart_localFold
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (actual : G8ActualOrthodoxCenteredChart ctx) :
    G8e1LocalFoldReadable ctx.test :=
  g8OrthodoxShadowAxisSource_localFold ctx
    actual.shadowAxisSource

/-- The actual chart object agrees with the weak test context's orthodox
    shadow. -/
theorem g8ActualOrthodoxCenteredChart_chart_agrees
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx)
    (z : ctx.test.base.orthodoxZero) :
    (g8ActualOrthodoxCenteredChart_to_chart actual).centeredShadow z =
      ctx.test.orthodoxShadow z :=
  g8OrthodoxShadowAxisSource_chart_agrees
    actual.shadowAxisSource z

-- ============================================================
-- FALSIFIERS AND DIAGNOSTICS
-- ============================================================

/-- An actual-chart off-critical candidate classified on-axis refutes the
    actual chart source law. -/
structure G8ActualOrthodoxCenteredChartOffCriticalOnAxisWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx) where
  z : ctx.test.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  shadowAxis :
    OnCriticalAxis
      (g8ActualOrthodoxCenteredChart_centeredShadow actual z)

/-- Off-critical but on-axis data refutes the actual centered chart source. -/
theorem
    g8ActualOrthodoxCenteredChartOffCriticalOnAxis_refutes_actual
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {actual : G8ActualOrthodoxCenteredChart ctx}
    (w : G8ActualOrthodoxCenteredChartOffCriticalOnAxisWitness actual) :
    False :=
  (g8ActualOrthodoxCenteredChart_offCritical_to_offAxis
    actual w.z w.offCritical) w.shadowAxis

/-- A mismatch between the actual centered chart and the weak test context. -/
structure G8ActualOrthodoxCenteredChartAgreementMismatchWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx) where
  z : ctx.test.base.orthodoxZero
  mismatch :
    (g8ActualOrthodoxCenteredChart_centeredShadow actual z) ≠
      ctx.test.orthodoxShadow z

/-- Actual chart/context mismatch refutes the actual chart source. -/
theorem
    g8ActualOrthodoxCenteredChartAgreementMismatch_refutes_actual
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {actual : G8ActualOrthodoxCenteredChart ctx}
    (w : G8ActualOrthodoxCenteredChartAgreementMismatchWitness actual) :
    False :=
  w.mismatch
    (g8ActualOrthodoxCenteredChart_chart_agrees actual w.z)

/-- Height/provenance mismatch is diagnostic only for G8f localization. -/
structure G8ActualOrthodoxCenteredChartHeightDiagnostic
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (actual : G8ActualOrthodoxCenteredChart ctx) where
  z : ctx.test.base.orthodoxZero
  referenceHeight : Nat
  heightDiffers :
    (g8ActualOrthodoxCenteredChart_centeredShadow actual z).heightWitness ≠
      referenceHeight

/-- Height diagnostics do not refute the off-axis localization chart. -/
theorem
    g8ActualOrthodoxCenteredChartHeightDiagnostic_not_refutation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {actual : G8ActualOrthodoxCenteredChart ctx}
    (_w : G8ActualOrthodoxCenteredChartHeightDiagnostic actual) :
    True :=
  trivial

end Tau.BookIII.Bridge
