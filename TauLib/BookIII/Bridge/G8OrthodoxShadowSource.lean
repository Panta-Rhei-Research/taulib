import TauLib.BookIII.Bridge.G8PrimePolarityAxisOffsetAlignment

/-!
# TauLib.BookIII.Bridge.G8OrthodoxShadowSource

Orthodox shadow-source interface for the G8f off-axis localization corridor.

The v0.3 roadmap makes the first chart-theory arrow explicit:

* a declared orthodox off-critical candidate has a centered receiving shadow;
* that shadow agrees with the weak pullback test context;
* off-criticality is readable as off-axis in the centered shadow;
* the source records G3/G4 chart-readout guards without importing the full
  G8d divisor-transfer package into the weak lane.

This module only supplies the first arrow of the corridor.  It does not
construct tau preimages, does not prove axis-offset alignment for the actual
chart, and does not identify any receiving divisor.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- ORTHODOX SHADOW SOURCE
-- ============================================================

/-- Source package for the receiving-side centered shadow used by the weak
    G8f corridor.

The G3/G4 fields are chart-readout guards only.  They are deliberately weaker
than a full `G8dZeroDivisorTransferAdmissible` assumption. -/
structure G8OrthodoxShadowSource
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  centeredShadow : ctx.test.base.orthodoxZero → CriticalAxisShadow
  shadowAgrees :
    ∀ z : ctx.test.base.orthodoxZero,
      centeredShadow z = ctx.test.orthodoxShadow z
  offCriticalReadable :
    ∀ z : ctx.test.base.orthodoxZero,
      ClassicalOffCriticalZero ctx.test.base z →
        ShadowOffAxis (centeredShadow z)
  g3ZetaChartReadout :
    ctx.test.base.transfer.completion.chart.g3ZetaBridge
  g4CompletedXiReadout :
    ctx.test.base.transfer.completion.chart.g4AnalyticContinuation
  finiteGuardrails : G8bFiniteOnlyGuardrails finiteG8bContext :=
    finiteG8bContext_guardrails

/-- The shadow source exposes the G3 zeta-chart readout guard. -/
theorem g8OrthodoxShadowSource_requires_g3ZetaBridge
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowSource ctx) :
    ctx.test.base.transfer.completion.chart.g3ZetaBridge :=
  source.g3ZetaChartReadout

/-- The shadow source exposes the G4 completed-xi/continuation readout guard. -/
theorem g8OrthodoxShadowSource_requires_g4AnalyticContinuation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowSource ctx) :
    ctx.test.base.transfer.completion.chart.g4AnalyticContinuation :=
  source.g4CompletedXiReadout

/-- The shadow source remains below analytic divisor claims at the finite
    substrate layer. -/
theorem g8OrthodoxShadowSource_finiteOnly
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowSource ctx) :
    finiteG8bContext.finiteOnly :=
  source.finiteGuardrails.left

/-- The shadow source carries no orthodox xi-divisor claim from finite stages. -/
theorem g8OrthodoxShadowSource_noXiDivisorClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowSource ctx) :
    finiteG8bContext.noXiDivisorClaim :=
  source.finiteGuardrails.right.left

/-- The shadow source carries no analytic-completion claim from finite stages. -/
theorem g8OrthodoxShadowSource_noAnalyticCompletionClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowSource ctx) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  source.finiteGuardrails.right.right

-- ============================================================
-- ADAPTERS INTO THE EXISTING CHART CORRIDOR
-- ============================================================

/-- The orthodox shadow source builds the explicit off-axis chart object. -/
def g8OrthodoxShadowSource_to_chart
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowSource ctx) :
    G8OffAxisChartObject ctx where
  centeredShadow := source.centeredShadow
  shadowAgrees := source.shadowAgrees
  shadowReadable := source.offCriticalReadable

/-- The orthodox shadow source supplies chart-shadow readability. -/
theorem g8OrthodoxShadowSource_readable
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowSource ctx) :
    G8ChartShadowReadable (g8OrthodoxShadowSource_to_chart source) :=
  source.offCriticalReadable

/-- The orthodox shadow source supplies the decomposed readability predicate. -/
theorem g8OrthodoxShadowSource_offAxisChartReadable
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowSource ctx) :
    G8OffAxisChartReadable (g8OrthodoxShadowSource_to_chart source) :=
  g8OrthodoxShadowSource_readable source

/-- The orthodox shadow source yields local fold readability for the weak
    pullback test. -/
theorem g8OrthodoxShadowSource_localFold
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (source : G8OrthodoxShadowSource ctx) :
    G8e1LocalFoldReadable ctx.test :=
  g8OffAxisChartObject_localFold ctx
    (g8OrthodoxShadowSource_to_chart source)

/-- A declared orthodox off-critical candidate becomes off-axis in the chart
    built from the shadow source. -/
theorem g8OrthodoxShadowSource_offCritical_to_chartOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    G8ChartOffAxis (g8OrthodoxShadowSource_to_chart source) z :=
  source.offCriticalReadable z hz

/-- The chart built from the shadow source agrees with the weak test context. -/
theorem g8OrthodoxShadowSource_chart_agrees
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowSource ctx)
    (z : ctx.test.base.orthodoxZero) :
    (g8OrthodoxShadowSource_to_chart source).centeredShadow z =
      ctx.test.orthodoxShadow z :=
  source.shadowAgrees z

-- ============================================================
-- FALSIFIERS FOR THE SHADOW-SOURCE STEP
-- ============================================================

/-- An orthodox off-critical candidate whose declared source shadow is not
    readable as off-axis. -/
structure G8OrthodoxUnreadableOffCriticalShadowWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowSource ctx) where
  z : ctx.test.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  notReadable : ¬ ShadowOffAxis (source.centeredShadow z)

/-- An unreadable off-critical shadow refutes the shadow source. -/
theorem g8OrthodoxUnreadableShadow_refutes_source
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowSource ctx}
    (w : G8OrthodoxUnreadableOffCriticalShadowWitness source) :
    False :=
  w.notReadable (source.offCriticalReadable w.z w.offCritical)

/-- A mismatch between the source shadow and the weak test context shadow. -/
structure G8OrthodoxShadowAgreementMismatchWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowSource ctx) where
  z : ctx.test.base.orthodoxZero
  mismatch :
    source.centeredShadow z ≠ ctx.test.orthodoxShadow z

/-- A shadow agreement mismatch refutes the shadow source. -/
theorem g8OrthodoxShadowAgreementMismatch_refutes_source
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowSource ctx}
    (w : G8OrthodoxShadowAgreementMismatchWitness source) :
    False :=
  w.mismatch (source.shadowAgrees w.z)

/-- An off-critical candidate accidentally classified as on-axis by the source
    shadow. -/
structure G8OrthodoxOffCriticalOnAxisWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowSource ctx) where
  z : ctx.test.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  onAxis : OnCriticalAxis (source.centeredShadow z)

/-- An on-axis classification of an off-critical candidate refutes the shadow
    source readability field. -/
theorem g8OrthodoxOffCriticalOnAxis_refutes_source
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowSource ctx}
    (w : G8OrthodoxOffCriticalOnAxisWitness source) :
    False :=
  (source.offCriticalReadable w.z w.offCritical) w.onAxis

/-- A context-level on-axis classification of an off-critical candidate
    refutes the shadow source through the agreement field. -/
structure G8OrthodoxContextOffCriticalOnAxisWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowSource ctx) where
  z : ctx.test.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  onAxis : OnCriticalAxis (ctx.test.orthodoxShadow z)

/-- A context-level on-axis witness refutes the shadow source. -/
theorem g8OrthodoxContextOffCriticalOnAxis_refutes_source
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowSource ctx}
    (w : G8OrthodoxContextOffCriticalOnAxisWitness source) :
    False := by
  have hChartAxis : OnCriticalAxis (source.centeredShadow w.z) := by
    rw [source.shadowAgrees w.z]
    exact w.onAxis
  exact (source.offCriticalReadable w.z w.offCritical) hChartAxis

end Tau.BookIII.Bridge
