import TauLib.BookIII.Bridge.G8OrthodoxShadowSource

/-!
# TauLib.BookIII.Bridge.G8OrthodoxShadowReadability

Chart-normalized readability for the first G8f chart-theory arrow.

`G8OrthodoxShadowSource` records the first arrow as a source-field interface:
an orthodox off-critical candidate has a readable off-axis centered shadow.
This module isolates the first theorem-backed version of that arrow.  It
introduces a chart-normalized receiving shadow where the declared orthodox
off-critical predicate is definitionally equivalent to being off-axis in the
centered shadow.  Under that normalization law, the arrow

`ClassicalOffCriticalZero -> readable off-axis chart shadow`

is proved by unfolding the chart-normalized structure and then adapted into
the existing weak G8f corridor.

This is still local chart theory.  It does not construct tau preimages, does
not prove axis-offset alignment for the actual orthodox chart, does not prove
O3, and does not identify any xi zero divisor.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CHART-NORMALIZED ORTHODOX SHADOW
-- ============================================================

/-- A chart-normalized orthodox shadow source.

The normalization law is the proof-facing content of this module:
`ClassicalOffCriticalZero` is equivalent to off-axis readability in the
centered shadow.  This is weaker than constructing the actual xi chart, but
stronger than an opaque `offCriticalReadable` field because it records the
exact local chart law that future G3/G4 work must justify. -/
structure G8ChartNormalizedOrthodoxShadow
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  centeredShadow : ctx.test.base.orthodoxZero → CriticalAxisShadow
  shadowAgrees :
    ∀ z : ctx.test.base.orthodoxZero,
      centeredShadow z = ctx.test.orthodoxShadow z
  offCritical_iff_offAxis :
    ∀ z : ctx.test.base.orthodoxZero,
      ClassicalOffCriticalZero ctx.test.base z ↔
        ShadowOffAxis (centeredShadow z)
  g3ZetaChartReadout :
    ctx.test.base.transfer.completion.chart.g3ZetaBridge
  g4CompletedXiReadout :
    ctx.test.base.transfer.completion.chart.g4AnalyticContinuation
  finiteGuardrails : G8bFiniteOnlyGuardrails finiteG8bContext :=
    finiteG8bContext_guardrails

/-- In a chart-normalized source, a declared orthodox off-critical candidate is
    readable as off-axis in the centered shadow. -/
theorem g8ChartNormalized_offCritical_to_offAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    ShadowOffAxis (source.centeredShadow z) :=
  (source.offCritical_iff_offAxis z).mp hz

/-- Conversely, off-axis readability in a chart-normalized source is exactly
    the declared off-critical predicate.  This is a local chart-normalization
    fact, not a divisor theorem. -/
theorem g8ChartNormalized_offAxis_to_offCritical
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx)
    (z : ctx.test.base.orthodoxZero)
    (hOffAxis : ShadowOffAxis (source.centeredShadow z)) :
    ClassicalOffCriticalZero ctx.test.base z :=
  (source.offCritical_iff_offAxis z).mpr hOffAxis

/-- The chart-normalized source exposes the G3 zeta-chart readout guard. -/
theorem g8ChartNormalized_requires_g3ZetaBridge
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx) :
    ctx.test.base.transfer.completion.chart.g3ZetaBridge :=
  source.g3ZetaChartReadout

/-- The chart-normalized source exposes the G4 completed-xi/continuation
    readout guard. -/
theorem g8ChartNormalized_requires_g4AnalyticContinuation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx) :
    ctx.test.base.transfer.completion.chart.g4AnalyticContinuation :=
  source.g4CompletedXiReadout

/-- The chart-normalized source remains finite-only at the G8b layer. -/
theorem g8ChartNormalized_finiteOnly
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx) :
    finiteG8bContext.finiteOnly :=
  source.finiteGuardrails.left

/-- The chart-normalized source carries no xi-divisor claim from finite stages. -/
theorem g8ChartNormalized_noXiDivisorClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx) :
    finiteG8bContext.noXiDivisorClaim :=
  source.finiteGuardrails.right.left

/-- The chart-normalized source carries no analytic-completion claim from
    finite stages. -/
theorem g8ChartNormalized_noAnalyticCompletionClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  source.finiteGuardrails.right.right

-- ============================================================
-- ADAPTERS INTO THE EXISTING SHADOW-SOURCE CORRIDOR
-- ============================================================

/-- A chart-normalized source supplies the existing orthodox shadow-source
    interface. -/
def g8ChartNormalized_to_shadowSource
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx) :
    G8OrthodoxShadowSource ctx where
  centeredShadow := source.centeredShadow
  shadowAgrees := source.shadowAgrees
  offCriticalReadable := by
    intro z hz
    exact g8ChartNormalized_offCritical_to_offAxis source z hz
  g3ZetaChartReadout := source.g3ZetaChartReadout
  g4CompletedXiReadout := source.g4CompletedXiReadout
  finiteGuardrails := source.finiteGuardrails

/-- A chart-normalized source builds the explicit off-axis chart object. -/
def g8ChartNormalized_to_chart
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx) :
    G8OffAxisChartObject ctx :=
  g8OrthodoxShadowSource_to_chart
    (g8ChartNormalized_to_shadowSource source)

/-- A chart-normalized source supplies chart-shadow readability. -/
theorem g8ChartNormalized_readable
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx) :
    G8ChartShadowReadable (g8ChartNormalized_to_chart source) :=
  g8OrthodoxShadowSource_readable
    (g8ChartNormalized_to_shadowSource source)

/-- A chart-normalized source supplies the decomposed off-axis readability
    predicate. -/
theorem g8ChartNormalized_offAxisChartReadable
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx) :
    G8OffAxisChartReadable (g8ChartNormalized_to_chart source) :=
  g8OrthodoxShadowSource_offAxisChartReadable
    (g8ChartNormalized_to_shadowSource source)

/-- The chart-normalized source yields local fold readability for the weak
    pullback test. -/
theorem g8ChartNormalized_localFold
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (source : G8ChartNormalizedOrthodoxShadow ctx) :
    G8e1LocalFoldReadable ctx.test :=
  g8OrthodoxShadowSource_localFold ctx
    (g8ChartNormalized_to_shadowSource source)

/-- A declared orthodox off-critical candidate becomes off-axis in the explicit
    chart built from a chart-normalized source. -/
theorem g8ChartNormalized_offCritical_to_chartOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    G8ChartOffAxis (g8ChartNormalized_to_chart source) z :=
  g8ChartNormalized_offCritical_to_offAxis source z hz

/-- Context-level off-axis data follows from chart-normalized off-criticality. -/
theorem g8ChartNormalized_offCritical_to_contextOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    ShadowOffAxis (ctx.test.orthodoxShadow z) :=
  g8ChartOffAxis_to_context
    (g8ChartNormalized_to_chart source)
    (g8ChartNormalized_offCritical_to_chartOffAxis source z hz)

/-- The chart built from a chart-normalized source agrees with the weak test
    context. -/
theorem g8ChartNormalized_chart_agrees
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx)
    (z : ctx.test.base.orthodoxZero) :
    (g8ChartNormalized_to_chart source).centeredShadow z =
      ctx.test.orthodoxShadow z :=
  source.shadowAgrees z

/-- In a chart-normalized source, context off-axis data is also exactly the
    declared off-critical predicate.  This remains local chart vocabulary, not
    a zero-divisor statement. -/
theorem g8ChartNormalized_contextOffAxis_to_offCritical
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx)
    (z : ctx.test.base.orthodoxZero)
    (hOffAxis : ShadowOffAxis (ctx.test.orthodoxShadow z)) :
    ClassicalOffCriticalZero ctx.test.base z := by
  apply g8ChartNormalized_offAxis_to_offCritical source z
  unfold ShadowOffAxis at hOffAxis ⊢
  intro hAxis
  exact hOffAxis ((source.shadowAgrees z) ▸ hAxis)

-- ============================================================
-- NORMALIZATION FALSIFIERS
-- ============================================================

/-- A declared off-critical candidate whose normalized shadow is not off-axis. -/
structure G8ChartNormalizationFailureWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx) where
  z : ctx.test.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  notOffAxis : ¬ ShadowOffAxis (source.centeredShadow z)

/-- A chart-normalization failure refutes the normalized source. -/
theorem g8ChartNormalizationFailure_refutes_source
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8ChartNormalizedOrthodoxShadow ctx}
    (w : G8ChartNormalizationFailureWitness source) :
    False :=
  w.notOffAxis
    (g8ChartNormalized_offCritical_to_offAxis
      source w.z w.offCritical)

/-- A declared off-critical candidate accidentally classified on-axis by the
    normalized shadow. -/
structure G8ChartNormalizationOnAxisFailureWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx) where
  z : ctx.test.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  onAxis : OnCriticalAxis (source.centeredShadow z)

/-- An on-axis normalized shadow refutes off-critical readability. -/
theorem g8ChartNormalizationOnAxisFailure_refutes_source
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8ChartNormalizedOrthodoxShadow ctx}
    (w : G8ChartNormalizationOnAxisFailureWitness source) :
    False :=
  (g8ChartNormalized_offCritical_to_offAxis
    source w.z w.offCritical) w.onAxis

/-- A context-level on-axis classification refutes a chart-normalized
    off-critical candidate through the shadow-agreement field. -/
structure G8ChartNormalizationContextOnAxisFailureWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx) where
  z : ctx.test.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  onAxis : OnCriticalAxis (ctx.test.orthodoxShadow z)

/-- A context-level on-axis failure refutes the normalized source. -/
theorem g8ChartNormalizationContextOnAxisFailure_refutes_source
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8ChartNormalizedOrthodoxShadow ctx}
    (w : G8ChartNormalizationContextOnAxisFailureWitness source) :
    False := by
  have hChartAxis : OnCriticalAxis (source.centeredShadow w.z) := by
    rw [source.shadowAgrees w.z]
    exact w.onAxis
  exact
    (g8ChartNormalized_offCritical_to_offAxis
      source w.z w.offCritical) hChartAxis

/-- Off-axis data that is not recognized by the declared off-critical
    predicate.  This refutes the bidirectional chart-normalization law, but it
    is diagnostic for the local chart package rather than a divisor claim. -/
structure G8ChartNormalizationOverreadWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx) where
  z : ctx.test.base.orthodoxZero
  offAxis : ShadowOffAxis (source.centeredShadow z)
  notOffCritical : ¬ ClassicalOffCriticalZero ctx.test.base z

/-- A chart-overread witness refutes the bidirectional normalization law. -/
theorem g8ChartNormalizationOverread_refutes_source
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8ChartNormalizedOrthodoxShadow ctx}
    (w : G8ChartNormalizationOverreadWitness source) :
    False :=
  w.notOffCritical
    (g8ChartNormalized_offAxis_to_offCritical
      source w.z w.offAxis)

/-- A mismatch between the normalized source shadow and the weak test context. -/
structure G8ChartNormalizationAgreementMismatchWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8ChartNormalizedOrthodoxShadow ctx) where
  z : ctx.test.base.orthodoxZero
  mismatch :
    source.centeredShadow z ≠ ctx.test.orthodoxShadow z

/-- A chart-normalized agreement mismatch refutes the normalized source. -/
theorem g8ChartNormalizationAgreementMismatch_refutes_source
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8ChartNormalizedOrthodoxShadow ctx}
    (w : G8ChartNormalizationAgreementMismatchWitness source) :
    False :=
  w.mismatch (source.shadowAgrees w.z)

end Tau.BookIII.Bridge
