import TauLib.BookIII.Bridge.G8OrthodoxCenteredChartHygiene

/-!
# TauLib.BookIII.Bridge.G8OrthodoxShadowAxisSource

Shadow-axis source for the G8f centered chart corridor.

`G8OrthodoxCenteredChartHygiene` still allowed the orthodox critical-axis
predicate to be supplied as a separate field, together with a proof that it
agrees with the centered `CriticalAxisShadow` axis.  This module removes that
degree of freedom: the orthodox critical axis is defined directly as
`OnCriticalAxis (centeredShadow z)`.

The only remaining source law is therefore the real chart-hygiene obligation:
the declared orthodox off-critical predicate is exactly failure of the
centered shadow axis.  This is still local chart theory.  It does not prove an
analytic xi chart, does not construct tau preimages, and does not identify any
zero divisor.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- SHADOW-AXIS SOURCE
-- ============================================================

/-- Receiving-side chart source whose critical-axis predicate is definitionally
    the centered shadow axis. -/
structure G8OrthodoxShadowAxisSource
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  centeredShadow : ctx.test.base.orthodoxZero → CriticalAxisShadow
  shadowAgrees :
    ∀ z : ctx.test.base.orthodoxZero,
      centeredShadow z = ctx.test.orthodoxShadow z
  offCritical_iff_notShadowAxis :
    ∀ z : ctx.test.base.orthodoxZero,
      ClassicalOffCriticalZero ctx.test.base z ↔
        ¬ OnCriticalAxis (centeredShadow z)
  g3ZetaChartReadout :
    ctx.test.base.transfer.completion.chart.g3ZetaBridge
  g4CompletedXiReadout :
    ctx.test.base.transfer.completion.chart.g4AnalyticContinuation
  finiteGuardrails : G8bFiniteOnlyGuardrails finiteG8bContext :=
    finiteG8bContext_guardrails

/-- The shadow-axis source exposes the G3 zeta-chart readout guard. -/
theorem g8OrthodoxShadowAxisSource_requires_g3ZetaBridge
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    ctx.test.base.transfer.completion.chart.g3ZetaBridge :=
  source.g3ZetaChartReadout

/-- The shadow-axis source exposes the G4 completed-xi/continuation readout
    guard. -/
theorem g8OrthodoxShadowAxisSource_requires_g4AnalyticContinuation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    ctx.test.base.transfer.completion.chart.g4AnalyticContinuation :=
  source.g4CompletedXiReadout

/-- The shadow-axis source remains finite-only at the G8b layer. -/
theorem g8OrthodoxShadowAxisSource_finiteOnly
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    finiteG8bContext.finiteOnly :=
  source.finiteGuardrails.left

/-- The shadow-axis source carries no xi-divisor claim from finite stages. -/
theorem g8OrthodoxShadowAxisSource_noXiDivisorClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    finiteG8bContext.noXiDivisorClaim :=
  source.finiteGuardrails.right.left

/-- The shadow-axis source carries no analytic-completion claim from finite
    stages. -/
theorem g8OrthodoxShadowAxisSource_noAnalyticCompletionClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  source.finiteGuardrails.right.right

-- ============================================================
-- DIRECT SHADOW-AXIS THEOREMS
-- ============================================================

/-- Off-criticality is exactly failure of the centered shadow axis. -/
theorem g8OrthodoxShadowAxisSource_offCritical_iff_offAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero) :
    ClassicalOffCriticalZero ctx.test.base z ↔
      ShadowOffAxis (source.centeredShadow z) :=
  source.offCritical_iff_notShadowAxis z

/-- An orthodox off-critical candidate is readable as off-axis in the centered
    shadow. -/
theorem g8OrthodoxShadowAxisSource_offCritical_to_offAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    ShadowOffAxis (source.centeredShadow z) :=
  (g8OrthodoxShadowAxisSource_offCritical_iff_offAxis source z).mp hz

/-- Off-axis centered-shadow data reflects to the local off-critical predicate.
    This remains chart vocabulary, not divisor transfer. -/
theorem g8OrthodoxShadowAxisSource_offAxis_to_offCritical
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (hOffAxis : ShadowOffAxis (source.centeredShadow z)) :
    ClassicalOffCriticalZero ctx.test.base z :=
  (g8OrthodoxShadowAxisSource_offCritical_iff_offAxis source z).mpr hOffAxis

/-- Context-level off-axis data follows from a shadow-axis source. -/
theorem g8OrthodoxShadowAxisSource_offCritical_to_contextOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    ShadowOffAxis (ctx.test.orthodoxShadow z) := by
  unfold ShadowOffAxis at *
  intro hAxis
  exact
    (g8OrthodoxShadowAxisSource_offCritical_to_offAxis source z hz)
      ((source.shadowAgrees z) ▸ hAxis)

-- ============================================================
-- ADAPTERS INTO THE EXISTING CORRIDOR
-- ============================================================

/-- A shadow-axis source supplies centered chart hygiene, with the axis
    agreement reduced to definitional equality. -/
def g8OrthodoxShadowAxisSource_to_centeredHygiene
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    G8OrthodoxCenteredChartHygiene ctx where
  centeredShadow := source.centeredShadow
  shadowAgrees := source.shadowAgrees
  orthodoxCriticalAxis :=
    fun z => OnCriticalAxis (source.centeredShadow z)
  criticalAxis_iff_shadowAxis := by
    intro z
    exact Iff.rfl
  offCritical_iff_notCriticalAxis :=
    source.offCritical_iff_notShadowAxis
  g3ZetaChartReadout := source.g3ZetaChartReadout
  g4CompletedXiReadout := source.g4CompletedXiReadout
  finiteGuardrails := source.finiteGuardrails

/-- A shadow-axis source supplies the chart-normalized source package. -/
def g8OrthodoxShadowAxisSource_to_chartNormalized
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    G8ChartNormalizedOrthodoxShadow ctx :=
  g8CenteredChartHygiene_to_chartNormalized
    (g8OrthodoxShadowAxisSource_to_centeredHygiene source)

/-- A shadow-axis source supplies the orthodox shadow-source interface. -/
def g8OrthodoxShadowAxisSource_to_shadowSource
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    G8OrthodoxShadowSource ctx :=
  g8CenteredChartHygiene_to_shadowSource
    (g8OrthodoxShadowAxisSource_to_centeredHygiene source)

/-- A shadow-axis source builds the explicit off-axis chart object. -/
def g8OrthodoxShadowAxisSource_to_chart
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) :
    G8OffAxisChartObject ctx :=
  g8CenteredChartHygiene_to_chart
    (g8OrthodoxShadowAxisSource_to_centeredHygiene source)

/-- A shadow-axis source supplies local fold readability. -/
theorem g8OrthodoxShadowAxisSource_localFold
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (source : G8OrthodoxShadowAxisSource ctx) :
    G8e1LocalFoldReadable ctx.test :=
  g8CenteredChartHygiene_localFold ctx
    (g8OrthodoxShadowAxisSource_to_centeredHygiene source)

/-- A declared orthodox off-critical candidate becomes off-axis in the explicit
    chart built from a shadow-axis source. -/
theorem g8OrthodoxShadowAxisSource_offCritical_to_chartOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z :=
  g8CenteredChartHygiene_offCritical_to_chartOffAxis
    (g8OrthodoxShadowAxisSource_to_centeredHygiene source) z hz

/-- The explicit chart built from a shadow-axis source agrees with the weak
    test context. -/
theorem g8OrthodoxShadowAxisSource_chart_agrees
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (z : ctx.test.base.orthodoxZero) :
    (g8OrthodoxShadowAxisSource_to_chart source).centeredShadow z =
      ctx.test.orthodoxShadow z :=
  source.shadowAgrees z

-- ============================================================
-- SOURCE-LAW FALSIFIERS AND DIAGNOSTICS
-- ============================================================

/-- A declared off-critical candidate that remains on the centered shadow
    axis. -/
structure G8OrthodoxShadowAxisOffCriticalOnAxisWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  shadowAxis : OnCriticalAxis (source.centeredShadow z)

/-- A shadow-axis/on-axis witness refutes the shadow-axis source law. -/
theorem g8OrthodoxShadowAxisOffCriticalOnAxis_refutes_source
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8OrthodoxShadowAxisOffCriticalOnAxisWitness source) :
    False :=
  (g8OrthodoxShadowAxisSource_offCritical_to_offAxis
    source w.z w.offCritical) w.shadowAxis

/-- Centered-shadow off-axis data that is not recognized as off-critical. -/
structure G8OrthodoxShadowAxisOffAxisNotOffCriticalWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  offAxis : ShadowOffAxis (source.centeredShadow z)
  notOffCritical : ¬ ClassicalOffCriticalZero ctx.test.base z

/-- Off-axis-but-not-off-critical data refutes the shadow-axis source law. -/
theorem g8OrthodoxShadowAxisOffAxisNotOffCritical_refutes_source
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8OrthodoxShadowAxisOffAxisNotOffCriticalWitness source) :
    False :=
  w.notOffCritical
    (g8OrthodoxShadowAxisSource_offAxis_to_offCritical
      source w.z w.offAxis)

/-- A mismatch between the shadow-axis source and the weak test context. -/
structure G8OrthodoxShadowAxisAgreementMismatchWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  mismatch :
    source.centeredShadow z ≠ ctx.test.orthodoxShadow z

/-- A shadow-axis source/context mismatch refutes the source. -/
theorem g8OrthodoxShadowAxisAgreementMismatch_refutes_source
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8OrthodoxShadowAxisAgreementMismatchWitness source) :
    False :=
  w.mismatch (source.shadowAgrees w.z)

/-- Height/provenance differences remain diagnostic at this shadow-axis source
    layer.  They matter only if they also change the axis predicate. -/
structure G8OrthodoxShadowAxisHeightDiagnostic
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  referenceHeight : Nat
  heightDiffers :
    (source.centeredShadow z).heightWitness ≠ referenceHeight

/-- A height diagnostic is not by itself a localization refutation. -/
theorem g8OrthodoxShadowAxisHeightDiagnostic_not_refutation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (_w : G8OrthodoxShadowAxisHeightDiagnostic source) :
    True :=
  trivial

end Tau.BookIII.Bridge
