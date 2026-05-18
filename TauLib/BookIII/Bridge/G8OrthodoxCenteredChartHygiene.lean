import TauLib.BookIII.Bridge.G8OrthodoxShadowReadability

/-!
# TauLib.BookIII.Bridge.G8OrthodoxCenteredChartHygiene

Centered chart hygiene for the first G8f receiving-side arrow.

The preceding readability module packaged the local law
`ClassicalOffCriticalZero ↔ ShadowOffAxis centeredShadow`.  This module splits
that law into two smaller chart-hygiene facts:

* the orthodox critical-axis predicate agrees with the centered shadow axis;
* the orthodox off-critical predicate is exactly failure of that critical-axis
  predicate.

Together they prove the same local off-axis readability theorem, but with the
chart axis itself exposed as a proof-facing object.  This is chart hygiene
only: no tau preimage is constructed, no O3 or analytic-completion theorem is
proved, and no xi divisor is identified.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CENTERED CHART HYGIENE
-- ============================================================

/-- Centered receiving-side chart hygiene for the weak G8f corridor.

`orthodoxCriticalAxis` is the receiving-side axis predicate at the current
chart-theory layer.  The two equivalence fields say that this predicate agrees
with the `CriticalAxisShadow` axis and that the declared orthodox
off-critical predicate is exactly being outside that axis.

The `shadowAgrees` field ties the local centered shadow back to the existing
weak pullback test context, allowing this record to feed the already-built
chart corridor without changing any downstream interfaces. -/
structure G8OrthodoxCenteredChartHygiene
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  centeredShadow : ctx.test.base.orthodoxZero → CriticalAxisShadow
  shadowAgrees :
    ∀ z : ctx.test.base.orthodoxZero,
      centeredShadow z = ctx.test.orthodoxShadow z
  orthodoxCriticalAxis : ctx.test.base.orthodoxZero → Prop
  criticalAxis_iff_shadowAxis :
    ∀ z : ctx.test.base.orthodoxZero,
      orthodoxCriticalAxis z ↔ OnCriticalAxis (centeredShadow z)
  offCritical_iff_notCriticalAxis :
    ∀ z : ctx.test.base.orthodoxZero,
      ClassicalOffCriticalZero ctx.test.base z ↔
        ¬ orthodoxCriticalAxis z
  g3ZetaChartReadout :
    ctx.test.base.transfer.completion.chart.g3ZetaBridge
  g4CompletedXiReadout :
    ctx.test.base.transfer.completion.chart.g4AnalyticContinuation
  finiteGuardrails : G8bFiniteOnlyGuardrails finiteG8bContext :=
    finiteG8bContext_guardrails

/-- A chart-hygiene source exposes the G3 zeta-chart readout guard. -/
theorem g8CenteredChartHygiene_requires_g3ZetaBridge
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) :
    ctx.test.base.transfer.completion.chart.g3ZetaBridge :=
  hygiene.g3ZetaChartReadout

/-- A chart-hygiene source exposes the G4 completed-xi/continuation readout
    guard. -/
theorem g8CenteredChartHygiene_requires_g4AnalyticContinuation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) :
    ctx.test.base.transfer.completion.chart.g4AnalyticContinuation :=
  hygiene.g4CompletedXiReadout

/-- A chart-hygiene source remains finite-only at the G8b layer. -/
theorem g8CenteredChartHygiene_finiteOnly
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) :
    finiteG8bContext.finiteOnly :=
  hygiene.finiteGuardrails.left

/-- A chart-hygiene source carries no xi-divisor claim from finite stages. -/
theorem g8CenteredChartHygiene_noXiDivisorClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) :
    finiteG8bContext.noXiDivisorClaim :=
  hygiene.finiteGuardrails.right.left

/-- A chart-hygiene source carries no analytic-completion claim from finite
    stages. -/
theorem g8CenteredChartHygiene_noAnalyticCompletionClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  hygiene.finiteGuardrails.right.right

-- ============================================================
-- AXIS AND OFF-AXIS THEOREMS
-- ============================================================

/-- The declared orthodox critical-axis predicate implies the centered shadow
    axis predicate. -/
theorem g8CenteredChartHygiene_criticalAxis_to_shadowAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx)
    (z : ctx.test.base.orthodoxZero)
    (hAxis : hygiene.orthodoxCriticalAxis z) :
    OnCriticalAxis (hygiene.centeredShadow z) :=
  (hygiene.criticalAxis_iff_shadowAxis z).mp hAxis

/-- The centered shadow axis predicate reflects back to the declared orthodox
    critical-axis predicate. -/
theorem g8CenteredChartHygiene_shadowAxis_to_criticalAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx)
    (z : ctx.test.base.orthodoxZero)
    (hAxis : OnCriticalAxis (hygiene.centeredShadow z)) :
    hygiene.orthodoxCriticalAxis z :=
  (hygiene.criticalAxis_iff_shadowAxis z).mpr hAxis

/-- Off-criticality is failure of the declared orthodox critical-axis
    predicate. -/
theorem g8CenteredChartHygiene_offCritical_to_notCriticalAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    ¬ hygiene.orthodoxCriticalAxis z :=
  (hygiene.offCritical_iff_notCriticalAxis z).mp hz

/-- Failure of the declared critical-axis predicate is exactly the local
    off-critical predicate. -/
theorem g8CenteredChartHygiene_notCriticalAxis_to_offCritical
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx)
    (z : ctx.test.base.orthodoxZero)
    (hNotAxis : ¬ hygiene.orthodoxCriticalAxis z) :
    ClassicalOffCriticalZero ctx.test.base z :=
  (hygiene.offCritical_iff_notCriticalAxis z).mpr hNotAxis

/-- The chart-hygiene package proves the first local arrow: an orthodox
    off-critical candidate is readable as off-axis in the centered shadow. -/
theorem g8CenteredChartHygiene_offCritical_to_offAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    ShadowOffAxis (hygiene.centeredShadow z) := by
  intro hShadowAxis
  exact
    (g8CenteredChartHygiene_offCritical_to_notCriticalAxis
      hygiene z hz)
      (g8CenteredChartHygiene_shadowAxis_to_criticalAxis
        hygiene z hShadowAxis)

/-- Off-axis readability in the centered shadow reflects back to the declared
    off-critical predicate.  This remains chart vocabulary, not divisor
    transfer. -/
theorem g8CenteredChartHygiene_offAxis_to_offCritical
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx)
    (z : ctx.test.base.orthodoxZero)
    (hOffAxis : ShadowOffAxis (hygiene.centeredShadow z)) :
    ClassicalOffCriticalZero ctx.test.base z := by
  apply g8CenteredChartHygiene_notCriticalAxis_to_offCritical hygiene z
  intro hAxis
  exact hOffAxis
    (g8CenteredChartHygiene_criticalAxis_to_shadowAxis
      hygiene z hAxis)

/-- Chart hygiene yields the chart-normalized off-critical/off-axis law. -/
theorem g8CenteredChartHygiene_offCritical_iff_offAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx)
    (z : ctx.test.base.orthodoxZero) :
    ClassicalOffCriticalZero ctx.test.base z ↔
      ShadowOffAxis (hygiene.centeredShadow z) where
  mp := g8CenteredChartHygiene_offCritical_to_offAxis hygiene z
  mpr := g8CenteredChartHygiene_offAxis_to_offCritical hygiene z

-- ============================================================
-- ADAPTERS INTO THE EXISTING CORRIDOR
-- ============================================================

/-- Centered chart hygiene supplies the chart-normalized source package. -/
def g8CenteredChartHygiene_to_chartNormalized
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) :
    G8ChartNormalizedOrthodoxShadow ctx where
  centeredShadow := hygiene.centeredShadow
  shadowAgrees := hygiene.shadowAgrees
  offCritical_iff_offAxis :=
    g8CenteredChartHygiene_offCritical_iff_offAxis hygiene
  g3ZetaChartReadout := hygiene.g3ZetaChartReadout
  g4CompletedXiReadout := hygiene.g4CompletedXiReadout
  finiteGuardrails := hygiene.finiteGuardrails

/-- Centered chart hygiene supplies the orthodox shadow-source interface. -/
def g8CenteredChartHygiene_to_shadowSource
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) :
    G8OrthodoxShadowSource ctx :=
  g8ChartNormalized_to_shadowSource
    (g8CenteredChartHygiene_to_chartNormalized hygiene)

/-- Centered chart hygiene builds the explicit off-axis chart object. -/
def g8CenteredChartHygiene_to_chart
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) :
    G8OffAxisChartObject ctx :=
  g8ChartNormalized_to_chart
    (g8CenteredChartHygiene_to_chartNormalized hygiene)

/-- Centered chart hygiene supplies chart-shadow readability. -/
theorem g8CenteredChartHygiene_readable
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) :
    G8ChartShadowReadable (g8CenteredChartHygiene_to_chart hygiene) :=
  g8ChartNormalized_readable
    (g8CenteredChartHygiene_to_chartNormalized hygiene)

/-- Centered chart hygiene supplies decomposed off-axis readability. -/
theorem g8CenteredChartHygiene_offAxisChartReadable
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) :
    G8OffAxisChartReadable (g8CenteredChartHygiene_to_chart hygiene) :=
  g8ChartNormalized_offAxisChartReadable
    (g8CenteredChartHygiene_to_chartNormalized hygiene)

/-- Centered chart hygiene yields local fold readability for the weak pullback
    test. -/
theorem g8CenteredChartHygiene_localFold
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) :
    G8e1LocalFoldReadable ctx.test :=
  g8ChartNormalized_localFold ctx
    (g8CenteredChartHygiene_to_chartNormalized hygiene)

/-- A declared orthodox off-critical candidate becomes off-axis in the explicit
    chart built from centered chart hygiene. -/
theorem g8CenteredChartHygiene_offCritical_to_chartOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    G8ChartOffAxis (g8CenteredChartHygiene_to_chart hygiene) z :=
  g8ChartNormalized_offCritical_to_chartOffAxis
    (g8CenteredChartHygiene_to_chartNormalized hygiene) z hz

/-- Context-level off-axis data follows from centered chart hygiene. -/
theorem g8CenteredChartHygiene_offCritical_to_contextOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    ShadowOffAxis (ctx.test.orthodoxShadow z) :=
  g8ChartNormalized_offCritical_to_contextOffAxis
    (g8CenteredChartHygiene_to_chartNormalized hygiene) z hz

/-- The chart built from centered chart hygiene agrees with the weak test
    context. -/
theorem g8CenteredChartHygiene_chart_agrees
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx)
    (z : ctx.test.base.orthodoxZero) :
    (g8CenteredChartHygiene_to_chart hygiene).centeredShadow z =
      ctx.test.orthodoxShadow z :=
  hygiene.shadowAgrees z

-- ============================================================
-- HYGIENE FALSIFIERS AND DIAGNOSTICS
-- ============================================================

/-- The declared critical-axis predicate holds but the centered shadow is not
    on-axis. -/
structure G8OrthodoxCriticalAxisShadowMismatchWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) where
  z : ctx.test.base.orthodoxZero
  criticalAxis : hygiene.orthodoxCriticalAxis z
  notShadowAxis : ¬ OnCriticalAxis (hygiene.centeredShadow z)

/-- A critical-axis/shadow-axis mismatch refutes centered chart hygiene. -/
theorem g8OrthodoxCriticalAxisShadowMismatch_refutes_hygiene
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {hygiene : G8OrthodoxCenteredChartHygiene ctx}
    (w : G8OrthodoxCriticalAxisShadowMismatchWitness hygiene) :
    False :=
  w.notShadowAxis
    (g8CenteredChartHygiene_criticalAxis_to_shadowAxis
      hygiene w.z w.criticalAxis)

/-- The centered shadow is on-axis but the declared critical-axis predicate
    fails. -/
structure G8OrthodoxShadowAxisCriticalAxisMismatchWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) where
  z : ctx.test.base.orthodoxZero
  shadowAxis : OnCriticalAxis (hygiene.centeredShadow z)
  notCriticalAxis : ¬ hygiene.orthodoxCriticalAxis z

/-- A shadow-axis/critical-axis mismatch refutes centered chart hygiene. -/
theorem g8OrthodoxShadowAxisCriticalAxisMismatch_refutes_hygiene
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {hygiene : G8OrthodoxCenteredChartHygiene ctx}
    (w : G8OrthodoxShadowAxisCriticalAxisMismatchWitness hygiene) :
    False :=
  w.notCriticalAxis
    (g8CenteredChartHygiene_shadowAxis_to_criticalAxis
      hygiene w.z w.shadowAxis)

/-- A declared off-critical candidate that is still on the declared critical
    axis. -/
structure G8OrthodoxOffCriticalCriticalAxisMismatchWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) where
  z : ctx.test.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  criticalAxis : hygiene.orthodoxCriticalAxis z

/-- An off-critical/critical-axis mismatch refutes centered chart hygiene. -/
theorem g8OrthodoxOffCriticalCriticalAxisMismatch_refutes_hygiene
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {hygiene : G8OrthodoxCenteredChartHygiene ctx}
    (w : G8OrthodoxOffCriticalCriticalAxisMismatchWitness hygiene) :
    False :=
  (g8CenteredChartHygiene_offCritical_to_notCriticalAxis
    hygiene w.z w.offCritical) w.criticalAxis

/-- A point outside the declared critical axis that is not recognized as
    off-critical. -/
structure G8OrthodoxNotCriticalAxisOffCriticalMismatchWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) where
  z : ctx.test.base.orthodoxZero
  notCriticalAxis : ¬ hygiene.orthodoxCriticalAxis z
  notOffCritical : ¬ ClassicalOffCriticalZero ctx.test.base z

/-- A not-critical-axis/off-critical mismatch refutes centered chart hygiene. -/
theorem g8OrthodoxNotCriticalAxisOffCriticalMismatch_refutes_hygiene
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {hygiene : G8OrthodoxCenteredChartHygiene ctx}
    (w : G8OrthodoxNotCriticalAxisOffCriticalMismatchWitness hygiene) :
    False :=
  w.notOffCritical
    (g8CenteredChartHygiene_notCriticalAxis_to_offCritical
      hygiene w.z w.notCriticalAxis)

/-- A declared off-critical candidate accidentally classified on-axis by the
    centered shadow. -/
structure G8OrthodoxOffCriticalShadowAxisWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) where
  z : ctx.test.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  shadowAxis : OnCriticalAxis (hygiene.centeredShadow z)

/-- An off-critical candidate classified on the centered shadow axis refutes
    centered chart hygiene. -/
theorem g8OrthodoxOffCriticalShadowAxis_refutes_hygiene
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {hygiene : G8OrthodoxCenteredChartHygiene ctx}
    (w : G8OrthodoxOffCriticalShadowAxisWitness hygiene) :
    False :=
  (g8CenteredChartHygiene_offCritical_to_offAxis
    hygiene w.z w.offCritical) w.shadowAxis

/-- Height/provenance mismatches are diagnostic at this localization layer.
    They do not refute off-axis localization unless they also change the
    axis predicate. -/
structure G8OrthodoxHeightProvenanceDiagnostic
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (hygiene : G8OrthodoxCenteredChartHygiene ctx) where
  z : ctx.test.base.orthodoxZero
  referenceHeight : Nat
  heightDiffers :
    (hygiene.centeredShadow z).heightWitness ≠ referenceHeight

/-- A height/provenance diagnostic is not, by itself, a localization
    refutation. -/
theorem g8OrthodoxHeightProvenanceDiagnostic_not_refutation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {hygiene : G8OrthodoxCenteredChartHygiene ctx}
    (_w : G8OrthodoxHeightProvenanceDiagnostic hygiene) :
    True :=
  trivial

end Tau.BookIII.Bridge
