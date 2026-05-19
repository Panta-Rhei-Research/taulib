import TauLib.BookIII.Bridge.G8ActualXiZetaNoGhostDecomposition

/-!
# TauLib.BookIII.Bridge.G8ActualXiZetaThinSource

Thin actual `xi`/`zeta` chart source for the G8f off-axis corridor.

The older actual-source context is intentionally compatible with the existing
`OffCriticalZeroPullbackContext` stack, so it carries a full
`G8dZeroDivisorTransferContext`.  The weak G8f localization route does not
need that whole transfer package to state its chart hygiene and pointwise
tau-preimage contracts.  It only needs:

* the orthodox `xi` carrier and centered shadow;
* G3/G4 readout guards from a zeta-as-chart context;
* a tau-witness carrier and normal-form map;
* the binary normalized axis relation.

This module exposes that thinner surface and provides an adapter back to the
legacy actual source only at the boundary where existing corridor APIs still
expect it.  No O3 theorem, analytic-completion uniqueness, zero-divisor
transfer, tau purity, or RH theorem is proved here.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- THIN ACTUAL XI/ZETA SOURCE
-- ============================================================

/-- Thin actual `xi`/`zeta` source for the weak G8f chart route.

Unlike `G8ActualXiZetaSourceContext`, this context records only the
zeta-as-chart readout surface and the tau witness/normal-form map.  It does
not carry a full G8d zero-divisor-transfer context. -/
structure G8ActualXiZetaThinSourceContext where
  chart : ZetaAsCoordinateChartContext
  tauWitness : Type 2
  tauNormalForm : tauWitness → BoundaryNF
  g3ZetaChartReadout : chart.g3ZetaBridge
  g4CompletedXiReadout : chart.g4AnalyticContinuation
  status : G8OffCriticalExclusionStatus := .openObligation

/-- The thin source uses the actual Mathlib-backed `xi` zero carrier. -/
abbrev G8ActualXiZetaThinOrthodoxZero
    (_source : G8ActualXiZetaThinSourceContext) : Type 2 :=
  OrthodoxXiZeroCarrier

/-- Thin off-critical predicate: the actual `xi` zero is off the critical
    line in the receiving-side chart. -/
def G8ActualXiZetaThinOffCritical
    (_source : G8ActualXiZetaThinSourceContext)
    (z : OrthodoxXiZeroCarrier) : Prop :=
  OrthodoxXiCarrierOffCritical z

/-- Thin centered shadow: the actual centered `xi` shadow. -/
def g8ActualXiZetaThinCenteredShadow
    (_source : G8ActualXiZetaThinSourceContext)
    (z : OrthodoxXiZeroCarrier) : CriticalAxisShadow :=
  orthodoxXiCarrierCenteredShadow z

/-- Thin off-axis readability for the actual centered `xi` shadow. -/
def G8ActualXiZetaThinChartOffAxis
    (source : G8ActualXiZetaThinSourceContext)
    (z : OrthodoxXiZeroCarrier) : Prop :=
  ShadowOffAxis (g8ActualXiZetaThinCenteredShadow source z)

/-- In the thin source, actual off-criticality is exactly off-axis chart
    readability. -/
theorem g8ActualXiZetaThin_offCritical_iff_chartOffAxis
    (source : G8ActualXiZetaThinSourceContext)
    (z : OrthodoxXiZeroCarrier) :
    G8ActualXiZetaThinOffCritical source z ↔
      G8ActualXiZetaThinChartOffAxis source z := by
  exact orthodoxXiCarrierOffCritical_iff_shadowOffAxis z

/-- The thin source exposes the G3 zeta-chart readout guard. -/
theorem g8ActualXiZetaThin_requires_g3ZetaBridge
    (source : G8ActualXiZetaThinSourceContext) :
    source.chart.g3ZetaBridge :=
  source.g3ZetaChartReadout

/-- The thin source exposes the G4 completed-`xi` readout guard. -/
theorem g8ActualXiZetaThin_requires_g4AnalyticContinuation
    (source : G8ActualXiZetaThinSourceContext) :
    source.chart.g4AnalyticContinuation :=
  source.g4CompletedXiReadout

-- ============================================================
-- THIN NORMALIZED AXIS RELATION
-- ============================================================

/-- Thin normalized orthodox/tau relation.

This is the localization-bearing relation stripped of the legacy pullback
context: compare the binary receiving-side axis class with the tau
prime-polarity axis offset. -/
def G8ActualXiZetaThinNormalizedAxisRelated
    (source : G8ActualXiZetaThinSourceContext)
    (z : OrthodoxXiZeroCarrier)
    (w : source.tauWitness) : Prop :=
  normalizedAxisOffset (g8ActualXiZetaThinCenteredShadow source z) =
    primePolarityAxisOffset (source.tauNormalForm w)

/-- A thin related preimage for an actual off-axis `xi` shadow. -/
def G8ActualXiZetaThinRelatedTauCriticalPreimage
    (source : G8ActualXiZetaThinSourceContext)
    (z : OrthodoxXiZeroCarrier)
    (w : source.tauWitness) : Prop :=
  G8ActualXiZetaThinNormalizedAxisRelated source z w ∧
    TauCriticalImbalance (source.tauNormalForm w)

/-- Thin pointwise tau critical-imbalance preimages exist for every actual
    off-axis `xi` chart shadow. -/
def G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist
    (source : G8ActualXiZetaThinSourceContext) : Prop :=
  ∀ z : OrthodoxXiZeroCarrier,
    G8ActualXiZetaThinChartOffAxis source z →
      ∃ w : source.tauWitness,
        G8ActualXiZetaThinRelatedTauCriticalPreimage source z w

/-- A thin normalized-related preimage over an off-axis shadow has unit tau
    prime-polarity axis class. -/
theorem g8ActualXiZetaThinRelated_tauUnit
    {source : G8ActualXiZetaThinSourceContext}
    {z : OrthodoxXiZeroCarrier}
    {w : source.tauWitness}
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z)
    (hRel : G8ActualXiZetaThinNormalizedAxisRelated source z w) :
    primePolarityAxisOffset (source.tauNormalForm w) = 1 := by
  have hNorm :
      normalizedAxisOffset
          (g8ActualXiZetaThinCenteredShadow source z) = 1 :=
    normalizedAxisOffset_eq_one_of_offAxis hOffAxis
  rw [← hRel]
  exact hNorm

/-- A thin related tau critical preimage carries tau B/C imbalance. -/
theorem g8ActualXiZetaThinRelatedTauCriticalPreimage_bcImbalance
    {source : G8ActualXiZetaThinSourceContext}
    {z : OrthodoxXiZeroCarrier}
    {w : source.tauWitness}
    (hPre :
      G8ActualXiZetaThinRelatedTauCriticalPreimage source z w) :
    TauBCImbalance (source.tauNormalForm w) :=
  (tauCriticalImbalance_iff_bcImbalance
    (source.tauNormalForm w)).mp hPre.right

-- ============================================================
-- LEGACY SOURCE ADAPTER
-- ============================================================

/-- Boundary adapter from the thin actual source to the legacy actual source.

The full G8d transfer stack is required only when existing corridor APIs ask
for an `OffCriticalZeroPullbackContext`.  The `chartAgreement` field states
that the legacy transfer uses the same receiving chart as the thin source. -/
def g8ActualXiZetaThin_to_fullSource
    (source : G8ActualXiZetaThinSourceContext)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart) :
    G8ActualXiZetaSourceContext where
  transfer := transfer
  tauWitness := source.tauWitness
  tauNormalForm := source.tauNormalForm
  g3ZetaChartReadout := by
    rw [chartAgreement]
    exact source.g3ZetaChartReadout
  g4CompletedXiReadout := by
    rw [chartAgreement]
    exact source.g4CompletedXiReadout
  status := source.status

/-- Full-source off-axis readability reflects to the thin off-axis predicate. -/
theorem g8ActualXiZetaThin_fullOffAxis_to_thinOffAxis
    (source : G8ActualXiZetaThinSourceContext)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ChartOffAxis
        (g8ActualXiZeta_chart
          (g8ActualXiZetaThin_to_fullSource
            source transfer chartAgreement)) z) :
    G8ActualXiZetaThinChartOffAxis source z := by
  have hCtx :
      ShadowOffAxis
        ((g8ActualXiZeta_weak
          (g8ActualXiZetaThin_to_fullSource
            source transfer chartAgreement)).test.orthodoxShadow z) :=
    g8ChartOffAxis_to_context
      (g8ActualXiZeta_chart
        (g8ActualXiZetaThin_to_fullSource
          source transfer chartAgreement)) hOffAxis
  simpa [
    G8ActualXiZetaThinChartOffAxis,
    g8ActualXiZetaThinCenteredShadow,
    g8ActualXiZeta_weak,
    g8ActualXiZetaThin_to_fullSource
  ] using hCtx

/-- Thin pointwise preimages supply the legacy actual-source pointwise
    preimage contract after thickening. -/
theorem g8ActualXiZetaThinPointwise_to_fullPointwise
    (source : G8ActualXiZetaThinSourceContext)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart)
    (hPointwise :
      G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist source) :
    G8ActualXiZetaPointwiseTauImbalancePreimagesExist
      (g8ActualXiZetaThin_to_fullSource
        source transfer chartAgreement) := by
  intro z hOffAxis
  have hThinOffAxis :
      G8ActualXiZetaThinChartOffAxis source z :=
    g8ActualXiZetaThin_fullOffAxis_to_thinOffAxis
      source transfer chartAgreement z hOffAxis
  obtain ⟨w, hPre⟩ := hPointwise z hThinOffAxis
  exact
    ⟨w,
      ⟨by
          unfold G8OrthodoxTauNormalizedAxisRelated
          simpa [
            G8ActualXiZetaThinNormalizedAxisRelated,
            g8ActualXiZetaThinCenteredShadow,
            g8ActualXiZeta_shadowAxisSource,
            g8ActualXiZetaThin_to_fullSource
          ] using hPre.left,
        by
          simpa [g8ActualXiZetaThin_to_fullSource] using hPre.right⟩⟩

end Tau.BookIII.Bridge
