import TauLib.BookIII.Bridge.G8OrthodoxShadowAxisSource

/-!
# TauLib.BookIII.Bridge.G8OrthodoxPrimePolarityAxisPullback

Orthodox shadow-axis source plugged into the prime-polarity axis-offset
pullback.

The previous modules separated the two halves of the local chart theory:

* `G8OrthodoxShadowAxisSource` proves that an orthodox off-critical candidate
  is exactly a centered shadow that is not on the shadow axis;
* `G8PrimePolarityAxisOffsetAlignment` proves that the tau prime-polarity
  axis offset is zero exactly at B/C balance.

This module connects those two theorem-backed pieces.  Once a declared chart
relation has tau preimages and aligns only the axis-offset coordinate, an
orthodox off-critical candidate with a related tau preimage must carry tau
B/C imbalance, hence tau critical imbalance.  This is still local chart
theory: it does not construct the analytic xi chart, prove O3, classify
zero divisors, or close the global proof target.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- ORTHODOX SOURCE + PRIME-POLARITY AXIS PULLBACK CONTEXT
-- ============================================================

/-- Prime-polarity axis pullback context built from an orthodox shadow-axis
    source.

The hard fields remain explicit:
* related off-axis shadows must have tau preimages;
* the relation must align the localization-bearing axis-offset coordinate;
* tau imbalance must realize the declared tau witness;
* off-axis chart-only ghosts must be excluded.
-/
structure G8OrthodoxPrimePolarityAxisPullbackContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  source : G8OrthodoxShadowAxisSource ctx
  shadowTauRelated :
    G8OffAxisChartRelation
      (g8OrthodoxShadowAxisSource_to_chart source)
  offAxisHasTauPreimage :
    G8OffAxisTauPreimageExists
      (g8OrthodoxShadowAxisSource_to_chart source)
      shadowTauRelated
  axisOffsetAligned :
    G8PrimePolarityAxisOffsetAlignment
      (g8OrthodoxShadowAxisSource_to_chart source)
      shadowTauRelated
  tauWitness :
    G8OffAxisTauWitnessRealization
      (g8OrthodoxShadowAxisSource_to_chart source)
  offAxisGuard :
    G8OffAxisChartOnlyGhostGuard
      (g8OrthodoxShadowAxisSource_to_chart source)

/-- The explicit chart object induced by the orthodox source. -/
def g8OrthodoxPrimePolarityAxisPullback_chart
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx) :
    G8OffAxisChartObject ctx :=
  g8OrthodoxShadowAxisSource_to_chart pull.source

/-- Consume the orthodox-source pullback context as the existing
    axis-offset construction context. -/
def g8OrthodoxPrimePolarityAxisPullback_to_axisOffsetContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx) :
    G8PrimePolarityAxisOffsetConstructionContext ctx where
  chart := g8OrthodoxPrimePolarityAxisPullback_chart pull
  shadowTauRelated := pull.shadowTauRelated
  offAxisHasTauPreimage := pull.offAxisHasTauPreimage
  axisOffsetAligned := pull.axisOffsetAligned
  tauWitness := pull.tauWitness
  offAxisGuard := pull.offAxisGuard

-- ============================================================
-- SOURCE AND GUARDRAIL SELECTORS
-- ============================================================

/-- The pullback context inherits the G3 zeta-chart readout guard from its
    orthodox source. -/
theorem g8OrthodoxPrimePolarityAxisPullback_requires_g3ZetaBridge
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx) :
    ctx.test.base.transfer.completion.chart.g3ZetaBridge :=
  g8OrthodoxShadowAxisSource_requires_g3ZetaBridge pull.source

/-- The pullback context inherits the G4 continuation/readout guard from its
    orthodox source. -/
theorem
    g8OrthodoxPrimePolarityAxisPullback_requires_g4AnalyticContinuation
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx) :
    ctx.test.base.transfer.completion.chart.g4AnalyticContinuation :=
  g8OrthodoxShadowAxisSource_requires_g4AnalyticContinuation pull.source

/-- The pullback context keeps G8b finite support finite-only. -/
theorem g8OrthodoxPrimePolarityAxisPullback_finiteOnly
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx) :
    finiteG8bContext.finiteOnly :=
  g8OrthodoxShadowAxisSource_finiteOnly pull.source

/-- The pullback context carries no xi-divisor claim from finite stages. -/
theorem g8OrthodoxPrimePolarityAxisPullback_noXiDivisorClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx) :
    finiteG8bContext.noXiDivisorClaim :=
  g8OrthodoxShadowAxisSource_noXiDivisorClaim pull.source

/-- The pullback context carries no analytic-completion claim from finite
    stages. -/
theorem g8OrthodoxPrimePolarityAxisPullback_noAnalyticCompletionClaim
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8OrthodoxShadowAxisSource_noAnalyticCompletionClaim pull.source

-- ============================================================
-- LOCAL CHART-TO-TAU PULLBACK THEOREMS
-- ============================================================

/-- A declared orthodox off-critical candidate is off-axis in the induced
    chart. -/
theorem g8OrthodoxPrimePolarityAxisPullback_offCritical_to_chartOffAxis
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    G8ChartOffAxis
      (g8OrthodoxPrimePolarityAxisPullback_chart pull) z :=
  g8OrthodoxShadowAxisSource_offCritical_to_chartOffAxis
    pull.source z hz

/-- Orthodox off-critical data has a tau-related preimage once the declared
    chart relation supplies preimages for off-axis shadows. -/
theorem g8OrthodoxPrimePolarityAxisPullback_offCritical_hasTauPreimage
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    ∃ w : ctx.test.base.tauWitness, pull.shadowTauRelated z w :=
  pull.offAxisHasTauPreimage z
    (g8OrthodoxPrimePolarityAxisPullback_offCritical_to_chartOffAxis
      pull z hz)

/-- A related tau preimage of an orthodox off-critical candidate carries
    tau B/C imbalance by axis-offset alignment. -/
theorem
    g8OrthodoxPrimePolarityAxisPullback_offCritical_relatedPreimage_bcImbalance
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hz : ClassicalOffCriticalZero ctx.test.base z)
    (hRel : pull.shadowTauRelated z w) :
    TauBCImbalance (ctx.test.tauNormalForm w) :=
  g8PrimePolarityAxisOffset_offAxis_relatedPreimage_bcImbalance
    (g8OrthodoxPrimePolarityAxisPullback_to_axisOffsetContext pull)
    z w
    (g8OrthodoxPrimePolarityAxisPullback_offCritical_to_chartOffAxis
      pull z hz)
    hRel

/-- A related tau preimage of an orthodox off-critical candidate carries
    tau critical imbalance. -/
theorem
    g8OrthodoxPrimePolarityAxisPullback_offCritical_relatedPreimage_tauCritical
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness)
    (hz : ClassicalOffCriticalZero ctx.test.base z)
    (hRel : pull.shadowTauRelated z w) :
    TauCriticalImbalance (ctx.test.tauNormalForm w) :=
  (tauCriticalImbalance_iff_bcImbalance
    (ctx.test.tauNormalForm w)).mpr
    (g8OrthodoxPrimePolarityAxisPullback_offCritical_relatedPreimage_bcImbalance
      pull z w hz hRel)

/-- Orthodox off-critical data produces a related tau preimage carrying tau
    critical imbalance. -/
theorem
    g8OrthodoxPrimePolarityAxisPullback_offCritical_to_tauCriticalPreimage
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    ∃ w : ctx.test.base.tauWitness,
      pull.shadowTauRelated z w ∧
        TauCriticalImbalance (ctx.test.tauNormalForm w) := by
  obtain ⟨w, hRel⟩ :=
    g8OrthodoxPrimePolarityAxisPullback_offCritical_hasTauPreimage
      pull z hz
  exact
    ⟨w, hRel,
      g8OrthodoxPrimePolarityAxisPullback_offCritical_relatedPreimage_tauCritical
        pull z w hz hRel⟩

/-- Orthodox off-critical data produces the declared tau off-critical witness
    once tau imbalance realization is available. -/
theorem g8OrthodoxPrimePolarityAxisPullback_offCritical_to_tauWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx)
    (z : ctx.test.base.orthodoxZero)
    (hz : ClassicalOffCriticalZero ctx.test.base z) :
    ∃ w : ctx.test.base.tauWitness,
      TauOffCriticalWitness ctx.test.base w := by
  obtain ⟨w, _hRel, hTauCritical⟩ :=
    g8OrthodoxPrimePolarityAxisPullback_offCritical_to_tauCriticalPreimage
      pull z hz
  exact ⟨w, pull.tauWitness w hTauCritical⟩

/-- The orthodox-source plus prime-polarity axis-offset context yields the
    local one-sided pullback obligation. -/
theorem g8OrthodoxPrimePolarityAxisPullback_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx) :
    G8eOffCriticalPullback ctx.test.base := by
  intro z hz
  exact
    g8OrthodoxPrimePolarityAxisPullback_offCritical_to_tauWitness
      pull z hz

/-- With tau-side purity, the orthodox-source plus prime-polarity axis-offset
    context yields the local no-off-critical-zero conclusion. -/
theorem g8OrthodoxPrimePolarityAxisPullback_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base := by
  intro z hz
  obtain ⟨w, hw⟩ :=
    g8OrthodoxPrimePolarityAxisPullback_yields_pullback
      ctx pull z hz
  exact tauPurity w hw

-- ============================================================
-- ADAPTERS INTO EXISTING CORRIDORS
-- ============================================================

/-- The pullback context supplies the decomposed chart-faithfulness package. -/
def g8OrthodoxPrimePolarityAxisPullback_to_decomposition
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx) :
    G8OffAxisChartFaithfulnessDecomposition
      (g8OrthodoxPrimePolarityAxisPullback_chart pull) where
  shadowTauRelated := pull.shadowTauRelated
  chartReadable := by
    intro z hz
    exact
      g8OrthodoxPrimePolarityAxisPullback_offCritical_to_chartOffAxis
        pull z hz
  tauPreimageExists := pull.offAxisHasTauPreimage
  relationPreservesBCImbalance := by
    intro z w hOffAxis hRel
    exact
      g8PrimePolarityAxisOffset_offAxis_relatedPreimage_bcImbalance
        (g8OrthodoxPrimePolarityAxisPullback_to_axisOffsetContext pull)
        z w hOffAxis hRel
  tauWitness := pull.tauWitness
  offAxisGuard := pull.offAxisGuard

/-- The pullback context supplies the weak realization ladder. -/
def g8OrthodoxPrimePolarityAxisPullback_to_realization
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx) :
    G8WeakOffAxisPullbackRealizationContext ctx :=
  g8OffAxisChartFaithfulnessDecomposition_to_realization
    ctx
    (g8OrthodoxPrimePolarityAxisPullback_chart pull)
    (g8OrthodoxPrimePolarityAxisPullback_to_decomposition pull)

/-- Build the stage-aware localization audit from the orthodox-source
    prime-polarity axis pullback context. -/
def g8OrthodoxPrimePolarityAxisPullback_to_localizationAudit
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base)
    (stage : Nat) (factor : Nat → Nat)
    (stageAdmissible : ctx.test.base.orthodoxZero → Prop)
    (sameTauTowerSubstrate : ctx.test.base.orthodoxZero → Prop)
    (sameFiniteApproximantSubstrate :
      ctx.test.base.orthodoxZero → Prop)
    (receivingShadowAdmissible :
      ctx.test.base.orthodoxZero → Prop) :
    G8PrimePolarityLocalizationAudit :=
  g8PrimePolarityAxisOffset_to_localizationAudit
    ctx
    (g8OrthodoxPrimePolarityAxisPullback_to_axisOffsetContext pull)
    tauPurity stage factor stageAdmissible sameTauTowerSubstrate
    sameFiniteApproximantSubstrate receivingShadowAdmissible

-- ============================================================
-- LOCAL FALSIFIER PRESSURE
-- ============================================================

/-- An orthodox off-critical candidate with no related tau preimage refutes
    the pullback context. -/
structure G8OrthodoxPrimePolarityOffCriticalNoPreimageWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx) where
  z : ctx.test.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  noRelatedPreimage :
    ∀ w : ctx.test.base.tauWitness, ¬ pull.shadowTauRelated z w

/-- No-preimage witnesses refute the orthodox prime-polarity pullback
    context. -/
theorem
    g8OrthodoxPrimePolarityOffCriticalNoPreimage_refutes_pullback
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx}
    (w : G8OrthodoxPrimePolarityOffCriticalNoPreimageWitness pull) :
    False := by
  obtain ⟨tauW, hRel⟩ :=
    g8OrthodoxPrimePolarityAxisPullback_offCritical_hasTauPreimage
      pull w.z w.offCritical
  exact w.noRelatedPreimage tauW hRel

/-- A related tau preimage of an orthodox off-critical candidate that remains
    B/C-balanced refutes axis-offset alignment. -/
structure G8OrthodoxPrimePolarityOffCriticalBalancedPreimageWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx) where
  z : ctx.test.base.orthodoxZero
  w : ctx.test.base.tauWitness
  offCritical : ClassicalOffCriticalZero ctx.test.base z
  related : pull.shadowTauRelated z w
  balanced : BCBalanced (ctx.test.tauNormalForm w)

/-- Balanced related preimages refute the orthodox prime-polarity pullback
    context. -/
theorem
    g8OrthodoxPrimePolarityOffCriticalBalancedPreimage_refutes_pullback
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx}
    (w :
      G8OrthodoxPrimePolarityOffCriticalBalancedPreimageWitness pull) :
    False :=
  (g8OrthodoxPrimePolarityAxisPullback_offCritical_relatedPreimage_bcImbalance
    pull w.z w.w w.offCritical w.related) w.balanced

/-- A related orthodox/tau witness pair whose axis offsets disagree refutes
    the pullback context. -/
structure G8OrthodoxPrimePolarityAxisOffsetMismatchWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx) where
  z : ctx.test.base.orthodoxZero
  w : ctx.test.base.tauWitness
  related : pull.shadowTauRelated z w
  mismatch :
    ((g8OrthodoxPrimePolarityAxisPullback_chart pull).centeredShadow z).axisOffset ≠
      primePolarityAxisOffset (ctx.test.tauNormalForm w)

/-- Axis-offset mismatch refutes the orthodox prime-polarity pullback
    context. -/
theorem g8OrthodoxPrimePolarityAxisOffsetMismatch_refutes_pullback
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx}
    (w : G8OrthodoxPrimePolarityAxisOffsetMismatchWitness pull) :
    False :=
  w.mismatch (pull.axisOffsetAligned w.z w.w w.related)

/-- A chart-only off-critical zero refutes the pullback theorem produced by
    the orthodox prime-polarity axis context. -/
theorem g8OrthodoxPrimePolarityChartOnly_refutes_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (pull : G8OrthodoxPrimePolarityAxisPullbackContext ctx)
    (w : ChartOnlyOffCriticalZeroWitness ctx.test.base) :
    False :=
  (g8e_chartOnlyWitness_refutes_pullback
    ctx.test.base w)
    (g8OrthodoxPrimePolarityAxisPullback_yields_pullback ctx pull)

end Tau.BookIII.Bridge
