import TauLib.BookIII.Bridge.G8ActualXiZetaCorridor

/-!
# TauLib.BookIII.Bridge.G8ActualXiZetaNoGhostDecomposition

Pointwise no-off-axis-ghost decomposition for the actual Mathlib-backed
`xi`/`zeta` source.

The actual receiving-side chart is already binary and theorem-backed:
off-critical `xi` zeros are exactly off-axis centered shadows.  This module
sharpens the remaining ghost target from "no tau witness anywhere" to the
pointwise, relation-specific obstruction:

* an actual off-axis `xi` shadow,
* no normalized-axis-related tau preimage,
* carrying tau critical imbalance.

The module does not prove O3, analytic-completion uniqueness, divisor transfer,
tau purity, or the global RH target.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- ACTUAL OFF-AXIS XI SHADOW
-- ============================================================

/-- Actual `xi` off-criticality is exactly off-axis readability in the actual
    chart object. -/
theorem g8ActualXiZeta_offCritical_iff_chartOffAxis
    (source : G8ActualXiZetaSourceContext)
    (z : OrthodoxXiZeroCarrier) :
    ClassicalOffCriticalZero (g8ActualXiZeta_base source) z ↔
      G8ChartOffAxis (g8ActualXiZeta_chart source) z := by
  constructor
  · intro hz
    exact g8ActualXiZeta_offCritical_to_chartOffAxis source z hz
  · intro hOffAxis
    have hCtx :
        ShadowOffAxis ((g8ActualXiZeta_weak source).test.orthodoxShadow z) :=
      g8ChartOffAxis_to_context
        (g8ActualXiZeta_chart source) hOffAxis
    exact
      (g8ActualXiZeta_offCritical_iff_offAxis source z).mpr
        (by simpa [g8ActualXiZeta_weak] using hCtx)

/-- Chart off-axis readability for the actual `xi` chart reflects back to
    actual orthodox off-criticality. -/
theorem g8ActualXiZeta_chartOffAxis_to_offCritical
    (source : G8ActualXiZetaSourceContext)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ChartOffAxis (g8ActualXiZeta_chart source) z) :
    ClassicalOffCriticalZero (g8ActualXiZeta_base source) z :=
  (g8ActualXiZeta_offCritical_iff_chartOffAxis source z).mpr hOffAxis

-- ============================================================
-- POINTWISE TAU PREIMAGE CONTRACT
-- ============================================================

/-- A relation-specific tau preimage for an actual off-axis `xi` shadow.

It packages exactly the data needed by the weak localization route: normalized
axis relatedness plus tau critical imbalance. -/
def G8ActualXiZetaRelatedTauCriticalPreimage
    (source : G8ActualXiZetaSourceContext)
    (z : OrthodoxXiZeroCarrier)
    (w : source.tauWitness) : Prop :=
  G8OrthodoxTauNormalizedAxisRelated
      (g8ActualXiZeta_shadowAxisSource source) z w ∧
    TauCriticalImbalance (source.tauNormalForm w)

/-- Pointwise tau critical-imbalance preimages exist for every actual off-axis
    `xi` chart shadow. -/
def G8ActualXiZetaPointwiseTauImbalancePreimagesExist
    (source : G8ActualXiZetaSourceContext) : Prop :=
  ∀ z : OrthodoxXiZeroCarrier,
    G8ChartOffAxis (g8ActualXiZeta_chart source) z →
      ∃ w : source.tauWitness,
        G8ActualXiZetaRelatedTauCriticalPreimage source z w

/-- A related tau critical preimage carries tau B/C imbalance. -/
theorem g8ActualXiZetaRelatedTauCriticalPreimage_bcImbalance
    {source : G8ActualXiZetaSourceContext}
    {z : OrthodoxXiZeroCarrier}
    {w : source.tauWitness}
    (hPre :
      G8ActualXiZetaRelatedTauCriticalPreimage source z w) :
    TauBCImbalance (source.tauNormalForm w) :=
  (tauCriticalImbalance_iff_bcImbalance
    (source.tauNormalForm w)).mp hPre.right

/-- A related tau critical preimage has tau prime-polarity axis class `1`
    whenever the actual receiving shadow is off-axis. -/
theorem g8ActualXiZetaRelatedTauCriticalPreimage_tauUnit
    {source : G8ActualXiZetaSourceContext}
    {z : OrthodoxXiZeroCarrier}
    {w : source.tauWitness}
    (hOffAxis : G8ChartOffAxis (g8ActualXiZeta_chart source) z)
    (hPre :
      G8ActualXiZetaRelatedTauCriticalPreimage source z w) :
    primePolarityAxisOffset (source.tauNormalForm w) = 1 := by
  have hNorm :
      normalizedAxisOffset
          ((g8ActualXiZeta_shadowAxisSource source).centeredShadow z) = 1 :=
    normalizedAxisOffset_eq_one_of_offAxis hOffAxis
  have hRel := hPre.left
  unfold G8OrthodoxTauNormalizedAxisRelated at hRel
  exact hRel ▸ hNorm

/-- Pointwise related tau critical preimages supply the older unit-axis
    preimage field consumed by the normalized corridor. -/
theorem
    g8ActualXiZetaPointwisePreimages_to_unitTauPreimages
    {source : G8ActualXiZetaSourceContext}
    (hPointwise :
      G8ActualXiZetaPointwiseTauImbalancePreimagesExist source) :
    G8OrthodoxTauUnitAxisPreimagesExist
      (g8ActualXiZeta_shadowAxisSource source) := by
  intro z hOffAxis
  obtain ⟨w, hPre⟩ := hPointwise z hOffAxis
  exact
    ⟨w,
      g8ActualXiZetaRelatedTauCriticalPreimage_tauUnit
        hOffAxis hPre⟩

-- ============================================================
-- POINTWISE OFF-AXIS CHART-ONLY GHOST
-- ============================================================

/-- Actual-source, pointwise off-axis chart-only ghost witness.

This is the sharper fatal falsifier for the actual `xi` chart: the receiving
shadow is genuinely off-axis, but no normalized-axis-related tau preimage
carries tau critical imbalance for that point. -/
structure G8ActualXiZetaOffAxisChartOnlyGhostWitness
    (source : G8ActualXiZetaSourceContext) where
  z : OrthodoxXiZeroCarrier
  offCritical :
    ClassicalOffCriticalZero (g8ActualXiZeta_base source) z
  offAxis :
    G8ChartOffAxis (g8ActualXiZeta_chart source) z
  noPointwiseTauImbalancePreimage :
    ∀ w : source.tauWitness,
      ¬ G8ActualXiZetaRelatedTauCriticalPreimage source z w

/-- No actual pointwise off-axis chart-only ghost exists. -/
def G8ActualXiZetaNoPointwiseOffAxisGhosts
    (source : G8ActualXiZetaSourceContext) : Prop :=
  ¬ Nonempty (G8ActualXiZetaOffAxisChartOnlyGhostWitness source)

/-- Pointwise tau critical preimages rule out actual pointwise off-axis
    chart-only ghosts. -/
theorem g8ActualXiZetaPointwisePreimages_noPointwiseGhosts
    {source : G8ActualXiZetaSourceContext}
    (hPointwise :
      G8ActualXiZetaPointwiseTauImbalancePreimagesExist source) :
    G8ActualXiZetaNoPointwiseOffAxisGhosts source := by
  intro hGhost
  rcases hGhost with ⟨ghost⟩
  obtain ⟨w, hPre⟩ := hPointwise ghost.z ghost.offAxis
  exact ghost.noPointwiseTauImbalancePreimage w hPre

/-- A pointwise off-axis ghost refutes the pointwise preimage contract. -/
theorem
    g8ActualXiZetaPointwiseGhost_refutes_pointwisePreimages
    {source : G8ActualXiZetaSourceContext}
    (ghost : G8ActualXiZetaOffAxisChartOnlyGhostWitness source) :
    ¬ G8ActualXiZetaPointwiseTauImbalancePreimagesExist source := by
  intro hPointwise
  exact g8ActualXiZetaPointwisePreimages_noPointwiseGhosts
    hPointwise ⟨ghost⟩

/-- A pointwise off-axis ghost's explicit off-axis field can be reconstructed
    from its actual orthodox off-critical field. -/
theorem g8ActualXiZetaPointwiseGhost_offAxis_from_offCritical
    {source : G8ActualXiZetaSourceContext}
    (ghost : G8ActualXiZetaOffAxisChartOnlyGhostWitness source) :
    G8ChartOffAxis (g8ActualXiZeta_chart source) ghost.z :=
  (g8ActualXiZeta_offCritical_iff_chartOffAxis
    source ghost.z).mp ghost.offCritical

-- ============================================================
-- ADAPTER TO THE EXISTING GUARD MACHINERY
-- ============================================================

/-- Pointwise related tau critical preimages, plus tau-witness realization,
    imply the existing no-off-axis-chart-only-ghost guard.

This is the bridge from the sharper pointwise falsifier back to the older
coarse guard consumed by the current normalized corridor. -/
theorem g8ActualXiZetaPointwisePreimages_to_offAxisGuard
    {source : G8ActualXiZetaSourceContext}
    (hPointwise :
      G8ActualXiZetaPointwiseTauImbalancePreimagesExist source)
    (tauWitness :
      G8OffAxisTauWitnessRealization
        (g8ActualXiZeta_chart source)) :
    G8ActualOrthodoxCenteredChartNoOffAxisGhosts
      (g8ActualXiZeta_actualCenteredChart source) := by
  intro hGhost
  rcases hGhost with ⟨ghost⟩
  have hChartOffAxis :
      G8ChartOffAxis (g8ActualXiZeta_chart source) ghost.z :=
    g8ChartOffAxis_from_context
      (g8ActualXiZeta_chart source) ghost.offAxis
  obtain ⟨w, hPre⟩ := hPointwise ghost.z hChartOffAxis
  exact ghost.noTauPreimage w (tauWitness w hPre.right)

/-- No-ghost decomposition for the actual `xi`/`zeta` corridor.

The pointwise preimage contract is the real new target; the remaining field is
the existing tau critical-imbalance realization into the local tau witness
predicate. -/
structure G8ActualXiZetaNoGhostDecomposition
    (source : G8ActualXiZetaSourceContext) where
  pointwisePreimages :
    G8ActualXiZetaPointwiseTauImbalancePreimagesExist source
  tauWitness :
    G8OffAxisTauWitnessRealization
      (g8ActualXiZeta_chart source)

/-- The no-ghost decomposition supplies the existing actual `xi`/`zeta`
    corridor. -/
def g8ActualXiZetaNoGhostDecomposition_to_corridor
    {source : G8ActualXiZetaSourceContext}
    (decomp : G8ActualXiZetaNoGhostDecomposition source) :
    G8ActualXiZetaCorridor source where
  unitTauPreimages :=
    g8ActualXiZetaPointwisePreimages_to_unitTauPreimages
      decomp.pointwisePreimages
  tauWitness := decomp.tauWitness
  offAxisGuard :=
    g8ActualXiZetaPointwisePreimages_to_offAxisGuard
      decomp.pointwisePreimages decomp.tauWitness

/-- The no-ghost decomposition yields the local one-sided pullback through
    the existing actual `xi`/`zeta` corridor. -/
theorem g8ActualXiZetaNoGhostDecomposition_yields_pullback
    (source : G8ActualXiZetaSourceContext)
    (decomp : G8ActualXiZetaNoGhostDecomposition source) :
    G8eOffCriticalPullback (g8ActualXiZeta_base source) :=
  g8ActualXiZetaCorridor_yields_pullback
    source
    (g8ActualXiZetaNoGhostDecomposition_to_corridor decomp)

/-- The no-ghost decomposition plus tau-side purity yields local exclusion of
    off-critical actual `xi` zeros. -/
theorem g8ActualXiZetaNoGhostDecomposition_noOffCriticalXiZeros
    (source : G8ActualXiZetaSourceContext)
    (decomp : G8ActualXiZetaNoGhostDecomposition source)
    (tauPurity :
      G8eTauPurityExcludesOffCritical
        (g8ActualXiZeta_base source)) :
    G8eNoOrthodoxOffCriticalZeros
      (g8ActualXiZeta_base source) :=
  g8ActualXiZetaCorridor_noOffCriticalXiZeros
    source
    (g8ActualXiZetaNoGhostDecomposition_to_corridor decomp)
    tauPurity

/-- A pointwise off-axis ghost refutes the no-ghost decomposition. -/
theorem
    g8ActualXiZetaPointwiseGhost_refutes_noGhostDecomposition
    {source : G8ActualXiZetaSourceContext}
    (ghost : G8ActualXiZetaOffAxisChartOnlyGhostWitness source) :
    ¬ G8ActualXiZetaNoGhostDecomposition source := by
  intro decomp
  exact
    g8ActualXiZetaPointwiseGhost_refutes_pointwisePreimages
      ghost decomp.pointwisePreimages

-- ============================================================
-- FINITE-STAGE GUARDRAILS
-- ============================================================

/-- The pointwise no-ghost decomposition remains finite-only at G8b. -/
theorem g8ActualXiZetaNoGhostDecomposition_finiteOnly
    {source : G8ActualXiZetaSourceContext}
    (_decomp : G8ActualXiZetaNoGhostDecomposition source) :
    finiteG8bContext.finiteOnly :=
  g8ActualXiZeta_finiteOnly source

/-- The pointwise no-ghost decomposition carries no `xi` divisor claim from
    finite stages. -/
theorem g8ActualXiZetaNoGhostDecomposition_noXiDivisorClaim
    {source : G8ActualXiZetaSourceContext}
    (_decomp : G8ActualXiZetaNoGhostDecomposition source) :
    finiteG8bContext.noXiDivisorClaim :=
  g8ActualXiZeta_noXiDivisorClaim source

/-- The pointwise no-ghost decomposition carries no analytic-completion claim
    from finite stages. -/
theorem g8ActualXiZetaNoGhostDecomposition_noAnalyticCompletionClaim
    {source : G8ActualXiZetaSourceContext}
    (_decomp : G8ActualXiZetaNoGhostDecomposition source) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8ActualXiZeta_noAnalyticCompletionClaim source

end Tau.BookIII.Bridge
