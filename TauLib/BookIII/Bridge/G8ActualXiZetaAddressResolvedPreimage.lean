import TauLib.BookIII.Bridge.G8ActualXiZetaBoundaryAddressMap

/-!
# TauLib.BookIII.Bridge.G8ActualXiZetaAddressResolvedPreimage

Address-resolved tau preimages for actual off-axis `xi` shadows.

The preceding boundary-address-map layer inserts the finite point-address
socket:

```text
actual off-axis xi shadow
  -> boundary point address
  -> normalized canonical boundary witness
  -> tau B/C and critical imbalance
```

This module proves the next split-disciplined step: an address map plus a
compatible witness-carrier adapter directly supplies pointwise tau imbalance
preimages.  Crucially, this route does not require compatibility with the
older binary `g8TauShadowSelectedNormalForm` handoff.  That older handoff
remains available only as a separate adapter when explicitly supplied.

No O3 theorem, analytic-completion uniqueness, full divisor transfer,
tau-side purity theorem, classical RH theorem, or global zero-divisor theorem
is proved here.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- ADDRESS-RESOLVED PREIMAGE SOURCE
-- ============================================================

/-- Address-resolved preimage source for a thin actual `xi`/`zeta` source.

The `addrMap` is the finite boundary point-address resolver.  The `witness`
field embeds normalized boundary witnesses into the source's tau-witness
carrier.  This is exactly the extra data needed to turn address resolution
into pointwise tau preimages, without passing through the old selected-NF
sample corridor. -/
structure G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource
    (source : G8ActualXiZetaThinSourceContext) where
  addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source
  witness :
    G8ActualXiZetaThinBoundaryPointAddressWitnessAdapter addrMap

/-- The pointwise witness selected by an address-resolved source. -/
def G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource.pointSpecificWitness
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    source.tauWitness :=
  resolved.witness.pointSpecificWitness z hOffAxis

/-- The normalized boundary witness selected by an address-resolved source. -/
def G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource.normalizedWitness
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    G8CanonicalBoundaryWitness :=
  resolved.addrMap.normalizedWitness z hOffAxis

/-- The pointwise witness normal form is the normalized boundary-address
    witness normal form. -/
theorem g8ActualXiZetaThinBoundaryAddressResolvedPreimageSource_witness_normalForm_eq_normalizedAddress
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    source.tauNormalForm
        (resolved.pointSpecificWitness z hOffAxis) =
      (resolved.normalizedWitness z hOffAxis).nf :=
  resolved.witness.witness_normalForm_eq_normalizedAddress z hOffAxis

/-- Address-resolved witnesses satisfy the thin normalized-axis relation. -/
theorem g8ActualXiZetaThinBoundaryAddressResolvedPreimageSource_normalizedRelated
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    G8ActualXiZetaThinNormalizedAxisRelated
      source z (resolved.pointSpecificWitness z hOffAxis) := by
  unfold G8ActualXiZetaThinNormalizedAxisRelated
  rw [
    g8ActualXiZetaThinBoundaryAddressResolvedPreimageSource_witness_normalForm_eq_normalizedAddress
      resolved z hOffAxis
  ]
  exact (resolved.addrMap.normalizedAxis_agrees z hOffAxis).symm

/-- Address-resolved witnesses carry tau B/C imbalance. -/
theorem g8ActualXiZetaThinBoundaryAddressResolvedPreimageSource_bcImbalance
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    TauBCImbalance
      (source.tauNormalForm
        (resolved.pointSpecificWitness z hOffAxis)) := by
  rw [
    g8ActualXiZetaThinBoundaryAddressResolvedPreimageSource_witness_normalForm_eq_normalizedAddress
      resolved z hOffAxis
  ]
  exact
    g8ActualXiZetaThinBoundaryPointAddressMap_bcImbalance
      resolved.addrMap z hOffAxis

/-- Address-resolved witnesses carry tau critical imbalance. -/
theorem g8ActualXiZetaThinBoundaryAddressResolvedPreimageSource_criticalImbalance
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    TauCriticalImbalance
      (source.tauNormalForm
        (resolved.pointSpecificWitness z hOffAxis)) := by
  rw [
    g8ActualXiZetaThinBoundaryAddressResolvedPreimageSource_witness_normalForm_eq_normalizedAddress
      resolved z hOffAxis
  ]
  exact
    g8ActualXiZetaThinBoundaryPointAddressMap_criticalImbalance
      resolved.addrMap z hOffAxis

/-- Address-resolved witnesses have unit tau axis class. -/
theorem g8ActualXiZetaThinBoundaryAddressResolvedPreimageSource_unitAxis
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    primePolarityAxisOffset
      (source.tauNormalForm
        (resolved.pointSpecificWitness z hOffAxis)) = 1 := by
  rw [
    g8ActualXiZetaThinBoundaryAddressResolvedPreimageSource_witness_normalForm_eq_normalizedAddress
      resolved z hOffAxis
  ]
  exact
    g8ActualXiZetaThinBoundaryPointAddressMap_unitAxis
      resolved.addrMap z hOffAxis

-- ============================================================
-- DIRECT POINTWISE PREIMAGE THEOREM
-- ============================================================

/-- A boundary point-address map plus a compatible witness-carrier adapter
    directly supplies pointwise tau imbalance preimages.

This theorem intentionally avoids the selected-NF compatibility gate.  It is
the address-resolution route rather than the older binary sample route. -/
theorem G8ActualXiZetaThinBoundaryPointAddressMap.to_pointwisePreimages
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source)
    (witness :
      G8ActualXiZetaThinBoundaryPointAddressWitnessAdapter addrMap) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist source := by
  intro z hOffAxis
  refine
    ⟨witness.pointSpecificWitness z hOffAxis, ?_⟩
  constructor
  · unfold G8ActualXiZetaThinNormalizedAxisRelated
    rw [witness.witness_normalForm_eq_normalizedAddress z hOffAxis]
    exact (addrMap.normalizedAxis_agrees z hOffAxis).symm
  · rw [witness.witness_normalForm_eq_normalizedAddress z hOffAxis]
    exact
      g8ActualXiZetaThinBoundaryPointAddressMap_criticalImbalance
        addrMap z hOffAxis

/-- An address-resolved source supplies pointwise tau imbalance preimages. -/
theorem G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource.to_pointwisePreimages
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist source :=
  resolved.addrMap.to_pointwisePreimages resolved.witness

-- ============================================================
-- THICKENING AND CORRIDOR ADAPTERS
-- ============================================================

/-- Address-resolved source supplies the legacy actual-source pointwise
    preimage contract after explicit thickening. -/
theorem G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource.to_fullPointwise
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart) :
    G8ActualXiZetaPointwiseTauImbalancePreimagesExist
      (g8ActualXiZetaThin_to_fullSource
        source transfer chartAgreement) :=
  g8ActualXiZetaThinPointwise_to_fullPointwise
    source transfer chartAgreement
    resolved.to_pointwisePreimages

/-- The thickened address-resolved source realizes tau critical imbalance as
    the local tau off-critical witness predicate. -/
theorem
    g8ActualXiZetaThinAddressResolved_to_fullTauWitnessRealization
    (source : G8ActualXiZetaThinSourceContext)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart) :
    G8OffAxisTauWitnessRealization
      (g8ActualXiZeta_chart
        (g8ActualXiZetaThin_to_fullSource
          source transfer chartAgreement)) := by
  intro _w hImbalance
  exact hImbalance

/-- An address-resolved source supplies the actual no-ghost decomposition
    after explicit thickening. -/
def G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource.to_noGhostDecomposition
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart) :
    G8ActualXiZetaNoGhostDecomposition
      (g8ActualXiZetaThin_to_fullSource
        source transfer chartAgreement) where
  pointwisePreimages :=
    resolved.to_fullPointwise transfer chartAgreement
  tauWitness :=
    g8ActualXiZetaThinAddressResolved_to_fullTauWitnessRealization
      source transfer chartAgreement

/-- An address-resolved source supplies the actual `xi`/`zeta` corridor after
    explicit thickening. -/
def G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource.to_corridor
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart) :
    G8ActualXiZetaCorridor
      (g8ActualXiZetaThin_to_fullSource
        source transfer chartAgreement) :=
  g8ActualXiZetaNoGhostDecomposition_to_corridor
    (resolved.to_noGhostDecomposition transfer chartAgreement)

/-- An address-resolved source yields local one-sided pullback after explicit
    thickening. -/
theorem G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource.yields_pullback
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart) :
    G8eOffCriticalPullback
      (g8ActualXiZeta_base
        (g8ActualXiZetaThin_to_fullSource
          source transfer chartAgreement)) :=
  g8ActualXiZetaNoGhostDecomposition_yields_pullback
    (g8ActualXiZetaThin_to_fullSource
      source transfer chartAgreement)
    (resolved.to_noGhostDecomposition transfer chartAgreement)

/-- An address-resolved source plus tau-side purity yields local exclusion
    after explicit thickening. -/
theorem G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource.noOffCriticalXiZeros
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart)
    (tauPurity :
      G8eTauPurityExcludesOffCritical
        (g8ActualXiZeta_base
          (g8ActualXiZetaThin_to_fullSource
            source transfer chartAgreement))) :
    G8eNoOrthodoxOffCriticalZeros
      (g8ActualXiZeta_base
        (g8ActualXiZetaThin_to_fullSource
          source transfer chartAgreement)) :=
  g8ActualXiZetaNoGhostDecomposition_noOffCriticalXiZeros
    (g8ActualXiZetaThin_to_fullSource
      source transfer chartAgreement)
    (resolved.to_noGhostDecomposition transfer chartAgreement)
    tauPurity

-- ============================================================
-- GUARDRAILS AND DIAGNOSTICS
-- ============================================================

/-- Address-resolved preimage sources remain finite-stage guarded. -/
theorem G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource.finiteStageGuardrails
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source) :
    resolved.addrMap.finiteStageGuardrails :=
  resolved.addrMap.finiteStageGuardrails_proof

/-- Address-resolved preimage sources do not assert a receiving-side `xi`
    divisor claim. -/
theorem G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource.noXiDivisorClaim
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source) :
    resolved.addrMap.noXiDivisorClaim :=
  resolved.addrMap.noXiDivisorClaim_proof

/-- Address-resolved preimage sources do not assert analytic-completion
    uniqueness or existence. -/
theorem G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource.noAnalyticCompletionClaim
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source) :
    resolved.addrMap.noAnalyticCompletionClaim :=
  resolved.addrMap.noAnalyticCompletionClaim_proof

/-- Point-sensitivity remains a separate diagnostic certificate. -/
def G8ActualXiZetaThinBoundaryAddressResolvedPreimageSourcePointSensitive
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source) :
    Prop :=
  G8ActualXiZetaThinBoundaryPointAddressMapPointSensitive
    resolved.addrMap

/-- Sample-class collapse remains a separate diagnostic falsifier. -/
def G8ActualXiZetaThinBoundaryAddressResolvedPreimageSourceSampleClass
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source) :
    Prop :=
  G8ActualXiZetaThinBoundaryPointAddressMapSampleClass
    resolved.addrMap

/-- A point-sensitive address-resolved source is not sample-class. -/
theorem G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource.pointSensitive_not_sampleClass
    {source : G8ActualXiZetaThinSourceContext}
    (resolved :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource source)
    (hPoint :
      G8ActualXiZetaThinBoundaryAddressResolvedPreimageSourcePointSensitive
        resolved) :
    ¬ G8ActualXiZetaThinBoundaryAddressResolvedPreimageSourceSampleClass
        resolved :=
  g8ActualXiZetaThinBoundaryPointAddressMap_pointSensitive_not_sampleClass
    hPoint

end Tau.BookIII.Bridge
