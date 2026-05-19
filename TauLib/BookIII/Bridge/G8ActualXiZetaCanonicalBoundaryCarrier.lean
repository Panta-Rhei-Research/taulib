import TauLib.BookIII.Bridge.G8ActualXiZetaAddressResolvedPreimage

/-!
# TauLib.BookIII.Bridge.G8ActualXiZetaCanonicalBoundaryCarrier

Canonical boundary-witness carrier for the actual `xi`/`zeta` G8f corridor.

The address-resolved preimage layer reduced the hard witness step to one
carrier adapter:

```text
normalized canonical boundary witness -> source.tauWitness
```

This module instantiates that adapter by choosing the source tau-witness
carrier to be `G8CanonicalBoundaryWitness` itself.  The point-specific witness
is then the normalized boundary-address witness, and the normal-form equality
is definitional.

It also connects the actual centered `xi` shadow to this carrier through the
shadow-induced point-address map.  Point sensitivity over the actual carrier is
kept as a certificate: two actual off-axis carriers must expose the two
distinguished off-axis centered shadows before sample-class collapse is
refuted at the actual-source level.

No O3 theorem, analytic-completion uniqueness, full divisor transfer,
tau-side purity theorem, classical localization theorem, or global
zero-divisor theorem is proved here.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- CANONICAL BOUNDARY CARRIER
-- ============================================================

/-- Universe-lifted canonical boundary witness carrier for the G8 interfaces.

The mathematical witness remains `G8CanonicalBoundaryWitness`; the lift only
places it in the `Type 2` slot used by the bridge contexts. -/
abbrev G8CanonicalBoundaryWitnessCarrier : Type 2 :=
  ULift.{2, 0} G8CanonicalBoundaryWitness

/-- Lift a canonical boundary witness into the bridge carrier. -/
def G8CanonicalBoundaryWitness.toCarrier
    (w : G8CanonicalBoundaryWitness) :
    G8CanonicalBoundaryWitnessCarrier :=
  ULift.up w

/-- Project a bridge carrier back to the canonical boundary witness. -/
def G8CanonicalBoundaryWitnessCarrier.toWitness
    (w : G8CanonicalBoundaryWitnessCarrier) :
    G8CanonicalBoundaryWitness :=
  w.down

/-- Normal form carried by a lifted canonical boundary witness. -/
def G8CanonicalBoundaryWitnessCarrier.normalForm
    (w : G8CanonicalBoundaryWitnessCarrier) :
    BoundaryNF :=
  w.toWitness.nf

/-- Thin actual `xi`/`zeta` source whose tau-witness carrier is exactly the
    canonical boundary-witness type. -/
def g8ActualXiZetaCanonicalBoundaryThinSource
    (chart : ZetaAsCoordinateChartContext)
    (hG3 : chart.g3ZetaBridge)
    (hG4 : chart.g4AnalyticContinuation) :
    G8ActualXiZetaThinSourceContext where
  chart := chart
  tauWitness := G8CanonicalBoundaryWitnessCarrier
  tauNormalForm := G8CanonicalBoundaryWitnessCarrier.normalForm
  g3ZetaChartReadout := hG3
  g4CompletedXiReadout := hG4
  status := .conditionalExclusionAvailable

/-- Full actual `xi`/`zeta` source whose tau-witness carrier is the canonical
    boundary-witness type. -/
def g8ActualXiZetaCanonicalBoundaryFullSource
    (transfer : G8dZeroDivisorTransferContext)
    (hG3 : transfer.completion.chart.g3ZetaBridge)
    (hG4 : transfer.completion.chart.g4AnalyticContinuation) :
    G8ActualXiZetaSourceContext where
  transfer := transfer
  tauWitness := G8CanonicalBoundaryWitnessCarrier
  tauNormalForm := G8CanonicalBoundaryWitnessCarrier.normalForm
  g3ZetaChartReadout := hG3
  g4CompletedXiReadout := hG4
  status := .conditionalExclusionAvailable

/-- The thin canonical-boundary source obtained from a full transfer context
    uses the same chart as the full canonical-boundary source. -/
theorem g8ActualXiZetaCanonicalBoundaryThinSourceOfTransfer_chart
    (transfer : G8dZeroDivisorTransferContext)
    (hG3 : transfer.completion.chart.g3ZetaBridge)
    (hG4 : transfer.completion.chart.g4AnalyticContinuation) :
    (g8ActualXiZetaCanonicalBoundaryThinSource
      transfer.completion.chart hG3 hG4).chart =
      transfer.completion.chart :=
  rfl

-- ============================================================
-- IDENTITY WITNESS ADAPTER
-- ============================================================

/-- For the canonical boundary carrier, a normalized point-address witness is
    already a tau witness. -/
def g8ActualXiZetaCanonicalBoundaryWitnessAdapter
    {chart : ZetaAsCoordinateChartContext}
    {hG3 : chart.g3ZetaBridge}
    {hG4 : chart.g4AnalyticContinuation}
    (addrMap :
      G8ActualXiZetaThinBoundaryPointAddressMap
        (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4)) :
    G8ActualXiZetaThinBoundaryPointAddressWitnessAdapter addrMap where
  pointSpecificWitness :=
    fun z hOffAxis =>
      (addrMap.normalizedWitness z hOffAxis).toCarrier
  witness_normalForm_eq_normalizedAddress := by
    intro _z _hOffAxis
    rfl

/-- Any canonical-boundary point-address map is address-resolved by the
    identity carrier adapter. -/
def g8ActualXiZetaCanonicalBoundaryAddressResolvedSource
    {chart : ZetaAsCoordinateChartContext}
    {hG3 : chart.g3ZetaBridge}
    {hG4 : chart.g4AnalyticContinuation}
    (addrMap :
      G8ActualXiZetaThinBoundaryPointAddressMap
        (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4)) :
    G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource
      (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4) where
  addrMap := addrMap
  witness :=
    g8ActualXiZetaCanonicalBoundaryWitnessAdapter addrMap

/-- A canonical-boundary point-address map supplies pointwise tau imbalance
    preimages with no selected-NF/sample compatibility gate. -/
theorem g8ActualXiZetaCanonicalBoundaryAddressMap_pointwisePreimages
    {chart : ZetaAsCoordinateChartContext}
    {hG3 : chart.g3ZetaBridge}
    {hG4 : chart.g4AnalyticContinuation}
    (addrMap :
      G8ActualXiZetaThinBoundaryPointAddressMap
        (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4)) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist
      (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4) :=
  (g8ActualXiZetaCanonicalBoundaryAddressResolvedSource
    addrMap).to_pointwisePreimages

-- ============================================================
-- ACTUAL SHADOW-INDUCED CANONICAL CARRIER
-- ============================================================

/-- The actual centered `xi` shadow induces a point-address map into the
    canonical boundary carrier. -/
def g8ActualXiZetaCanonicalBoundaryShadowAddressMap
    (chart : ZetaAsCoordinateChartContext)
    (hG3 : chart.g3ZetaBridge)
    (hG4 : chart.g4AnalyticContinuation) :
    G8ActualXiZetaThinBoundaryPointAddressMap
      (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4) :=
  g8ActualXiZetaThinShadowInducedBoundaryPointAddressMap
    (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4)

/-- The actual centered `xi` shadow induces an address-resolved source into
    the canonical boundary carrier. -/
def g8ActualXiZetaCanonicalBoundaryShadowResolvedSource
    (chart : ZetaAsCoordinateChartContext)
    (hG3 : chart.g3ZetaBridge)
    (hG4 : chart.g4AnalyticContinuation) :
    G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource
      (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4) :=
  g8ActualXiZetaCanonicalBoundaryAddressResolvedSource
    (g8ActualXiZetaCanonicalBoundaryShadowAddressMap chart hG3 hG4)

/-- The actual centered `xi` shadow supplies canonical-boundary pointwise tau
    imbalance preimages. -/
theorem g8ActualXiZetaCanonicalBoundaryShadow_pointwisePreimages
    (chart : ZetaAsCoordinateChartContext)
    (hG3 : chart.g3ZetaBridge)
    (hG4 : chart.g4AnalyticContinuation) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist
      (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4) :=
  (g8ActualXiZetaCanonicalBoundaryShadowResolvedSource
    chart hG3 hG4).to_pointwisePreimages

/-- The shadow-induced canonical-boundary source remains finite-stage
    guarded. -/
theorem g8ActualXiZetaCanonicalBoundaryShadow_finiteStageGuardrails
    (chart : ZetaAsCoordinateChartContext)
    (hG3 : chart.g3ZetaBridge)
    (hG4 : chart.g4AnalyticContinuation) :
    (g8ActualXiZetaCanonicalBoundaryShadowResolvedSource
      chart hG3 hG4).addrMap.finiteStageGuardrails :=
  (g8ActualXiZetaCanonicalBoundaryShadowResolvedSource
    chart hG3 hG4).finiteStageGuardrails

/-- The shadow-induced canonical-boundary source makes no receiving-side
    divisor claim. -/
theorem g8ActualXiZetaCanonicalBoundaryShadow_noXiDivisorClaim
    (chart : ZetaAsCoordinateChartContext)
    (hG3 : chart.g3ZetaBridge)
    (hG4 : chart.g4AnalyticContinuation) :
    (g8ActualXiZetaCanonicalBoundaryShadowResolvedSource
      chart hG3 hG4).addrMap.noXiDivisorClaim :=
  (g8ActualXiZetaCanonicalBoundaryShadowResolvedSource
    chart hG3 hG4).noXiDivisorClaim

/-- The shadow-induced canonical-boundary source makes no analytic-completion
    claim. -/
theorem g8ActualXiZetaCanonicalBoundaryShadow_noAnalyticCompletionClaim
    (chart : ZetaAsCoordinateChartContext)
    (hG3 : chart.g3ZetaBridge)
    (hG4 : chart.g4AnalyticContinuation) :
    (g8ActualXiZetaCanonicalBoundaryShadowResolvedSource
      chart hG3 hG4).addrMap.noAnalyticCompletionClaim :=
  (g8ActualXiZetaCanonicalBoundaryShadowResolvedSource
    chart hG3 hG4).noAnalyticCompletionClaim

-- ============================================================
-- THICKENED CORRIDOR HANDOFFS
-- ============================================================

/-- The canonical-boundary shadow source supplies the actual no-ghost
    decomposition after thickening along the same transfer chart. -/
def g8ActualXiZetaCanonicalBoundaryShadow_to_noGhostDecomposition
    (transfer : G8dZeroDivisorTransferContext)
    (hG3 : transfer.completion.chart.g3ZetaBridge)
    (hG4 : transfer.completion.chart.g4AnalyticContinuation) :
    G8ActualXiZetaNoGhostDecomposition
      (g8ActualXiZetaThin_to_fullSource
        (g8ActualXiZetaCanonicalBoundaryThinSource
          transfer.completion.chart hG3 hG4)
        transfer rfl) :=
  (g8ActualXiZetaCanonicalBoundaryShadowResolvedSource
    transfer.completion.chart hG3 hG4).to_noGhostDecomposition
      transfer rfl

/-- The canonical-boundary shadow source supplies the actual corridor after
    thickening along the same transfer chart. -/
def g8ActualXiZetaCanonicalBoundaryShadow_to_corridor
    (transfer : G8dZeroDivisorTransferContext)
    (hG3 : transfer.completion.chart.g3ZetaBridge)
    (hG4 : transfer.completion.chart.g4AnalyticContinuation) :
    G8ActualXiZetaCorridor
      (g8ActualXiZetaThin_to_fullSource
        (g8ActualXiZetaCanonicalBoundaryThinSource
          transfer.completion.chart hG3 hG4)
        transfer rfl) :=
  (g8ActualXiZetaCanonicalBoundaryShadowResolvedSource
    transfer.completion.chart hG3 hG4).to_corridor
      transfer rfl

/-- The canonical-boundary shadow source yields the local one-sided pullback
    after thickening along the same transfer chart. -/
theorem g8ActualXiZetaCanonicalBoundaryShadow_yields_pullback
    (transfer : G8dZeroDivisorTransferContext)
    (hG3 : transfer.completion.chart.g3ZetaBridge)
    (hG4 : transfer.completion.chart.g4AnalyticContinuation) :
    G8eOffCriticalPullback
      (g8ActualXiZeta_base
        (g8ActualXiZetaThin_to_fullSource
          (g8ActualXiZetaCanonicalBoundaryThinSource
            transfer.completion.chart hG3 hG4)
          transfer rfl)) :=
  (g8ActualXiZetaCanonicalBoundaryShadowResolvedSource
    transfer.completion.chart hG3 hG4).yields_pullback
      transfer rfl

/-- With tau-side purity supplied explicitly, the canonical-boundary shadow
    corridor excludes orthodox off-critical carrier zeros locally. -/
theorem g8ActualXiZetaCanonicalBoundaryShadow_noOffCriticalXiZeros
    (transfer : G8dZeroDivisorTransferContext)
    (hG3 : transfer.completion.chart.g3ZetaBridge)
    (hG4 : transfer.completion.chart.g4AnalyticContinuation)
    (tauPurity :
      G8eTauPurityExcludesOffCritical
        (g8ActualXiZeta_base
          (g8ActualXiZetaThin_to_fullSource
            (g8ActualXiZetaCanonicalBoundaryThinSource
              transfer.completion.chart hG3 hG4)
            transfer rfl))) :
    G8eNoOrthodoxOffCriticalZeros
      (g8ActualXiZeta_base
        (g8ActualXiZetaThin_to_fullSource
          (g8ActualXiZetaCanonicalBoundaryThinSource
            transfer.completion.chart hG3 hG4)
          transfer rfl)) :=
  (g8ActualXiZetaCanonicalBoundaryShadowResolvedSource
    transfer.completion.chart hG3 hG4).noOffCriticalXiZeros
      transfer rfl tauPurity

-- ============================================================
-- ACTUAL POINT-SENSITIVITY CERTIFICATE
-- ============================================================

/-- Certificate that the actual thin source exposes the two distinguished
    off-axis centered shadows used by the point-sensitive address selector.

This is intentionally a certificate, not an assertion about all actual
orthodox zeros.  It is the strongest current route for lifting the
point-sensitive boundary-address theorem to the actual `xi` carrier. -/
structure G8ActualXiZetaThinActualPointSensitivityWitness
    (source : G8ActualXiZetaThinSourceContext) where
  zA : OrthodoxXiZeroCarrier
  zB : OrthodoxXiZeroCarrier
  zA_offAxis : G8ActualXiZetaThinChartOffAxis source zA
  zB_offAxis : G8ActualXiZetaThinChartOffAxis source zB
  zA_shadow :
    g8ActualXiZetaThinCenteredShadow source zA =
      g8PointSensitiveShadowA
  zB_shadow :
    g8ActualXiZetaThinCenteredShadow source zB =
      g8PointSensitiveShadowB

/-- A source exposing the two distinguished off-axis shadows makes the
    shadow-induced address map point-sensitive at the actual-source level. -/
theorem g8ActualXiZetaThinActualPointSensitivityWitness_shadowInduced_pointSensitive
    {source : G8ActualXiZetaThinSourceContext}
    (cert : G8ActualXiZetaThinActualPointSensitivityWitness source) :
    G8ActualXiZetaThinBoundaryPointAddressMapPointSensitive
      (g8ActualXiZetaThinShadowInducedBoundaryPointAddressMap source) := by
  refine
    ⟨cert.zA, cert.zB, cert.zA_offAxis, cert.zB_offAxis, ?_⟩
  intro hEq
  have hAB :
      g8PointSensitiveOffAxisAddressA.normalize =
        g8PointSensitiveOffAxisAddressB.normalize := by
    simpa [
      G8ActualXiZetaThinBoundaryPointAddressMap.normalizedWitness,
      g8ActualXiZetaThinShadowInducedBoundaryPointAddressMap,
      cert.zA_shadow,
      cert.zB_shadow,
      g8PointSensitiveBoundaryAddressOf_shadowA,
      g8PointSensitiveBoundaryAddressOf_shadowB
    ] using hEq
  exact g8PointSensitiveOffAxisAddressA_ne_B hAB

/-- Actual point sensitivity refutes sample-class collapse for the
    shadow-induced address map. -/
theorem g8ActualXiZetaThinActualPointSensitivityWitness_not_sampleClass
    {source : G8ActualXiZetaThinSourceContext}
    (cert : G8ActualXiZetaThinActualPointSensitivityWitness source) :
    ¬ G8ActualXiZetaThinBoundaryPointAddressMapSampleClass
        (g8ActualXiZetaThinShadowInducedBoundaryPointAddressMap source) :=
  g8ActualXiZetaThinBoundaryPointAddressMap_pointSensitive_not_sampleClass
    (g8ActualXiZetaThinActualPointSensitivityWitness_shadowInduced_pointSensitive
      cert)

/-- Actual point sensitivity refutes sample-class collapse for the
    canonical-boundary resolved source. -/
theorem g8ActualXiZetaCanonicalBoundaryShadow_not_sampleClass
    {chart : ZetaAsCoordinateChartContext}
    {hG3 : chart.g3ZetaBridge}
    {hG4 : chart.g4AnalyticContinuation}
    (cert :
      G8ActualXiZetaThinActualPointSensitivityWitness
        (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4)) :
    ¬ G8ActualXiZetaThinBoundaryAddressResolvedPreimageSourceSampleClass
        (g8ActualXiZetaCanonicalBoundaryShadowResolvedSource
          chart hG3 hG4) :=
  (g8ActualXiZetaCanonicalBoundaryShadowResolvedSource
    chart hG3 hG4).pointSensitive_not_sampleClass
      (g8ActualXiZetaThinActualPointSensitivityWitness_shadowInduced_pointSensitive
        cert)

end Tau.BookIII.Bridge
