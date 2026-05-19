import TauLib.BookIII.Bridge.G8FinalRHSpineDischarge

/-!
# TauLib.BookIII.Bridge.G8AcceptedTauSpectralPurityDomain

Accepted tau spectral-witness domain for the final G8f spine.

The manuscript-facing purity statement belongs to an accepted spectral domain,
not to every finite boundary-address witness.  This module therefore inserts
one final filter between the actual centered `xi` address resolver and the
tau-purity target:

```text
actual off-axis xi shadow
  -> centered boundary address
  -> accepted spectral witness
  -> tau normal form
  -> purity exclusion on the accepted domain
```

The broad canonical boundary carrier remains useful as an address-resolution
and diagnostic surface.  It is not the target of tau spectral purity.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- ACCEPTED TAU SPECTRAL DOMAIN
-- ============================================================

/-- Accepted tau spectral-witness domain for the G8f final spine.

The field `spectralPurity` is deliberately scoped to this accepted carrier:
it excludes tau critical imbalance only after a witness has been admitted into
the spectral domain. -/
structure G8AcceptedTauSpectralWitnessDomain where
  tauWitness : Type 2
  tauNormalForm : tauWitness → BoundaryNF
  spectralPurity :
    ∀ w : tauWitness, ¬ TauCriticalImbalance (tauNormalForm w)
  status : G8OffCriticalExclusionStatus := .openObligation

/-- Thin actual `xi` source backed by an accepted tau spectral domain. -/
def G8AcceptedTauSpectralWitnessDomain.thinSource
    {transfer : G8dZeroDivisorTransferContext}
    (domain : G8AcceptedTauSpectralWitnessDomain)
    (readout : G8FinalRHTransferChartReadout transfer) :
    G8ActualXiZetaThinSourceContext where
  chart := transfer.completion.chart
  tauWitness := domain.tauWitness
  tauNormalForm := domain.tauNormalForm
  g3ZetaChartReadout := readout.g3ZetaChartReadout
  g4CompletedXiReadout := readout.g4CompletedXiReadout
  status := domain.status

/-- Full actual `xi` source backed by an accepted tau spectral domain. -/
def G8AcceptedTauSpectralWitnessDomain.source
    {transfer : G8dZeroDivisorTransferContext}
    (domain : G8AcceptedTauSpectralWitnessDomain)
    (readout : G8FinalRHTransferChartReadout transfer) :
    G8ActualXiZetaSourceContext :=
  g8ActualXiZetaThin_to_fullSource
    (domain.thinSource readout) transfer rfl

/-- Accepted-domain spectral purity supplies the local tau-purity target for
    the source induced by that same accepted domain. -/
theorem G8AcceptedTauSpectralWitnessDomain.to_g8eTauPurity
    {transfer : G8dZeroDivisorTransferContext}
    (domain : G8AcceptedTauSpectralWitnessDomain)
    (readout : G8FinalRHTransferChartReadout transfer) :
    G8eTauPurityExcludesOffCritical
      (g8ActualXiZeta_base (domain.source readout)) := by
  intro w hImbalance
  exact domain.spectralPurity w hImbalance

-- ============================================================
-- ADMISSION FROM BOUNDARY ADDRESSES
-- ============================================================

/-- Admission map from an actual off-axis centered boundary address into the
    accepted tau spectral domain.

The key equation states that the admitted spectral witness has the normal form
of the normalized centered boundary address.  This is the exact proof-facing
place where future tau geometry must justify acceptance of the address-resolved
witness into the spectral domain. -/
structure G8BoundaryToAcceptedTauSpectralAdmission
    {transfer : G8dZeroDivisorTransferContext}
    (domain : G8AcceptedTauSpectralWitnessDomain)
    (readout : G8FinalRHTransferChartReadout transfer) where
  admit :
    ∀ z : OrthodoxXiZeroCarrier,
      G8ActualXiZetaThinChartOffAxis
        (domain.thinSource readout) z →
        domain.tauWitness
  admit_normalForm :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis :
        G8ActualXiZetaThinChartOffAxis
          (domain.thinSource readout) z),
      domain.tauNormalForm (admit z hOffAxis) =
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf

/-- The explicit centered-shadow address map for an accepted spectral
    domain. -/
def G8BoundaryToAcceptedTauSpectralAdmission.toAddressMap
    {transfer : G8dZeroDivisorTransferContext}
    {domain : G8AcceptedTauSpectralWitnessDomain}
    {readout : G8FinalRHTransferChartReadout transfer}
    (_admission :
      G8BoundaryToAcceptedTauSpectralAdmission domain readout) :
    G8ActualXiZetaThinBoundaryPointAddressMap
      (domain.thinSource readout) :=
  (g8ActualXiZetaExplicitShadowAddressCorrectness
    (domain.thinSource readout)).toAddressMap

/-- An admission map embeds normalized centered addresses into the accepted
    spectral witness carrier. -/
def G8BoundaryToAcceptedTauSpectralAdmission.toWitnessAdapter
    {transfer : G8dZeroDivisorTransferContext}
    {domain : G8AcceptedTauSpectralWitnessDomain}
    {readout : G8FinalRHTransferChartReadout transfer}
    (admission :
      G8BoundaryToAcceptedTauSpectralAdmission domain readout) :
    G8ActualXiZetaThinBoundaryPointAddressWitnessAdapter
      admission.toAddressMap where
  pointSpecificWitness := admission.admit
  witness_normalForm_eq_normalizedAddress := by
    intro z hOffAxis
    exact admission.admit_normalForm z hOffAxis

/-- Accepted-domain admission yields an address-resolved source. -/
def G8BoundaryToAcceptedTauSpectralAdmission.toResolvedSource
    {transfer : G8dZeroDivisorTransferContext}
    {domain : G8AcceptedTauSpectralWitnessDomain}
    {readout : G8FinalRHTransferChartReadout transfer}
    (admission :
      G8BoundaryToAcceptedTauSpectralAdmission domain readout) :
    G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource
      (domain.thinSource readout) where
  addrMap := admission.toAddressMap
  witness := admission.toWitnessAdapter

/-- Accepted-domain admission supplies pointwise tau-imbalance preimages. -/
theorem G8BoundaryToAcceptedTauSpectralAdmission.pointwisePreimages
    {transfer : G8dZeroDivisorTransferContext}
    {domain : G8AcceptedTauSpectralWitnessDomain}
    {readout : G8FinalRHTransferChartReadout transfer}
    (admission :
      G8BoundaryToAcceptedTauSpectralAdmission domain readout) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist
      (domain.thinSource readout) :=
  admission.toResolvedSource.to_pointwisePreimages

/-- Accepted-domain admission assembles the actual `xi`/`zeta` corridor. -/
def G8BoundaryToAcceptedTauSpectralAdmission.corridor
    {transfer : G8dZeroDivisorTransferContext}
    {domain : G8AcceptedTauSpectralWitnessDomain}
    {readout : G8FinalRHTransferChartReadout transfer}
    (admission :
      G8BoundaryToAcceptedTauSpectralAdmission domain readout) :
    G8ActualXiZetaCorridor (domain.source readout) :=
  admission.toResolvedSource.to_corridor transfer rfl

-- ============================================================
-- ACCEPTED ALMOST-FINAL SPINE
-- ============================================================

/-- Final-spine discharge surface using an accepted tau spectral domain.

Compared with `G8AlmostFinalRHSpine`, this object does not use the broad
canonical boundary carrier as the purity domain.  It records an explicit
admission map from actual centered boundary addresses into the accepted
spectral witness domain. -/
structure G8AcceptedTauSpectralAlmostFinalSpine where
  transfer : G8dZeroDivisorTransferContext
  readout : G8FinalRHTransferChartReadout transfer
  domain : G8AcceptedTauSpectralWitnessDomain
  admission : G8BoundaryToAcceptedTauSpectralAdmission domain readout

/-- Thin accepted source selected by the accepted almost-final spine. -/
def G8AcceptedTauSpectralAlmostFinalSpine.thinSource
    (spine : G8AcceptedTauSpectralAlmostFinalSpine) :
    G8ActualXiZetaThinSourceContext :=
  spine.domain.thinSource spine.readout

/-- Full accepted source selected by the accepted almost-final spine. -/
def G8AcceptedTauSpectralAlmostFinalSpine.source
    (spine : G8AcceptedTauSpectralAlmostFinalSpine) :
    G8ActualXiZetaSourceContext :=
  spine.domain.source spine.readout

/-- Address-resolved accepted source selected by the accepted almost-final
    spine. -/
def G8AcceptedTauSpectralAlmostFinalSpine.resolvedSource
    (spine : G8AcceptedTauSpectralAlmostFinalSpine) :
    G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource
      spine.thinSource :=
  spine.admission.toResolvedSource

/-- The accepted almost-final spine exposes the G3 readout. -/
theorem G8AcceptedTauSpectralAlmostFinalSpine.requires_g3ZetaBridge
    (spine : G8AcceptedTauSpectralAlmostFinalSpine) :
    spine.transfer.completion.chart.g3ZetaBridge :=
  spine.readout.g3ZetaChartReadout

/-- The accepted almost-final spine exposes the G4 readout. -/
theorem G8AcceptedTauSpectralAlmostFinalSpine.requires_g4AnalyticContinuation
    (spine : G8AcceptedTauSpectralAlmostFinalSpine) :
    spine.transfer.completion.chart.g4AnalyticContinuation :=
  spine.readout.g4CompletedXiReadout

/-- The accepted almost-final spine supplies pointwise tau-imbalance
    preimages through the explicit admission map. -/
theorem G8AcceptedTauSpectralAlmostFinalSpine.pointwisePreimages
    (spine : G8AcceptedTauSpectralAlmostFinalSpine) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist
      spine.thinSource :=
  spine.admission.pointwisePreimages

/-- The accepted almost-final spine assembles the actual `xi`/`zeta`
    corridor. -/
def G8AcceptedTauSpectralAlmostFinalSpine.corridor
    (spine : G8AcceptedTauSpectralAlmostFinalSpine) :
    G8ActualXiZetaCorridor spine.source :=
  spine.admission.corridor

/-- Accepted-domain spectral purity for the selected source. -/
theorem G8AcceptedTauSpectralAlmostFinalSpine.tauPurity
    (spine : G8AcceptedTauSpectralAlmostFinalSpine) :
    G8eTauPurityExcludesOffCritical
      (g8ActualXiZeta_base spine.source) :=
  spine.domain.to_g8eTauPurity spine.readout

/-- Accepted-domain spine yields local exclusion of actual off-critical `xi`
    zeros. -/
theorem G8AcceptedTauSpectralAlmostFinalSpine.noOffCriticalXiZeros
    (spine : G8AcceptedTauSpectralAlmostFinalSpine) :
    G8eNoOrthodoxOffCriticalZeros
      (g8ActualXiZeta_base spine.source) :=
  spine.resolvedSource.noOffCriticalXiZeros
    spine.transfer rfl spine.tauPurity

/-- Accepted-domain spine yields Mathlib's `RiemannHypothesis` target through
    the existing receiving-side coverage theorem. -/
theorem G8AcceptedTauSpectralAlmostFinalSpine.mathlibRiemannHypothesis
    (spine : G8AcceptedTauSpectralAlmostFinalSpine) :
    RiemannHypothesis :=
  g8ActualXiZetaCorridor_to_mathlibRiemannHypothesis_fromCoverage
    spine.source spine.corridor spine.tauPurity

-- ============================================================
-- CANONICAL BOUNDARY CARRIER DIAGNOSTIC
-- ============================================================

/-- The current broad canonical boundary carrier contains an off-axis
    boundary witness.  Therefore it is an address carrier and diagnostic
    surface, not the accepted spectral-purity domain. -/
theorem g8CanonicalBoundaryCarrier_containsTauCriticalImbalance
    (transfer : G8dZeroDivisorTransferContext)
    (hG3 : transfer.completion.chart.g3ZetaBridge)
    (hG4 : transfer.completion.chart.g4AnalyticContinuation) :
    ¬ G8eTauPurityExcludesOffCritical
      (g8ActualXiZeta_base
        (g8ActualXiZetaCanonicalBoundaryFullSource
          transfer hG3 hG4)) := by
  intro hPurity
  let w : G8CanonicalBoundaryWitnessCarrier :=
    G8CanonicalBoundaryWitness.toCarrier
      g8TauSampleOffAxisCanonicalBoundaryWitness
  have hImbalance :
      TauOffCriticalWitness
        (g8ActualXiZeta_base
          (g8ActualXiZetaCanonicalBoundaryFullSource
            transfer hG3 hG4)) w := by
    exact g8TauSampleOffAxisBoundaryNF_criticalImbalance
  exact hPurity w hImbalance

end Tau.BookIII.Bridge
