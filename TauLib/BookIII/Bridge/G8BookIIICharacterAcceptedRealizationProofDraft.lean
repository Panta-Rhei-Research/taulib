import TauLib.BookIII.Bridge.G8BookIIICharacterAcceptedRealizationLaw

/-!
# TauLib.BookIII.Bridge.G8BookIIICharacterAcceptedRealizationProofDraft

Lean translation surface for the accepted-realization coverage proof draft.

The preceding modules already theorem-back the receiving-side handoff and the
Book III character-algebra side of the route.  This module mirrors the private
LaTeX proof draft by splitting the remaining mathematical hinge into exactly
two proof fields:

* accepted tower witness realization for each orthodox `xi` carrier;
* normal-form alignment with the normalized centered boundary address.

Supplying those fields yields the existing conditional `RiemannHypothesis`
handoff.  This module does not assert the fields globally and does not add any
axioms or sorries.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- ACCEPTED TOWER REALIZATION DATA
-- ============================================================

/-- Pointwise accepted tower realization data for an orthodox `xi` carrier.

This is the first handwritten target lemma: the canonical Book III
boundary-character readout is represented by an accepted tower witness.  The
normal-form alignment is deliberately kept as a separate predicate below. -/
structure G8BookIIIAcceptedTowerRealizationData
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (_z : OrthodoxXiZeroCarrier) where
  witness : model.spectralWitness
  accepted : model.IsAccepted witness
  status : G8OffCriticalExclusionStatus := .openObligation

/-- The second handwritten target lemma: the accepted tower witness has exactly
the normalized centered boundary-address normal form. -/
def G8BookIIIAcceptedTowerRealizationAligned
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (data : G8BookIIIAcceptedTowerRealizationData model z) : Prop :=
  model.normalForm data.witness =
    (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf

/-- Accepted tower realization data plus alignment gives the pointwise
accepted-realization certificate from the existing final spine. -/
def G8BookIIIAcceptedTowerRealizationData.toCertificate
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (data : G8BookIIIAcceptedTowerRealizationData model z)
    (hAligned : G8BookIIIAcceptedTowerRealizationAligned data) :
    G8BookIIICharacterAcceptedRealizationCertificate model z where
  readout := orthodoxXiCarrierBoundaryCharacterReadout z
  readout_canonical := rfl
  factor := bookIII_orthodoxXiBoundaryCharacter_factors z
  witness := data.witness
  accepted := data.accepted
  normalForm := hAligned
  status := data.status

/-- Accepted tower realization data plus alignment gives D5 accepted centered
address admission. -/
theorem G8BookIIIAcceptedTowerRealizationData.toTowerAdmitsCenteredAddress
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (data : G8BookIIIAcceptedTowerRealizationData model z)
    (hAligned : G8BookIIIAcceptedTowerRealizationAligned data) :
    G8BookIIITowerAdmitsCenteredAddress model z :=
  (data.toCertificate hAligned).toTowerAdmitsCenteredAddress

-- ============================================================
-- GLOBAL PROOF PACKAGE
-- ============================================================

/-- Proof package corresponding to the two handwritten target lemmas.

This is the exact last-mile Lean target: no accepted witness is manufactured
here.  The implementer must supply `realizationData` and `normalFormAligned`
from Book III character/tower machinery. -/
structure G8BookIIICharacterAcceptedRealizationProofPackage
    (model : G8BookIIITowerAcceptedSpectralWitnessModel) where
  realizationData :
    ∀ z : OrthodoxXiZeroCarrier,
      G8BookIIIAcceptedTowerRealizationData model z
  normalFormAligned :
    ∀ z : OrthodoxXiZeroCarrier,
      G8BookIIIAcceptedTowerRealizationAligned (realizationData z)
  status : G8OffCriticalExclusionStatus := .openObligation

/-- Pointwise certificate selected by a proof package. -/
def G8BookIIICharacterAcceptedRealizationProofPackage.certificate
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (pkg : G8BookIIICharacterAcceptedRealizationProofPackage model)
    (z : OrthodoxXiZeroCarrier) :
    G8BookIIICharacterAcceptedRealizationCertificate model z :=
  (pkg.realizationData z).toCertificate (pkg.normalFormAligned z)

/-- A proof package supplies the stronger pointwise realization interface. -/
def G8BookIIICharacterAcceptedRealizationProofPackage.toAcceptedRealization
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (pkg : G8BookIIICharacterAcceptedRealizationProofPackage model) :
    G8BookIIICharacterAcceptedRealization model where
  acceptedWitnessOf := by
    intro z _readout _hFactor
    exact (pkg.realizationData z).witness
  acceptedWitness_accepted := by
    intro z _readout _hFactor
    exact (pkg.realizationData z).accepted
  acceptedWitness_normalForm := by
    intro z _readout _hFactor
    exact pkg.normalFormAligned z
  status := pkg.status

/-- A proof package gives pointwise accepted-realization coverage for all
Mathlib nontrivial zeta zeros through the existing receiving-side coverage. -/
theorem G8BookIIICharacterAcceptedRealizationProofPackage.realizationCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (pkg : G8BookIIICharacterAcceptedRealizationProofPackage model) :
    G8BookIIICharacterAcceptedRealizationCoversMathlibNontrivialZetaZeros
      model :=
  pkg.toAcceptedRealization.realizationCoverage

/-- A proof package gives D5 accepted-carrier coverage. -/
theorem G8BookIIICharacterAcceptedRealizationProofPackage.acceptedXiCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (pkg : G8BookIIICharacterAcceptedRealizationProofPackage model) :
    G8BookIIIAcceptedXiCoversMathlibNontrivialZetaZeros model :=
  g8BookIIICharacterAcceptedRealizationCoverage_toAcceptedXiCoverage
    pkg.realizationCoverage

/-- Conditional receiving-side handoff from the proof package. -/
theorem G8BookIIICharacterAcceptedRealizationProofPackage.mathlibRiemannHypothesis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (pkg : G8BookIIICharacterAcceptedRealizationProofPackage model) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_from_characterAcceptedRealizationCoverage
    pkg.realizationCoverage

-- ============================================================
-- POINTWISE RED-TEAM FALSIFIER
-- ============================================================

/-- Pointwise falsifier for the accepted-realization route.

It records the theorem-backed canonical no-rogue B/C readout for a carrier
and the failure of any accepted tower witness to align with that carrier's
normalized centered boundary address. -/
structure G8BookIIIAcceptedRealizationPointwiseFalsifier
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (z : OrthodoxXiZeroCarrier) where
  readout : G8BookIIIBoundaryCharacterReadout z
  readout_canonical :
    readout = orthodoxXiCarrierBoundaryCharacterReadout z
  admissible :
    G8BookIIIAdmissibleGlobalCharacter readout.character
  noRogueFactor :
    G8BookIIITauBipolarFactorization readout.character
  noAcceptedAlignedWitness :
    ∀ data : G8BookIIIAcceptedTowerRealizationData model z,
      ¬ G8BookIIIAcceptedTowerRealizationAligned data
  status : G8OffCriticalExclusionStatus := .offAxisGhostPressure

/-- Canonical no-rogue readout plus a no-aligned-witness proof gives the
pointwise red-team falsifier. -/
def G8BookIIIAcceptedRealizationPointwiseFalsifier.canonical
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (hNoAligned :
      ∀ data : G8BookIIIAcceptedTowerRealizationData model z,
        ¬ G8BookIIIAcceptedTowerRealizationAligned data) :
    G8BookIIIAcceptedRealizationPointwiseFalsifier model z where
  readout := orthodoxXiCarrierBoundaryCharacterReadout z
  readout_canonical := rfl
  admissible :=
    bookIII_boundaryCharacter_admissible
      (orthodoxXiCarrierBoundaryCharacterReadout z).character
  noRogueFactor := bookIII_orthodoxXiBoundaryCharacter_factors z
  noAcceptedAlignedWitness := hNoAligned

/-- The pointwise falsifier refutes any global proof package. -/
theorem G8BookIIIAcceptedRealizationPointwiseFalsifier.refutesProofPackage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (falsifier :
      G8BookIIIAcceptedRealizationPointwiseFalsifier model z)
    (pkg : G8BookIIICharacterAcceptedRealizationProofPackage model) :
    False :=
  falsifier.noAcceptedAlignedWitness
    (pkg.realizationData z)
    (pkg.normalFormAligned z)

/-- A pointwise falsifier rules out the corresponding accepted-realization
certificate. -/
theorem G8BookIIIAcceptedRealizationPointwiseFalsifier.refutesCertificate
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (falsifier :
      G8BookIIIAcceptedRealizationPointwiseFalsifier model z)
    (cert : G8BookIIICharacterAcceptedRealizationCertificate model z) :
    False := by
  let data : G8BookIIIAcceptedTowerRealizationData model z :=
    { witness := cert.witness
      accepted := cert.accepted
      status := cert.status }
  exact falsifier.noAcceptedAlignedWitness data cert.normalForm

/-- A pointwise falsifier rules out D5 accepted centered-address admission for
the same carrier. -/
theorem G8BookIIIAcceptedRealizationPointwiseFalsifier.refutesTowerAdmits
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (falsifier :
      G8BookIIIAcceptedRealizationPointwiseFalsifier model z)
    (hAdmits : G8BookIIITowerAdmitsCenteredAddress model z) :
    False :=
  falsifier.refutesCertificate
    (G8BookIIICharacterAcceptedRealizationCertificate.ofTowerAdmitsCenteredAddress
      hAdmits)

end Tau.BookIII.Bridge
