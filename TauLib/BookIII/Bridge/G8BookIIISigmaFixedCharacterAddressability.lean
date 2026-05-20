import TauLib.BookIII.Bridge.G8BookIIICharacterAcceptedRealizationReduction

/-!
# TauLib.BookIII.Bridge.G8BookIIISigmaFixedCharacterAddressability

Sigma-fixed character addressability for the G8 accepted-realization hinge.

The no-rogue-channel layer proves that the canonical `xi` boundary character is
two-channel.  This module separates that fact from the stronger Book III
acceptance requirement: the accepted tower carrier is B/C-balanced, so the
remaining realization route must pass through a sigma-fixed, B=C character and
then supply an accepted tower witness with exact centered-address normal form.

This module is an interface/proof-shape layer.  It does not prove the actual
`xi` sigma-fixed theorem, construct global accepted witnesses, prove O3, prove
full divisor transfer, or claim an unconditional receiving-side theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Sectors
open Tau.BookIII.Spectral

-- ============================================================
-- SIGMA-FIXED BOUNDARY CHARACTERS
-- ============================================================

/-- A Book III boundary character is sigma-fixed when its B and C channel
    indices agree.  This is the formal B=C diagonal in the two-channel
    character lattice. -/
def G8BoundaryCharacterSigmaFixed
    (chi : BoundaryCharacter) : Prop :=
  chi.m_index = chi.n_index

/-- The canonical centered `xi` boundary character is sigma-fixed.  This is the
    first real remaining `xi`-chart theorem target; it is recorded pointwise
    rather than asserted globally. -/
def G8XiBoundaryCharacterSigmaFixed
    (z : OrthodoxXiZeroCarrier) : Prop :=
  G8BoundaryCharacterSigmaFixed (orthodoxXiCarrierBoundaryCharacter z)

/-- Global target: every canonical `xi` boundary character is sigma-fixed.

This is intentionally a proposition, not a theorem in this module.  It must be
proved from the centered `xi` chart / functional symmetry, not from the final
RH conclusion. -/
def G8ActualXiBoundaryCharacterSigmaFixed : Prop :=
  ∀ z : OrthodoxXiZeroCarrier,
    G8XiBoundaryCharacterSigmaFixed z

/-- The canonical `xi` boundary character is always a two-channel B/C object. -/
theorem g8XiBoundaryCharacter_noRogue
    (z : OrthodoxXiZeroCarrier) :
    G8BookIIITauBipolarFactorization
      (orthodoxXiCarrierBoundaryCharacter z) :=
  bookIII_orthodoxXiBoundaryCharacter_factors z

/-- Sigma-fixedness of the canonical `xi` character is exactly B/C balance of
    the normalized centered boundary address. -/
theorem g8XiBoundaryCharacter_sigmaFixed_iff_centeredAddress_bcBalanced
    (z : OrthodoxXiZeroCarrier) :
    G8XiBoundaryCharacterSigmaFixed z ↔
      BCBalanced
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf := by
  unfold G8XiBoundaryCharacterSigmaFixed G8BoundaryCharacterSigmaFixed
    orthodoxXiCarrierBoundaryCharacter BCBalanced
  constructor
  · intro h
    exact Int.ofNat.inj h
  · intro h
    rw [h]

/-- A sigma-fixed canonical `xi` character supplies the centered-address
    B/C-balance fact used by the accepted tower carrier. -/
theorem G8XiBoundaryCharacterSigmaFixed.centeredAddress_bcBalanced
    {z : OrthodoxXiZeroCarrier}
    (hSigma : G8XiBoundaryCharacterSigmaFixed z) :
    BCBalanced
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf :=
  (g8XiBoundaryCharacter_sigmaFixed_iff_centeredAddress_bcBalanced z).mp
    hSigma

/-- B/C balance of the centered address supplies sigma-fixedness of the
    canonical `xi` boundary character. -/
theorem G8XiBoundaryCharacterSigmaFixed.of_centeredAddress_bcBalanced
    {z : OrthodoxXiZeroCarrier}
    (hBalanced :
      BCBalanced
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf) :
    G8XiBoundaryCharacterSigmaFixed z :=
  (g8XiBoundaryCharacter_sigmaFixed_iff_centeredAddress_bcBalanced z).mpr
    hBalanced

-- ============================================================
-- SIGMA-FIXED NF ADDRESSABILITY SURFACE
-- ============================================================

/-- NF-addressability evidence for a sigma-fixed Book III boundary character.

The fields mirror the Book III Ch. 41/42 proof shape at the bridge level:
sigma-fixed character data has a finite primorial depth, a normalized boundary
normal form, B/C balance, and exact alignment between the character indices and
the normal form.  This is still below accepted tower realization: it supplies
addressability evidence, not an accepted spectral witness by itself. -/
structure G8SigmaFixedNFAddressabilityCertificate
    (chi : BoundaryCharacter) where
  stage : Nat
  nf : BoundaryNF
  sigmaFixed : G8BoundaryCharacterSigmaFixed chi
  bcBalanced : BCBalanced nf
  character_nf_aligned :
    chi.m_index = Int.ofNat nf.b_part ∧
      chi.n_index = Int.ofNat nf.c_part
  status : G8OffCriticalExclusionStatus := .openObligation

/-- The NF addressability certificate keeps sigma-fixedness visible. -/
theorem G8SigmaFixedNFAddressabilityCertificate.sigmaFixedCharacter
    {chi : BoundaryCharacter}
    (cert : G8SigmaFixedNFAddressabilityCertificate chi) :
    G8BoundaryCharacterSigmaFixed chi :=
  cert.sigmaFixed

/-- The NF addressability certificate keeps B/C balance visible. -/
theorem G8SigmaFixedNFAddressabilityCertificate.centeredBalance
    {chi : BoundaryCharacter}
    (cert : G8SigmaFixedNFAddressabilityCertificate chi) :
    BCBalanced cert.nf :=
  cert.bcBalanced

/-- Exact aligned sigma-fixed character indices force B/C balance of the
    aligned normal form. -/
theorem g8SigmaFixedNFAddressability_bcBalanced_of_alignment
    {chi : BoundaryCharacter}
    {nf : BoundaryNF}
    (hSigma : G8BoundaryCharacterSigmaFixed chi)
    (hAligned :
      chi.m_index = Int.ofNat nf.b_part ∧
        chi.n_index = Int.ofNat nf.c_part) :
    BCBalanced nf := by
  unfold G8BoundaryCharacterSigmaFixed at hSigma
  unfold BCBalanced
  have hInt : Int.ofNat nf.b_part = Int.ofNat nf.c_part := by
    rw [← hAligned.1, ← hAligned.2]
    exact hSigma
  exact Int.ofNat.inj hInt

/-- Canonical `xi` NF-addressability certificates align with the centered
    boundary normal form exactly. -/
def G8XiSigmaFixedNFAddressability
    (z : OrthodoxXiZeroCarrier) : Prop :=
  ∃ cert :
      G8SigmaFixedNFAddressabilityCertificate
        (orthodoxXiCarrierBoundaryCharacter z),
    cert.nf =
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf

/-- A canonical `xi` NF-addressability certificate supplies sigma-fixedness of
    the pointwise boundary character. -/
theorem G8XiSigmaFixedNFAddressability.sigmaFixed
    {z : OrthodoxXiZeroCarrier}
    (hAddr : G8XiSigmaFixedNFAddressability z) :
    G8XiBoundaryCharacterSigmaFixed z := by
  rcases hAddr with ⟨cert, _hEq⟩
  exact cert.sigmaFixed

-- ============================================================
-- ACCEPTED REALIZATION FROM SIGMA-FIXED ADDRESSABILITY
-- ============================================================

/-- Remaining realization law after the no-rogue and sigma-fixed split.

For a sigma-fixed canonical `xi` character, Book III addressability supplies
NF evidence, and the accepted-tower realization law must select an accepted
tower witness whose normal form is exactly the centered boundary address. -/
structure G8BookIIIAcceptedTowerRealizationFromSigmaFixed
    (model : G8BookIIITowerAcceptedSpectralWitnessModel) where
  nfAddressability :
    ∀ (z : OrthodoxXiZeroCarrier),
      G8XiBoundaryCharacterSigmaFixed z →
        G8XiSigmaFixedNFAddressability z
  acceptedWitnessOf :
    ∀ (z : OrthodoxXiZeroCarrier),
      G8XiBoundaryCharacterSigmaFixed z →
        model.spectralWitness
  acceptedWitness_accepted :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hSigma : G8XiBoundaryCharacterSigmaFixed z),
      model.IsAccepted (acceptedWitnessOf z hSigma)
  acceptedWitness_normalForm :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hSigma : G8XiBoundaryCharacterSigmaFixed z),
      model.normalForm (acceptedWitnessOf z hSigma) =
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf
  status : G8OffCriticalExclusionStatus := .openObligation

/-- Sigma-fixed accepted realization gives the D5 centered-address admission
    target pointwise. -/
theorem G8BookIIIAcceptedTowerRealizationFromSigmaFixed.toTowerAdmits
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model)
    {z : OrthodoxXiZeroCarrier}
    (hSigma : G8XiBoundaryCharacterSigmaFixed z) :
    G8BookIIITowerAdmitsCenteredAddress model z :=
  ⟨realization.acceptedWitnessOf z hSigma,
    realization.acceptedWitness_accepted z hSigma,
    realization.acceptedWitness_normalForm z hSigma⟩

/-- The realization law supplies the named `sigma-fixed -> accepted witness`
    target, while keeping the sigma-fixed hypothesis explicit. -/
theorem sigmaFixedCharacter_to_acceptedTowerWitness
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model)
    (z : OrthodoxXiZeroCarrier)
    (hSigma : G8XiBoundaryCharacterSigmaFixed z) :
    G8BookIIITowerAdmitsCenteredAddress model z :=
  realization.toTowerAdmits hSigma

/-- Actual sigma-fixedness plus the sigma-fixed realization law gives the exact
    pointwise accepted centered-address coverage target. -/
theorem G8BookIIIAcceptedTowerRealizationFromSigmaFixed.pointwiseCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model)
    (hActualSigma : G8ActualXiBoundaryCharacterSigmaFixed) :
    G8BookIIIPointwiseAcceptedCenteredAddressCoverage model := by
  intro z
  exact realization.toTowerAdmits (hActualSigma z)

/-- Actual sigma-fixedness plus the sigma-fixed realization law gives the
    last-mile proof package. -/
def G8BookIIIAcceptedTowerRealizationFromSigmaFixed.toProofPackage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model)
    (hActualSigma : G8ActualXiBoundaryCharacterSigmaFixed) :
    G8BookIIICharacterAcceptedRealizationProofPackage model :=
  G8BookIIICharacterAcceptedRealizationProofPackage.ofPointwiseTowerCoverage
    (realization.pointwiseCoverage hActualSigma)

/-- Actual sigma-fixedness plus the sigma-fixed realization law gives the
    existing accepted realization interface. -/
def G8BookIIIAcceptedTowerRealizationFromSigmaFixed.toAcceptedRealization
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model)
    (hActualSigma : G8ActualXiBoundaryCharacterSigmaFixed) :
    G8BookIIICharacterAcceptedRealization model :=
  (realization.toProofPackage hActualSigma).toAcceptedRealization

/-- Conditional Mathlib handoff through the existing final spine. -/
theorem G8BookIIIAcceptedTowerRealizationFromSigmaFixed.mathlibRiemannHypothesis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model)
    (hActualSigma : G8ActualXiBoundaryCharacterSigmaFixed) :
    RiemannHypothesis :=
  (realization.toProofPackage hActualSigma).mathlibRiemannHypothesis

-- ============================================================
-- GUARDRAILS AND FALSIFIERS
-- ============================================================

/-- No-rogue character evidence without sigma-fixedness or accepted realization.

This record deliberately has no accepted tower witness field.  The remaining
target is still D5 centered-address admission. -/
structure G8NoRogueCharacterEvidenceOnly
    (z : OrthodoxXiZeroCarrier) where
  readout : G8BookIIIBoundaryCharacterReadout z
  readout_canonical :
    readout = orthodoxXiCarrierBoundaryCharacterReadout z
  noRogueFactor :
    G8BookIIITauBipolarFactorization readout.character

/-- Canonical no-rogue evidence for a centered `xi` carrier. -/
def G8NoRogueCharacterEvidenceOnly.canonical
    (z : OrthodoxXiZeroCarrier) :
    G8NoRogueCharacterEvidenceOnly z where
  readout := orthodoxXiCarrierBoundaryCharacterReadout z
  readout_canonical := rfl
  noRogueFactor := bookIII_orthodoxXiBoundaryCharacter_factors z

/-- No-rogue evidence alone leaves the accepted-realization target unchanged. -/
theorem G8NoRogueCharacterEvidenceOnly.remainingTarget_iff_towerAdmits
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (_guard : G8NoRogueCharacterEvidenceOnly z) :
    G8BookIIIAcceptedTowerAlignedRealizationExists model z ↔
      G8BookIIITowerAdmitsCenteredAddress model z :=
  g8AcceptedAlignedRealizationExists_iff_towerAdmits model z

/-- A two-channel canonical character that is not sigma-fixed refutes the
    global actual-sigma-fixed target. -/
structure G8TwoChannelButNotSigmaFixedWitness where
  z : OrthodoxXiZeroCarrier
  noRogue :
    G8BookIIITauBipolarFactorization
      (orthodoxXiCarrierBoundaryCharacter z)
  notSigmaFixed : ¬ G8XiBoundaryCharacterSigmaFixed z

/-- Canonical constructor for the two-channel-but-not-sigma-fixed falsifier. -/
def G8TwoChannelButNotSigmaFixedWitness.canonical
    {z : OrthodoxXiZeroCarrier}
    (hNotSigma : ¬ G8XiBoundaryCharacterSigmaFixed z) :
    G8TwoChannelButNotSigmaFixedWitness where
  z := z
  noRogue := g8XiBoundaryCharacter_noRogue z
  notSigmaFixed := hNotSigma

/-- Two-channel but non-sigma-fixed evidence refutes the actual-sigma target. -/
theorem G8TwoChannelButNotSigmaFixedWitness.refutesActualSigmaFixed
    (w : G8TwoChannelButNotSigmaFixedWitness) :
    ¬ G8ActualXiBoundaryCharacterSigmaFixed := by
  intro hActual
  exact w.notSigmaFixed (hActual w.z)

/-- A sigma-fixed carrier with no accepted centered-address admission refutes
    any sigma-fixed accepted-realization law for the model. -/
structure G8SigmaFixedWithoutAcceptedTowerWitness
    (model : G8BookIIITowerAcceptedSpectralWitnessModel) where
  z : OrthodoxXiZeroCarrier
  sigmaFixed : G8XiBoundaryCharacterSigmaFixed z
  notAdmitted : ¬ G8BookIIITowerAdmitsCenteredAddress model z

/-- Sigma-fixed-but-unadmitted evidence refutes the sigma-fixed realization
    law. -/
theorem G8SigmaFixedWithoutAcceptedTowerWitness.refutesRealization
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (w : G8SigmaFixedWithoutAcceptedTowerWitness model)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    False :=
  w.notAdmitted (realization.toTowerAdmits w.sigmaFixed)

/-- A selected sigma-fixed realization whose accepted witness has the wrong
    normal form refutes that realization object. -/
structure G8SigmaFixedRealizationNormalFormMismatch
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) where
  z : OrthodoxXiZeroCarrier
  sigmaFixed : G8XiBoundaryCharacterSigmaFixed z
  mismatch :
    model.normalForm
        (realization.acceptedWitnessOf z sigmaFixed) ≠
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf

/-- A normal-form mismatch refutes the selected sigma-fixed realization. -/
theorem G8SigmaFixedRealizationNormalFormMismatch.refutes
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model}
    (w : G8SigmaFixedRealizationNormalFormMismatch realization) :
    False :=
  w.mismatch
    (realization.acceptedWitness_normalForm w.z w.sigmaFixed)

/-- Accepted realization from sigma-fixed data rejects carrier-level
    off-criticality once actual sigma-fixedness is supplied. -/
theorem G8BookIIIAcceptedTowerRealizationFromSigmaFixed.notCarrierOffCritical
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model)
    (hActualSigma : G8ActualXiBoundaryCharacterSigmaFixed)
    (z : OrthodoxXiZeroCarrier) :
    ¬ OrthodoxXiCarrierOffCritical z :=
  g8BookIIITowerAdmitsCenteredAddress_notCarrierOffCritical
    model z (realization.toTowerAdmits (hActualSigma z))

/-- Accepted realization from sigma-fixed data refutes thin off-axis
    classification pointwise. -/
theorem G8BookIIIAcceptedTowerRealizationFromSigmaFixed.refutesThinOffAxis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model)
    {z : OrthodoxXiZeroCarrier}
    (hSigma : G8XiBoundaryCharacterSigmaFixed z)
    (source : G8ActualXiZetaThinSourceContext)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    False :=
  g8BookIIITowerAdmitsCenteredAddress_refutesThinOffAxis
    model source z (realization.toTowerAdmits hSigma) hOffAxis

end Tau.BookIII.Bridge
