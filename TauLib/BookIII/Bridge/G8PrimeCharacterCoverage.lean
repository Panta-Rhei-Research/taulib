import TauLib.BookIII.Bridge.G8BookIIITowerAdmissionLaw

/-!
# TauLib.BookIII.Bridge.G8PrimeCharacterCoverage

Prime-character coverage interface for the D5 accepted-carrier hinge.

The transcript-backed route says that the remaining global coverage theorem is
not a total off-axis admission law.  It is the no-rogue-channel law:

```text
Mathlib zeta zero
  -> orthodox xi carrier
  -> boundary character readout
  -> admissible global character
  -> tau-bipolar factorization
  -> accepted Book III tower address
```

This module packages that route as explicit proof fields and adapts it to the
existing D5 coverage target.  It does not prove the no-rogue-channel theorem,
O3, analytic-completion uniqueness, full divisor transfer, or an unconditional
receiving-side theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- PRIME-CHARACTER COVERAGE CONTEXT
-- ============================================================

/-- Prime-character coverage context for the accepted Book III tower carrier.

The hard content is kept explicit: an orthodox `xi` carrier has a boundary
character readout; that readout is admissible; the no-rogue-channel law forces
tau-bipolar factorization; and factorization supplies an accepted tower witness
whose normal form is the centered boundary address of the carrier.
-/
structure G8PrimeCharacterCoverageContext
    (model : G8BookIIITowerAcceptedSpectralWitnessModel) where
  characterReadout :
    OrthodoxXiZeroCarrier → Type 2
  boundaryCharacterOf :
    ∀ z : OrthodoxXiZeroCarrier,
      characterReadout z
  isAdmissibleGlobalCharacter :
    ∀ z : OrthodoxXiZeroCarrier,
      characterReadout z → Prop
  boundaryCharacter_admissible :
    ∀ z : OrthodoxXiZeroCarrier,
      isAdmissibleGlobalCharacter z (boundaryCharacterOf z)
  factorsThroughTauBipolarBoundary :
    ∀ z : OrthodoxXiZeroCarrier,
      characterReadout z → Prop
  noRogueThirdChannel :
    ∀ (z : OrthodoxXiZeroCarrier)
      (readout : characterReadout z),
      isAdmissibleGlobalCharacter z readout →
        factorsThroughTauBipolarBoundary z readout
  acceptedWitnessOf :
    ∀ (z : OrthodoxXiZeroCarrier)
      (readout : characterReadout z),
      factorsThroughTauBipolarBoundary z readout →
        model.spectralWitness
  acceptedWitness_accepted :
    ∀ (z : OrthodoxXiZeroCarrier)
      (readout : characterReadout z)
      (hFactor :
        factorsThroughTauBipolarBoundary z readout),
      model.IsAccepted (acceptedWitnessOf z readout hFactor)
  acceptedWitness_normalForm :
    ∀ (z : OrthodoxXiZeroCarrier)
      (readout : characterReadout z)
      (hFactor :
        factorsThroughTauBipolarBoundary z readout),
      model.normalForm (acceptedWitnessOf z readout hFactor) =
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf
  status : G8OffCriticalExclusionStatus := .openObligation

-- ============================================================
-- SELECTORS FOR THE TRANSCRIPT CHAIN
-- ============================================================

/-- The orthodox `xi` carrier has a boundary-character readout. -/
def G8PrimeCharacterCoverageContext.boundaryCharacter
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8PrimeCharacterCoverageContext model)
    (z : OrthodoxXiZeroCarrier) :
    ctx.characterReadout z :=
  ctx.boundaryCharacterOf z

/-- The selected boundary character is admissible as a global character. -/
theorem G8PrimeCharacterCoverageContext.boundaryCharacter_isAdmissible
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8PrimeCharacterCoverageContext model)
    (z : OrthodoxXiZeroCarrier) :
    ctx.isAdmissibleGlobalCharacter z (ctx.boundaryCharacter z) :=
  ctx.boundaryCharacter_admissible z

/-- The no-rogue-channel field turns admissibility into tau-bipolar
    factorization. -/
theorem G8PrimeCharacterCoverageContext.boundaryCharacter_factors
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8PrimeCharacterCoverageContext model)
    (z : OrthodoxXiZeroCarrier) :
    ctx.factorsThroughTauBipolarBoundary z (ctx.boundaryCharacter z) :=
  ctx.noRogueThirdChannel
    z (ctx.boundaryCharacter z)
    (ctx.boundaryCharacter_isAdmissible z)

/-- The accepted tower witness induced by a factorized boundary character. -/
def G8PrimeCharacterCoverageContext.acceptedWitness
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8PrimeCharacterCoverageContext model)
    (z : OrthodoxXiZeroCarrier) :
    model.spectralWitness :=
  ctx.acceptedWitnessOf
    z (ctx.boundaryCharacter z)
    (ctx.boundaryCharacter_factors z)

/-- The induced tower witness is accepted by the Book III model. -/
theorem G8PrimeCharacterCoverageContext.acceptedWitness_isAccepted
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8PrimeCharacterCoverageContext model)
    (z : OrthodoxXiZeroCarrier) :
    model.IsAccepted (ctx.acceptedWitness z) :=
  ctx.acceptedWitness_accepted
    z (ctx.boundaryCharacter z)
    (ctx.boundaryCharacter_factors z)

/-- The induced accepted witness has the centered boundary-address normal
    form. -/
theorem G8PrimeCharacterCoverageContext.acceptedWitness_normalForm_eq
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8PrimeCharacterCoverageContext model)
    (z : OrthodoxXiZeroCarrier) :
    model.normalForm (ctx.acceptedWitness z) =
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf :=
  ctx.acceptedWitness_normalForm
    z (ctx.boundaryCharacter z)
    (ctx.boundaryCharacter_factors z)

-- ============================================================
-- ADAPTERS INTO THE D5 ACCEPTED-CARRIER TARGET
-- ============================================================

/-- Prime-character coverage admits each orthodox `xi` carrier address into
    the accepted Book III tower carrier. -/
theorem G8PrimeCharacterCoverageContext.admitsCenteredAddress
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8PrimeCharacterCoverageContext model)
    (z : OrthodoxXiZeroCarrier) :
    G8BookIIITowerAdmitsCenteredAddress model z :=
  ⟨ctx.acceptedWitness z,
    ctx.acceptedWitness_isAccepted z,
    ctx.acceptedWitness_normalForm_eq z⟩

/-- Prime-character coverage discharges the D5 accepted-carrier coverage
    target, using the existing theorem-backed receiving-side `zeta -> xi`
    coverage bridge. -/
theorem G8PrimeCharacterCoverageContext.acceptedXiCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8PrimeCharacterCoverageContext model) :
    G8BookIIIAcceptedXiCoversMathlibNontrivialZetaZeros model := by
  intro s hz hNotTrivial hNotPole
  obtain ⟨z, hPoint⟩ :=
    g8XiCoversMathlibNontrivialZetaZeros
      s hz hNotTrivial hNotPole
  let carrier : OrthodoxXiZeroCarrier := z.toCarrier
  refine
    ⟨⟨carrier, ctx.admitsCenteredAddress carrier⟩, ?_⟩
  simpa [carrier, OrthodoxXiZero.toCarrier, OrthodoxXiZeroCarrier.toZero]
    using hPoint

/-- Conditional RH handoff from the prime-character coverage context.

This consumes the explicit no-rogue-channel coverage context through the D5
accepted-carrier theorem.  It is not an unconditional proof of the Mathlib RH
target. -/
theorem G8PrimeCharacterCoverageContext.mathlibRiemannHypothesis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8PrimeCharacterCoverageContext model) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_from_acceptedXiCoverage
    ctx.acceptedXiCoverage

-- ============================================================
-- INTERFACE CHECKS
-- ============================================================

#check G8PrimeCharacterCoverageContext
#check G8PrimeCharacterCoverageContext.boundaryCharacter_factors
#check G8PrimeCharacterCoverageContext.admitsCenteredAddress
#check G8PrimeCharacterCoverageContext.acceptedXiCoverage
#check G8PrimeCharacterCoverageContext.mathlibRiemannHypothesis

end Tau.BookIII.Bridge
