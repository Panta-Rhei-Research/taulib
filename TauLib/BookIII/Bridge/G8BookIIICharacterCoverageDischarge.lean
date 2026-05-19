import TauLib.BookIII.Bridge.G8PrimeCharacterCoverage
import TauLib.BookIII.Sectors.BoundaryCharacters
import TauLib.BookII.CentralTheorem.BoundaryCharacters
import TauLib.BookII.Hartogs.MutualDetermination

/-!
# TauLib.BookIII.Bridge.G8BookIIICharacterCoverageDischarge

Book III character-algebra discharge for the D5 coverage hinge.

This module theorem-backs the no-rogue-channel part of the prime-character
route.  The receiving-side `xi` carrier is assigned a concrete Book III
boundary character whose two coordinates are the B/C coordinates of its
centered boundary normal form.  Book III/II character checks then give
admissibility evidence, and the two-coordinate `BoundaryCharacter` type gives
tau-bipolar factorization.

The final accepted tower realization remains an explicit field.  This module
does not prove determinant correspondence, completion uniqueness, full divisor
transfer, or an unconditional receiving-side theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Sectors

-- ============================================================
-- CONCRETE BOOK III BOUNDARY-CHARACTER READOUT
-- ============================================================

/-- Concrete Book III boundary character read from the centered `xi` boundary
    address.  The two character indices are precisely the B/C coordinates of
    the normalized boundary normal form. -/
def orthodoxXiCarrierBoundaryCharacter
    (z : OrthodoxXiZeroCarrier) :
    BoundaryCharacter where
  m_index :=
    Int.ofNat
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf.b_part
  n_index :=
    Int.ofNat
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf.c_part

/-- Pointwise readout package: a boundary character together with the proof
    that it is the selected centered-address character for this `xi` carrier. -/
structure G8BookIIIBoundaryCharacterReadout
    (z : OrthodoxXiZeroCarrier) : Type 2 where
  character : BoundaryCharacter
  selected :
    character = orthodoxXiCarrierBoundaryCharacter z

/-- The canonical pointwise Book III boundary-character readout. -/
def orthodoxXiCarrierBoundaryCharacterReadout
    (z : OrthodoxXiZeroCarrier) :
    G8BookIIIBoundaryCharacterReadout z where
  character := orthodoxXiCarrierBoundaryCharacter z
  selected := rfl

-- ============================================================
-- ADMISSIBLE GLOBAL CHARACTER EVIDENCE
-- ============================================================

/-- Book III/II evidence that a Book III boundary character is admissible as a
    global character for the present bridge layer.

The fields deliberately package existing theorem-backed finite/tower
coherence and idempotent-support checks.  The character itself already has
only B/C coordinates; these fields record that this two-channel object is the
right Book III character-algebra surface. -/
structure G8BookIIIAdmissibleGlobalCharacter
    (_chi : BoundaryCharacter) : Prop where
  bookIII_boundaryCharacter :
    Tau.BookIII.Sectors.boundary_char_check 3 3 = true
  bookIII_boundaryToInterior :
    Tau.BookIII.Sectors.bti_functor_check 5 3 = true
  bookIII_boundaryToInterior_additive :
    Tau.BookIII.Sectors.bti_additive_check 3 3 = true
  bookII_idempotentCharacterAlgebra :
    Tau.BookII.CentralTheorem.full_boundary_characters_check 15 3 = true
  bookII_mutualDetermination :
    Tau.BookII.Hartogs.full_mutual_determination_check 10 4 = true

/-- Every Book III boundary character carries the current theorem-backed
    admissibility evidence. -/
theorem bookIII_boundaryCharacter_admissible
    (chi : BoundaryCharacter) :
    G8BookIIIAdmissibleGlobalCharacter chi where
  bookIII_boundaryCharacter :=
    Tau.BookIII.Sectors.boundary_char_3_3
  bookIII_boundaryToInterior :=
    Tau.BookIII.Sectors.bti_functor_5_3
  bookIII_boundaryToInterior_additive :=
    Tau.BookIII.Sectors.bti_additive_3_3
  bookII_idempotentCharacterAlgebra :=
    Tau.BookII.CentralTheorem.full_bnd_char_15_3
  bookII_mutualDetermination :=
    Tau.BookII.Hartogs.full_mutual_determination

/-- The selected centered-address character is admissible. -/
theorem bookIII_orthodoxXiBoundaryCharacter_admissible
    (z : OrthodoxXiZeroCarrier) :
    G8BookIIIAdmissibleGlobalCharacter
      (orthodoxXiCarrierBoundaryCharacter z) :=
  bookIII_boundaryCharacter_admissible
    (orthodoxXiCarrierBoundaryCharacter z)

-- ============================================================
-- NO-ROGUE-CHANNEL FACTORIZATION
-- ============================================================

/-- Tau-bipolar factorization for a Book III boundary character.

This is the localization-relevant no-third-channel shape: a Book III
`BoundaryCharacter` has exactly a B-channel index and a C-channel index. -/
def G8BookIIITauBipolarFactorization
    (chi : BoundaryCharacter) : Prop :=
  ∃ bIndex cIndex : Int,
    chi = { m_index := bIndex, n_index := cIndex }

/-- Every Book III boundary character factors through the two tau-bipolar
    channels by its constructor. -/
theorem bookIII_boundaryCharacter_factorsThroughTauBipolar
    (chi : BoundaryCharacter) :
    G8BookIIITauBipolarFactorization chi := by
  refine ⟨chi.m_index, chi.n_index, ?_⟩
  cases chi
  rfl

/-- No admissible Book III boundary character has a third asymptotic channel.

The admissibility evidence records that the object is the Book III/II
character-algebra surface; the actual exclusion is theorem-backed by the
two-coordinate `BoundaryCharacter` shape. -/
theorem bookIII_noRogueThirdChannel
    (chi : BoundaryCharacter)
    (_hAdmissible : G8BookIIIAdmissibleGlobalCharacter chi) :
    G8BookIIITauBipolarFactorization chi :=
  bookIII_boundaryCharacter_factorsThroughTauBipolar chi

/-- The selected centered-address character factors through the two
    tau-bipolar channels. -/
theorem bookIII_orthodoxXiBoundaryCharacter_factors
    (z : OrthodoxXiZeroCarrier) :
    G8BookIIITauBipolarFactorization
      (orthodoxXiCarrierBoundaryCharacter z) :=
  bookIII_noRogueThirdChannel
    (orthodoxXiCarrierBoundaryCharacter z)
    (bookIII_orthodoxXiBoundaryCharacter_admissible z)

-- ============================================================
-- ACCEPTED TOWER REALIZATION INTERFACE
-- ============================================================

/-- Remaining accepted-carrier realization law.

The character algebra above supplies a concrete readout, admissibility, and
no-rogue-channel factorization.  The load-bearing next theorem is that the
factorized pointwise readout is realized by an accepted Book III tower witness
whose normal form is the centered boundary address. -/
structure G8BookIIICharacterAcceptedRealization
    (model : G8BookIIITowerAcceptedSpectralWitnessModel) where
  acceptedWitnessOf :
    ∀ (z : OrthodoxXiZeroCarrier)
      (readout : G8BookIIIBoundaryCharacterReadout z),
      G8BookIIITauBipolarFactorization readout.character →
        model.spectralWitness
  acceptedWitness_accepted :
    ∀ (z : OrthodoxXiZeroCarrier)
      (readout : G8BookIIIBoundaryCharacterReadout z)
      (hFactor :
        G8BookIIITauBipolarFactorization readout.character),
      model.IsAccepted (acceptedWitnessOf z readout hFactor)
  acceptedWitness_normalForm :
    ∀ (z : OrthodoxXiZeroCarrier)
      (readout : G8BookIIIBoundaryCharacterReadout z)
      (hFactor :
        G8BookIIITauBipolarFactorization readout.character),
      model.normalForm (acceptedWitnessOf z readout hFactor) =
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf
  status : G8OffCriticalExclusionStatus := .openObligation

/-- The accepted witness selected by the Book III character realization law. -/
def G8BookIIICharacterAcceptedRealization.acceptedWitness
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization : G8BookIIICharacterAcceptedRealization model)
    (z : OrthodoxXiZeroCarrier) :
    model.spectralWitness :=
  realization.acceptedWitnessOf
    z
    (orthodoxXiCarrierBoundaryCharacterReadout z)
    (bookIII_orthodoxXiBoundaryCharacter_factors z)

/-- The selected witness is accepted by the tower model. -/
theorem G8BookIIICharacterAcceptedRealization.acceptedWitness_isAccepted
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization : G8BookIIICharacterAcceptedRealization model)
    (z : OrthodoxXiZeroCarrier) :
    model.IsAccepted (realization.acceptedWitness z) :=
  realization.acceptedWitness_accepted
    z
    (orthodoxXiCarrierBoundaryCharacterReadout z)
    (bookIII_orthodoxXiBoundaryCharacter_factors z)

/-- The selected witness has the centered boundary-address normal form. -/
theorem G8BookIIICharacterAcceptedRealization.acceptedWitness_normalForm_eq
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization : G8BookIIICharacterAcceptedRealization model)
    (z : OrthodoxXiZeroCarrier) :
    model.normalForm (realization.acceptedWitness z) =
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf :=
  realization.acceptedWitness_normalForm
    z
    (orthodoxXiCarrierBoundaryCharacterReadout z)
    (bookIII_orthodoxXiBoundaryCharacter_factors z)

-- ============================================================
-- ADAPTER INTO PRIME-CHARACTER COVERAGE
-- ============================================================

/-- Book III character algebra plus the remaining accepted-realization law
    instantiates the generic prime-character coverage context. -/
def G8BookIIICharacterAcceptedRealization.toPrimeCharacterCoverageContext
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization : G8BookIIICharacterAcceptedRealization model) :
    G8PrimeCharacterCoverageContext model where
  characterReadout := fun z => G8BookIIIBoundaryCharacterReadout z
  boundaryCharacterOf := orthodoxXiCarrierBoundaryCharacterReadout
  isAdmissibleGlobalCharacter := fun _ readout =>
    G8BookIIIAdmissibleGlobalCharacter readout.character
  boundaryCharacter_admissible := by
    intro z
    exact
      bookIII_boundaryCharacter_admissible
        (orthodoxXiCarrierBoundaryCharacterReadout z).character
  factorsThroughTauBipolarBoundary := fun _ readout =>
    G8BookIIITauBipolarFactorization readout.character
  noRogueThirdChannel := by
    intro _ readout hAdmissible
    exact bookIII_noRogueThirdChannel readout.character hAdmissible
  acceptedWitnessOf := by
    intro z readout hFactor
    exact realization.acceptedWitnessOf z readout hFactor
  acceptedWitness_accepted := by
    intro z readout hFactor
    exact realization.acceptedWitness_accepted z readout hFactor
  acceptedWitness_normalForm := by
    intro z readout hFactor
    exact realization.acceptedWitness_normalForm z readout hFactor
  status := realization.status

/-- Accepted-carrier coverage obtained from Book III character algebra plus
    accepted realization. -/
theorem G8BookIIICharacterAcceptedRealization.acceptedXiCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization : G8BookIIICharacterAcceptedRealization model) :
    G8BookIIIAcceptedXiCoversMathlibNontrivialZetaZeros model :=
  realization.toPrimeCharacterCoverageContext.acceptedXiCoverage

/-- Conditional receiving-side handoff through the existing D5 theorem,
    consuming the explicit accepted-realization law. -/
theorem G8BookIIICharacterAcceptedRealization.mathlibRiemannHypothesis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization : G8BookIIICharacterAcceptedRealization model) :
    RiemannHypothesis :=
  realization.toPrimeCharacterCoverageContext.mathlibRiemannHypothesis

-- ============================================================
-- INTERFACE CHECKS
-- ============================================================

#check orthodoxXiCarrierBoundaryCharacter
#check bookIII_boundaryCharacter_admissible
#check bookIII_noRogueThirdChannel
#check G8BookIIICharacterAcceptedRealization.toPrimeCharacterCoverageContext
#check G8BookIIICharacterAcceptedRealization.acceptedXiCoverage

end Tau.BookIII.Bridge
