import TauLib.BookIII.Bridge.G8BookIIICharacterCoverageDischarge

/-!
# TauLib.BookIII.Bridge.G8BookIIICharacterAcceptedRealizationLaw

Accepted-realization law for the Book III character coverage route.

The preceding discharge theorem-backs the character-algebra side: the centered
`xi` carrier has a concrete Book III boundary-character readout, that readout
is admissible, and it factors through exactly the B/C channels.  This module
turns the remaining hinge into a pointwise certificate and a global coverage
target.

The global coverage target remains an explicit hypothesis unless supplied by
later Book III character/tower machinery.  No new axioms or sorries are used.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- POINTWISE ACCEPTED-REALIZATION CERTIFICATE
-- ============================================================

/-- Pointwise accepted realization of the canonical Book III character readout
    attached to an orthodox `xi` carrier.

The certificate records the canonical readout, its two-channel factorization,
and an accepted Book III tower witness aligned to the centered boundary
address. -/
structure G8BookIIICharacterAcceptedRealizationCertificate
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (z : OrthodoxXiZeroCarrier) where
  readout : G8BookIIIBoundaryCharacterReadout z
  readout_canonical :
    readout = orthodoxXiCarrierBoundaryCharacterReadout z
  factor :
    G8BookIIITauBipolarFactorization readout.character
  witness : model.spectralWitness
  accepted : model.IsAccepted witness
  normalForm :
    model.normalForm witness =
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf
  status : G8OffCriticalExclusionStatus := .openObligation

/-- The canonical readout carried by a pointwise certificate is admissible. -/
theorem G8BookIIICharacterAcceptedRealizationCertificate.readout_admissible
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (cert :
      G8BookIIICharacterAcceptedRealizationCertificate model z) :
    G8BookIIIAdmissibleGlobalCharacter cert.readout.character := by
  exact bookIII_boundaryCharacter_admissible cert.readout.character

/-- A pointwise accepted-realization certificate gives D5 accepted centered
    address admission. -/
theorem G8BookIIICharacterAcceptedRealizationCertificate.toTowerAdmitsCenteredAddress
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (cert :
      G8BookIIICharacterAcceptedRealizationCertificate model z) :
    G8BookIIITowerAdmitsCenteredAddress model z :=
  ⟨cert.witness, cert.accepted, cert.normalForm⟩

/-- D5 accepted centered-address admission gives the pointwise character
    accepted-realization certificate, using the theorem-backed canonical
    readout and no-rogue factorization. -/
def G8BookIIICharacterAcceptedRealizationCertificate.ofTowerAdmitsCenteredAddress
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (hAdmits : G8BookIIITowerAdmitsCenteredAddress model z) :
    G8BookIIICharacterAcceptedRealizationCertificate model z where
  readout := orthodoxXiCarrierBoundaryCharacterReadout z
  readout_canonical := rfl
  factor := bookIII_orthodoxXiBoundaryCharacter_factors z
  witness := Classical.choose hAdmits
  accepted := (Classical.choose_spec hAdmits).1
  normalForm := (Classical.choose_spec hAdmits).2

/-- Pointwise accepted realization is equivalent to D5 accepted
    centered-address admission. -/
theorem g8BookIIICharacterAcceptedRealizationCertificate_iff_towerAdmits
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (z : OrthodoxXiZeroCarrier) :
    Nonempty (G8BookIIICharacterAcceptedRealizationCertificate model z) ↔
      G8BookIIITowerAdmitsCenteredAddress model z := by
  constructor
  · rintro ⟨cert⟩
    exact cert.toTowerAdmitsCenteredAddress
  · intro hAdmits
    exact
      ⟨G8BookIIICharacterAcceptedRealizationCertificate.ofTowerAdmitsCenteredAddress
        (model := model) (z := z) hAdmits⟩

/-- A nonempty pointwise accepted-realization certificate gives D5 accepted
    centered-address admission. -/
theorem G8BookIIICharacterAcceptedRealizationCertificate.nonempty_toTowerAdmitsCenteredAddress
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (hCert :
      Nonempty (G8BookIIICharacterAcceptedRealizationCertificate model z)) :
    G8BookIIITowerAdmitsCenteredAddress model z :=
  (g8BookIIICharacterAcceptedRealizationCertificate_iff_towerAdmits
    model z).mp hCert

/-- A pointwise accepted-realization certificate rejects carrier-level
    off-criticality. -/
theorem G8BookIIICharacterAcceptedRealizationCertificate.notCarrierOffCritical
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (cert :
      G8BookIIICharacterAcceptedRealizationCertificate model z) :
    ¬ OrthodoxXiCarrierOffCritical z :=
  g8BookIIITowerAdmitsCenteredAddress_notCarrierOffCritical
    model z cert.toTowerAdmitsCenteredAddress

/-- A pointwise accepted-realization certificate refutes thin off-axis
    classification for any actual thin source. -/
theorem G8BookIIICharacterAcceptedRealizationCertificate.refutesThinOffAxis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (source : G8ActualXiZetaThinSourceContext)
    {z : OrthodoxXiZeroCarrier}
    (cert :
      G8BookIIICharacterAcceptedRealizationCertificate model z)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    False :=
  g8BookIIITowerAdmitsCenteredAddress_refutesThinOffAxis
    model source z cert.toTowerAdmitsCenteredAddress hOffAxis

/-- A pointwise accepted-realization certificate rejects thin off-axis
    classification. -/
theorem G8BookIIICharacterAcceptedRealizationCertificate.notThinOffAxis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (source : G8ActualXiZetaThinSourceContext)
    {z : OrthodoxXiZeroCarrier}
    (cert :
      G8BookIIICharacterAcceptedRealizationCertificate model z) :
    ¬ G8ActualXiZetaThinChartOffAxis source z := by
  intro hOffAxis
  exact cert.refutesThinOffAxis source hOffAxis

-- ============================================================
-- GLOBAL ACCEPTED-REALIZATION COVERAGE TARGET
-- ============================================================

/-- Minimal accepted-realization coverage target for the Book III character
    route.

Every Mathlib nontrivial zeta zero is represented by an orthodox `xi` carrier
with a pointwise accepted-realization certificate.  This is the exact remaining
coverage law; this module records and routes it, but does not assert it
globally. -/
def G8BookIIICharacterAcceptedRealizationCoversMathlibNontrivialZetaZeros
    (model : G8BookIIITowerAcceptedSpectralWitnessModel) : Prop :=
  ∀ (s : ℂ),
    riemannZeta s = 0 →
    (¬ ∃ n : ℕ, s = -2 * (n + 1)) →
    s ≠ 1 →
      ∃ z : OrthodoxXiZeroCarrier,
        z.toZero.point = s ∧
          Nonempty (G8BookIIICharacterAcceptedRealizationCertificate model z)

/-- Pointwise accepted-realization coverage implies the D5 accepted-carrier
    coverage target. -/
theorem g8BookIIICharacterAcceptedRealizationCoverage_toAcceptedXiCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (coverage :
      G8BookIIICharacterAcceptedRealizationCoversMathlibNontrivialZetaZeros
        model) :
    G8BookIIIAcceptedXiCoversMathlibNontrivialZetaZeros model := by
  intro s hz hNotTrivial hNotPole
  obtain ⟨z, hPoint, hCert⟩ :=
    coverage s hz hNotTrivial hNotPole
  exact
    ⟨⟨z,
        G8BookIIICharacterAcceptedRealizationCertificate.nonempty_toTowerAdmitsCenteredAddress
          (model := model) (z := z) hCert⟩,
      hPoint⟩

/-- Conditional receiving-side handoff from the pointwise
    accepted-realization coverage law. -/
theorem mathlibRiemannHypothesis_from_characterAcceptedRealizationCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (coverage :
      G8BookIIICharacterAcceptedRealizationCoversMathlibNontrivialZetaZeros
        model) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_from_acceptedXiCoverage
    (g8BookIIICharacterAcceptedRealizationCoverage_toAcceptedXiCoverage
      coverage)

-- ============================================================
-- COMPATIBILITY WITH THE STRONGER POINTWISE REALIZATION INTERFACE
-- ============================================================

/-- The stronger pointwise realization interface supplies a certificate for
    every orthodox `xi` carrier. -/
def G8BookIIICharacterAcceptedRealization.certificate
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization : G8BookIIICharacterAcceptedRealization model)
    (z : OrthodoxXiZeroCarrier) :
    G8BookIIICharacterAcceptedRealizationCertificate model z where
  readout := orthodoxXiCarrierBoundaryCharacterReadout z
  readout_canonical := rfl
  factor := bookIII_orthodoxXiBoundaryCharacter_factors z
  witness := realization.acceptedWitness z
  accepted := realization.acceptedWitness_isAccepted z
  normalForm := realization.acceptedWitness_normalForm_eq z
  status := realization.status

/-- The stronger pointwise realization interface gives the minimal accepted
    realization coverage target, using the existing receiving-side
    `zeta -> xi` carrier coverage theorem. -/
theorem G8BookIIICharacterAcceptedRealization.realizationCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization : G8BookIIICharacterAcceptedRealization model) :
    G8BookIIICharacterAcceptedRealizationCoversMathlibNontrivialZetaZeros
      model := by
  intro s hz hNotTrivial hNotPole
  obtain ⟨z, hPoint⟩ :=
    g8XiCoversMathlibNontrivialZetaZeros
      s hz hNotTrivial hNotPole
  let carrier : OrthodoxXiZeroCarrier := z.toCarrier
  refine ⟨carrier, ?_, ⟨realization.certificate carrier⟩⟩
  simpa [carrier, OrthodoxXiZero.toCarrier, OrthodoxXiZeroCarrier.toZero]
    using hPoint

/-- The stronger pointwise realization interface reaches the same D5
    accepted-carrier coverage target through the minimal coverage law. -/
theorem G8BookIIICharacterAcceptedRealization.acceptedXiCoverage_fromLaw
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization : G8BookIIICharacterAcceptedRealization model) :
    G8BookIIIAcceptedXiCoversMathlibNontrivialZetaZeros model :=
  g8BookIIICharacterAcceptedRealizationCoverage_toAcceptedXiCoverage
    realization.realizationCoverage

/-- Conditional receiving-side handoff through the minimal coverage law for
    the stronger pointwise realization interface. -/
theorem G8BookIIICharacterAcceptedRealization.mathlibRiemannHypothesis_fromLaw
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (realization : G8BookIIICharacterAcceptedRealization model) :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_from_characterAcceptedRealizationCoverage
    realization.realizationCoverage

-- ============================================================
-- INTERFACE CHECKS
-- ============================================================

#check G8BookIIICharacterAcceptedRealizationCertificate
#check g8BookIIICharacterAcceptedRealizationCertificate_iff_towerAdmits
#check G8BookIIICharacterAcceptedRealizationCoversMathlibNontrivialZetaZeros
#check g8BookIIICharacterAcceptedRealizationCoverage_toAcceptedXiCoverage
#check mathlibRiemannHypothesis_from_characterAcceptedRealizationCoverage

end Tau.BookIII.Bridge
