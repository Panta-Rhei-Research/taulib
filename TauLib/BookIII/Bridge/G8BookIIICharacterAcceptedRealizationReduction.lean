import TauLib.BookIII.Bridge.G8BookIIICharacterAcceptedRealizationProofDraft

/-!
# TauLib.BookIII.Bridge.G8BookIIICharacterAcceptedRealizationReduction

Accepted-realization coverage reduction for the G8 final spine.

The previous module split the last-mile proof package into two fields:
pointwise accepted tower realization data and exact normal-form alignment.  This
module proves that those fields are equivalent to the D5 accepted centered
address target.  It also keeps the red-team guardrails visible:

* finite address normalization and no-rogue character readout are reusable
  evidence, but they do not manufacture an accepted tower witness;
* exact `BoundaryNF` equality is the required alignment, with axis-offset
  agreement only a consequence;
* an accepted aligned witness over an off-axis source immediately refutes
  itself by the existing D4/D5 conflict.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- POINTWISE ACCEPTED-REALIZATION TARGET
-- ============================================================

/-- Pointwise existence of accepted realization data aligned to the centered
boundary address. -/
def G8BookIIIAcceptedTowerAlignedRealizationExists
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (z : OrthodoxXiZeroCarrier) : Prop :=
  ∃ data : G8BookIIIAcceptedTowerRealizationData model z,
    G8BookIIIAcceptedTowerRealizationAligned data

/-- Build realization data from D5 accepted centered-address admission. -/
def G8BookIIIAcceptedTowerRealizationData.ofTowerAdmits
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (hAdmits : G8BookIIITowerAdmitsCenteredAddress model z) :
    G8BookIIIAcceptedTowerRealizationData model z where
  witness := Classical.choose hAdmits
  accepted := (Classical.choose_spec hAdmits).1

/-- The realization data selected from D5 accepted centered-address admission is
exactly aligned with the centered boundary normal form. -/
theorem G8BookIIIAcceptedTowerRealizationData.ofTowerAdmits_aligned
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (hAdmits : G8BookIIITowerAdmitsCenteredAddress model z) :
    G8BookIIIAcceptedTowerRealizationAligned
      (G8BookIIIAcceptedTowerRealizationData.ofTowerAdmits hAdmits) :=
  (Classical.choose_spec hAdmits).2

/-- Pointwise accepted realization plus exact alignment is equivalent to D5
accepted centered-address admission. -/
theorem g8AcceptedAlignedRealizationExists_iff_towerAdmits
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (z : OrthodoxXiZeroCarrier) :
    G8BookIIIAcceptedTowerAlignedRealizationExists model z ↔
      G8BookIIITowerAdmitsCenteredAddress model z := by
  constructor
  · intro hExists
    rcases hExists with ⟨data, hAligned⟩
    exact data.toTowerAdmitsCenteredAddress hAligned
  · intro hAdmits
    exact
      ⟨G8BookIIIAcceptedTowerRealizationData.ofTowerAdmits hAdmits,
        G8BookIIIAcceptedTowerRealizationData.ofTowerAdmits_aligned
          hAdmits⟩

/-- A convenient forward selector from accepted realization data plus alignment
to the D5 target. -/
theorem G8BookIIIAcceptedTowerRealizationData.towerAdmits
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (data : G8BookIIIAcceptedTowerRealizationData model z)
    (hAligned : G8BookIIIAcceptedTowerRealizationAligned data) :
    G8BookIIITowerAdmitsCenteredAddress model z :=
  (g8AcceptedAlignedRealizationExists_iff_towerAdmits model z).mp
    ⟨data, hAligned⟩

-- ============================================================
-- POINTWISE RED-TEAM FALSIFIER REDUCTION
-- ============================================================

/-- No accepted aligned tower witness exists for this carrier. -/
def G8BookIIINoAcceptedAlignedTowerWitness
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (z : OrthodoxXiZeroCarrier) : Prop :=
  ∀ data : G8BookIIIAcceptedTowerRealizationData model z,
    ¬ G8BookIIIAcceptedTowerRealizationAligned data

/-- The pointwise red-team falsifier is equivalent to the absence of an
accepted aligned tower witness. -/
theorem g8AcceptedRealizationPointwiseFalsifier_iff_noAlignedWitness
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (z : OrthodoxXiZeroCarrier) :
    Nonempty (G8BookIIIAcceptedRealizationPointwiseFalsifier model z) ↔
      G8BookIIINoAcceptedAlignedTowerWitness model z := by
  constructor
  · intro hFalsifier
    rcases hFalsifier with ⟨falsifier⟩
    exact falsifier.noAcceptedAlignedWitness
  · intro hNoAligned
    exact
      ⟨G8BookIIIAcceptedRealizationPointwiseFalsifier.canonical
        hNoAligned⟩

/-- Absence of an accepted aligned tower witness is equivalent to failure of the
D5 accepted centered-address target. -/
theorem g8NoAcceptedAlignedWitness_iff_notTowerAdmits
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (z : OrthodoxXiZeroCarrier) :
    G8BookIIINoAcceptedAlignedTowerWitness model z ↔
      ¬ G8BookIIITowerAdmitsCenteredAddress model z := by
  constructor
  · intro hNoAligned hAdmits
    exact
      hNoAligned
        (G8BookIIIAcceptedTowerRealizationData.ofTowerAdmits hAdmits)
        (G8BookIIIAcceptedTowerRealizationData.ofTowerAdmits_aligned
          hAdmits)
  · intro hNotAdmits data hAligned
    exact hNotAdmits (data.toTowerAdmitsCenteredAddress hAligned)

/-- Pointwise red-team falsifiers are equivalent to failure of D5 accepted
centered-address admission. -/
theorem g8AcceptedRealizationPointwiseFalsifier_iff_notTowerAdmits
    (model : G8BookIIITowerAcceptedSpectralWitnessModel)
    (z : OrthodoxXiZeroCarrier) :
    Nonempty (G8BookIIIAcceptedRealizationPointwiseFalsifier model z) ↔
      ¬ G8BookIIITowerAdmitsCenteredAddress model z :=
  (g8AcceptedRealizationPointwiseFalsifier_iff_noAlignedWitness
      model z).trans
    (g8NoAcceptedAlignedWitness_iff_notTowerAdmits model z)

-- ============================================================
-- GLOBAL PACKAGE REDUCTION
-- ============================================================

/-- Pointwise accepted centered-address coverage is the exact remaining global
target for the proof package. -/
def G8BookIIIPointwiseAcceptedCenteredAddressCoverage
    (model : G8BookIIITowerAcceptedSpectralWitnessModel) : Prop :=
  ∀ z : OrthodoxXiZeroCarrier,
    G8BookIIITowerAdmitsCenteredAddress model z

/-- Pointwise accepted centered-address coverage supplies the proof package by
selecting the accepted witness from each existential target. -/
def G8BookIIICharacterAcceptedRealizationProofPackage.ofPointwiseTowerCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (coverage : G8BookIIIPointwiseAcceptedCenteredAddressCoverage model) :
    G8BookIIICharacterAcceptedRealizationProofPackage model where
  realizationData := fun z =>
    G8BookIIIAcceptedTowerRealizationData.ofTowerAdmits
      (coverage z)
  normalFormAligned := fun z =>
    G8BookIIIAcceptedTowerRealizationData.ofTowerAdmits_aligned
      (coverage z)

/-- A proof package supplies pointwise accepted centered-address coverage. -/
theorem G8BookIIICharacterAcceptedRealizationProofPackage.pointwiseTowerCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (pkg : G8BookIIICharacterAcceptedRealizationProofPackage model) :
    G8BookIIIPointwiseAcceptedCenteredAddressCoverage model := by
  intro z
  exact
    (pkg.realizationData z).toTowerAdmitsCenteredAddress
      (pkg.normalFormAligned z)

/-- The proof package is equivalent to pointwise accepted centered-address
coverage. -/
theorem g8ProofPackage_iff_pointwiseTowerCoverage
    (model : G8BookIIITowerAcceptedSpectralWitnessModel) :
    Nonempty (G8BookIIICharacterAcceptedRealizationProofPackage model) ↔
      G8BookIIIPointwiseAcceptedCenteredAddressCoverage model := by
  constructor
  · intro hPkg
    rcases hPkg with ⟨pkg⟩
    exact pkg.pointwiseTowerCoverage
  · intro coverage
    exact
      ⟨G8BookIIICharacterAcceptedRealizationProofPackage.ofPointwiseTowerCoverage
        coverage⟩

/-- A proof package rejects carrier-level off-criticality pointwise through D5. -/
theorem G8BookIIICharacterAcceptedRealizationProofPackage.notCarrierOffCritical
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (pkg : G8BookIIICharacterAcceptedRealizationProofPackage model)
    (z : OrthodoxXiZeroCarrier) :
    ¬ OrthodoxXiCarrierOffCritical z :=
  g8BookIIITowerAdmitsCenteredAddress_notCarrierOffCritical
    model z (pkg.pointwiseTowerCoverage z)

-- ============================================================
-- NON-CIRCULARITY GUARDRAILS
-- ============================================================

/-- Finite address normalization plus canonical no-rogue character readout.

This record deliberately contains only the theorem-backed address/readout
evidence.  It has no accepted tower witness field; the remaining target is
still the D5 accepted centered-address admission proposition. -/
structure G8FiniteAddressNoRogueReadoutOnly
    (z : OrthodoxXiZeroCarrier) where
  address : G8BoundaryPointAddress
  address_eq :
    address = orthodoxXiCarrierCenteredBoundaryPointAddress z
  readout : G8BookIIIBoundaryCharacterReadout z
  readout_canonical :
    readout = orthodoxXiCarrierBoundaryCharacterReadout z
  noRogueFactor :
    G8BookIIITauBipolarFactorization readout.character

/-- Canonical finite address and no-rogue readout for a carrier. -/
def G8FiniteAddressNoRogueReadoutOnly.canonical
    (z : OrthodoxXiZeroCarrier) :
    G8FiniteAddressNoRogueReadoutOnly z where
  address := orthodoxXiCarrierCenteredBoundaryPointAddress z
  address_eq := rfl
  readout := orthodoxXiCarrierBoundaryCharacterReadout z
  readout_canonical := rfl
  noRogueFactor := bookIII_orthodoxXiBoundaryCharacter_factors z

/-- Even in the presence of the finite address/no-rogue readout evidence, the
remaining accepted-realization target is exactly D5 accepted centered-address
admission. -/
theorem G8FiniteAddressNoRogueReadoutOnly.remainingTarget_iff_towerAdmits
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (_guard : G8FiniteAddressNoRogueReadoutOnly z) :
    G8BookIIIAcceptedTowerAlignedRealizationExists model z ↔
      G8BookIIITowerAdmitsCenteredAddress model z :=
  g8AcceptedAlignedRealizationExists_iff_towerAdmits model z

/-- Exact normal-form alignment is stronger than axis-offset agreement.  The
axis-offset equality is only a consequence, not the accepted-realization
alignment target. -/
theorem G8BookIIIAcceptedTowerRealizationAligned.axisOffset_eq
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    {data : G8BookIIIAcceptedTowerRealizationData model z}
    (hAligned : G8BookIIIAcceptedTowerRealizationAligned data) :
    primePolarityAxisOffset (model.normalForm data.witness) =
      primePolarityAxisOffset
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf := by
  rw [hAligned]

/-- An accepted aligned tower witness refutes any thin off-axis classification
for the same carrier through the existing D5 conflict. -/
theorem G8BookIIIAcceptedTowerRealizationData.refutesThinOffAxis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (data : G8BookIIIAcceptedTowerRealizationData model z)
    (hAligned : G8BookIIIAcceptedTowerRealizationAligned data)
    (source : G8ActualXiZetaThinSourceContext)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    False :=
  g8BookIIITowerAdmitsCenteredAddress_refutesThinOffAxis
    model source z (data.toTowerAdmitsCenteredAddress hAligned) hOffAxis

/-- An accepted aligned tower witness rejects carrier-level off-criticality. -/
theorem G8BookIIIAcceptedTowerRealizationData.notCarrierOffCritical
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {z : OrthodoxXiZeroCarrier}
    (data : G8BookIIIAcceptedTowerRealizationData model z)
    (hAligned : G8BookIIIAcceptedTowerRealizationAligned data) :
    ¬ OrthodoxXiCarrierOffCritical z :=
  g8BookIIITowerAdmitsCenteredAddress_notCarrierOffCritical
    model z (data.toTowerAdmitsCenteredAddress hAligned)

end Tau.BookIII.Bridge
