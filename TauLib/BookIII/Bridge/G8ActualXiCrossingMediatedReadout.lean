import TauLib.BookIII.Bridge.G8ActualXiSigmaFixedReduction

/-!
# TauLib.BookIII.Bridge.G8ActualXiCrossingMediatedReadout

Crossing-mediated readout corridor for the actual-`xi` sigma-fixed hinge.

The iota-tau and boundary-algebra papers suggest the correct proof shape:
actual `xi` readouts should be shown to land in the sigma-fixed scalar fibre,
or equivalently in the crossing-mediated B/C-balanced channel.  This module
does not prove that landing theorem.  It packages it as explicit pointwise
evidence and forwards it through the existing final live hinge.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- CROSSING-MEDIATED ACTUAL XI READOUTS
-- ============================================================

/-- Pointwise evidence that an actual `xi` boundary readout lands in the
    crossing-mediated sigma-fixed scalar fibre.

In the current bridge model, the localization-bearing content of this evidence
is exactly B/C balance of the normalized centered boundary address. -/
structure G8ActualXiBoundaryReadoutCrossingMediated
    (z : OrthodoxXiZeroCarrier) : Prop where
  centeredAddress_bcBalanced :
    BCBalanced
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf

/-- Global crossing-mediated readout evidence for all actual `xi` carriers. -/
def G8ActualXiBoundaryReadoutCrossingMediatedAll : Prop :=
  ∀ z : OrthodoxXiZeroCarrier,
    G8ActualXiBoundaryReadoutCrossingMediated z

/-- Crossing-mediated evidence keeps the theorem-backed two-channel/no-rogue
    factorization visible. -/
theorem G8ActualXiBoundaryReadoutCrossingMediated.noRogue
    {z : OrthodoxXiZeroCarrier}
    (_h : G8ActualXiBoundaryReadoutCrossingMediated z) :
    G8BookIIITauBipolarFactorization
      (orthodoxXiCarrierBoundaryCharacter z) :=
  g8XiBoundaryCharacter_noRogue z

/-- Crossing-mediated evidence supplies the pointwise actual `xi`
    sigma-fixed character statement. -/
theorem G8ActualXiBoundaryReadoutCrossingMediated.sigmaFixed
    {z : OrthodoxXiZeroCarrier}
    (h : G8ActualXiBoundaryReadoutCrossingMediated z) :
    G8XiBoundaryCharacterSigmaFixed z :=
  G8XiBoundaryCharacterSigmaFixed.of_centeredAddress_bcBalanced
    h.centeredAddress_bcBalanced

/-- Global crossing-mediated evidence supplies the final actual sigma-fixed
    target. -/
theorem G8ActualXiBoundaryReadoutCrossingMediatedAll.actualSigmaFixed
    (hCrossing : G8ActualXiBoundaryReadoutCrossingMediatedAll) :
    G8ActualXiBoundaryCharacterSigmaFixed := by
  intro z
  exact (hCrossing z).sigmaFixed

/-- Global crossing-mediated evidence is the same as the existing centered
    address balance reduction target, with the evidence wrapper retained for
    proof-source clarity. -/
theorem g8ActualXiBoundaryReadoutCrossingMediatedAll_iff_centeredAddressBalanced :
    G8ActualXiBoundaryReadoutCrossingMediatedAll ↔
      G8ActualXiCenteredAddressBalanced := by
  constructor
  · intro hCrossing z
    exact (hCrossing z).centeredAddress_bcBalanced
  · intro hBalanced z
    exact
      { centeredAddress_bcBalanced := hBalanced z }

/-- Actual centered-address balance packages as global crossing-mediated
    readout evidence. -/
theorem G8ActualXiBoundaryReadoutCrossingMediatedAll.of_centeredAddressBalanced
    (hBalanced : G8ActualXiCenteredAddressBalanced) :
    G8ActualXiBoundaryReadoutCrossingMediatedAll :=
  g8ActualXiBoundaryReadoutCrossingMediatedAll_iff_centeredAddressBalanced.mpr
    hBalanced

/-- Global crossing-mediated evidence supplies actual centered-address balance. -/
theorem G8ActualXiBoundaryReadoutCrossingMediatedAll.centeredAddressBalanced
    (hCrossing : G8ActualXiBoundaryReadoutCrossingMediatedAll) :
    G8ActualXiCenteredAddressBalanced :=
  g8ActualXiBoundaryReadoutCrossingMediatedAll_iff_centeredAddressBalanced.mp
    hCrossing

-- ============================================================
-- FINAL LIVE-HINGE ADAPTERS
-- ============================================================

/-- Crossing-mediated readouts plus the sigma-fixed accepted-realization law
    build the existing final live-hinge package. -/
def G8FinalLiveHinge.ofCrossingMediatedAll
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (hCrossing : G8ActualXiBoundaryReadoutCrossingMediatedAll)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8FinalLiveHinge model where
  actualSigmaFixed := hCrossing.actualSigmaFixed
  sigmaFixedRealization := realization

/-- Crossing-mediated readouts plus accepted realization supply the existing
    pointwise accepted centered-address coverage target. -/
theorem G8ActualXiBoundaryReadoutCrossingMediatedAll.pointwiseCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (hCrossing : G8ActualXiBoundaryReadoutCrossingMediatedAll)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8BookIIIPointwiseAcceptedCenteredAddressCoverage model :=
  (G8FinalLiveHinge.ofCrossingMediatedAll hCrossing realization).pointwiseCoverage

/-- Crossing-mediated readouts plus accepted realization forward to the
    existing conditional Mathlib handoff. -/
theorem G8ActualXiBoundaryReadoutCrossingMediatedAll.mathlibRiemannHypothesis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (hCrossing : G8ActualXiBoundaryReadoutCrossingMediatedAll)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    RiemannHypothesis :=
  (G8FinalLiveHinge.ofCrossingMediatedAll hCrossing realization).mathlibRiemannHypothesis

-- ============================================================
-- FALSIFIERS AND GUARDRAILS
-- ============================================================

/-- Pointwise evidence that an actual `xi` carrier has not been shown to land
    in the crossing-mediated scalar fibre. -/
structure G8ActualXiNotCrossingMediatedWitness where
  z : OrthodoxXiZeroCarrier
  notCrossingMediated :
    ¬ G8ActualXiBoundaryReadoutCrossingMediated z

/-- A not-crossing-mediated witness refutes global crossing-mediated evidence. -/
theorem G8ActualXiNotCrossingMediatedWitness.refutesAll
    (w : G8ActualXiNotCrossingMediatedWitness) :
    ¬ G8ActualXiBoundaryReadoutCrossingMediatedAll := by
  intro hCrossing
  exact w.notCrossingMediated (hCrossing w.z)

/-- A claimed crossing-mediated readout with an imbalanced centered address is
    a direct contradiction. -/
structure G8ActualXiCrossingMediatedButImbalancedWitness where
  z : OrthodoxXiZeroCarrier
  crossingMediated : G8ActualXiBoundaryReadoutCrossingMediated z
  imbalance :
    TauBCImbalance
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf

/-- Crossing-mediated-plus-imbalanced evidence refutes itself. -/
theorem G8ActualXiCrossingMediatedButImbalancedWitness.refutes
    (w : G8ActualXiCrossingMediatedButImbalancedWitness) :
    False :=
  w.imbalance w.crossingMediated.centeredAddress_bcBalanced

/-- A two-channel/no-rogue but non-sigma-fixed witness refutes pointwise
    crossing-mediated evidence.  This records that no-rogue evidence alone is
    weaker than crossing-mediated sigma-fixedness. -/
theorem G8TwoChannelButNotSigmaFixedWitness.refutesCrossingMediated
    (w : G8TwoChannelButNotSigmaFixedWitness) :
    ¬ G8ActualXiBoundaryReadoutCrossingMediated w.z := by
  intro hCrossing
  exact w.notSigmaFixed hCrossing.sigmaFixed

/-- A two-channel/no-rogue but non-sigma-fixed witness refutes global
    crossing-mediated evidence. -/
theorem G8TwoChannelButNotSigmaFixedWitness.refutesCrossingMediatedAll
    (w : G8TwoChannelButNotSigmaFixedWitness) :
    ¬ G8ActualXiBoundaryReadoutCrossingMediatedAll := by
  intro hCrossing
  exact w.refutesCrossingMediated (hCrossing w.z)

/-- The existing imbalanced-centered-address falsifier refutes pointwise
    crossing-mediated evidence. -/
theorem G8ActualXiCenteredAddressImbalanceFalsifier.refutesCrossingMediated
    (w : G8ActualXiCenteredAddressImbalanceFalsifier) :
    ¬ G8ActualXiBoundaryReadoutCrossingMediated w.z := by
  intro hCrossing
  exact w.imbalance hCrossing.centeredAddress_bcBalanced

end Tau.BookIII.Bridge
