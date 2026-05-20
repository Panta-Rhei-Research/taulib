import TauLib.BookIII.Bridge.G8ActualXiCrossingMediatedReadout
import TauLib.BookIII.Bridge.G8ActualXiSigmaFixedFromSpectralReality

/-!
# TauLib.BookIII.Bridge.G8ActualXiCrossingMediatedLanding

Proof-carrying landing surface for the final actual-`xi` crossing-mediated
hinge.

The source papers suggest the following route:

```text
actual xi boundary germ/readout
  + sigma-fixed scalar-fibre evidence
  + non-polar two-lobe crossing evidence
  + omega/tail-stable crossing-mediator evidence
  -> centered-address B/C balance
```

This module does not prove that every actual `xi` readout lands in that fibre.
It packages that theorem as explicit pointwise evidence, connects the existing
spectral-reality lane to crossing-mediated evidence, and forwards both through
the already theorem-backed final live hinge.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- POINTWISE LANDING EVIDENCE
-- ============================================================

/-- Pointwise source-paper landing evidence for an actual `xi` carrier.

The first four proposition fields name the intended source of the evidence:
actual boundary readout, sigma-fixed scalar fibre, non-polar two-lobe crossing,
and omega/tail-stable crossing-mediator behavior.  The final field is the
localization-bearing conclusion consumed by the Lean spine. -/
structure G8ActualXiCrossingMediatedLandingEvidence
    (z : OrthodoxXiZeroCarrier) where
  actualXiBoundaryGermReadout : Prop
  sigmaFixedScalarFiber : Prop
  nonPolarTwoLobeCrossing : Prop
  omegaTailStableCrossingMediator : Prop
  readoutEvidence : actualXiBoundaryGermReadout
  sigmaFixedEvidence : sigmaFixedScalarFiber
  crossingEvidence : nonPolarTwoLobeCrossing
  mediatorEvidence : omegaTailStableCrossingMediator
  centeredAddress_bcBalanced :
    BCBalanced
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf
  status : G8OffCriticalExclusionStatus := .openObligation

/-- Global crossing-mediated landing context: every actual `xi` carrier has
    pointwise source-paper landing evidence. -/
structure G8ActualXiCrossingMediatedLandingContext where
  evidenceOf :
    ∀ z : OrthodoxXiZeroCarrier,
      G8ActualXiCrossingMediatedLandingEvidence z
  status : G8OffCriticalExclusionStatus := .openObligation

/-- Pointwise landing evidence supplies the existing crossing-mediated
    readout evidence. -/
def G8ActualXiCrossingMediatedLandingEvidence.toCrossingMediated
    {z : OrthodoxXiZeroCarrier}
    (e : G8ActualXiCrossingMediatedLandingEvidence z) :
    G8ActualXiBoundaryReadoutCrossingMediated z where
  centeredAddress_bcBalanced := e.centeredAddress_bcBalanced

/-- Pointwise landing evidence supplies the canonical no-rogue/two-channel
    factorization already available for actual `xi` carriers. -/
theorem G8ActualXiCrossingMediatedLandingEvidence.noRogue
    {z : OrthodoxXiZeroCarrier}
    (e : G8ActualXiCrossingMediatedLandingEvidence z) :
    G8BookIIITauBipolarFactorization
      (orthodoxXiCarrierBoundaryCharacter z) :=
  e.toCrossingMediated.noRogue

/-- Pointwise landing evidence supplies pointwise sigma-fixedness. -/
theorem G8ActualXiCrossingMediatedLandingEvidence.sigmaFixed
    {z : OrthodoxXiZeroCarrier}
    (e : G8ActualXiCrossingMediatedLandingEvidence z) :
    G8XiBoundaryCharacterSigmaFixed z :=
  e.toCrossingMediated.sigmaFixed

/-- A global landing context supplies global crossing-mediated readout
    evidence. -/
theorem G8ActualXiCrossingMediatedLandingContext.toCrossingMediatedAll
    (ctx : G8ActualXiCrossingMediatedLandingContext) :
    G8ActualXiBoundaryReadoutCrossingMediatedAll := by
  intro z
  exact (ctx.evidenceOf z).toCrossingMediated

/-- A global landing context supplies the actual sigma-fixed target. -/
theorem G8ActualXiCrossingMediatedLandingContext.actualSigmaFixed
    (ctx : G8ActualXiCrossingMediatedLandingContext) :
    G8ActualXiBoundaryCharacterSigmaFixed :=
  ctx.toCrossingMediatedAll.actualSigmaFixed

-- ============================================================
-- SPECTRAL-REALITY ADAPTERS
-- ============================================================

/-- The conditional spectral-reality lane supplies global crossing-mediated
    readout evidence via its theorem-backed centered-address balance theorem. -/
theorem G8ActualXiSpectralRealityContext.toCrossingMediatedAll
    (ctx : G8ActualXiSpectralRealityContext) :
    G8ActualXiBoundaryReadoutCrossingMediatedAll :=
  G8ActualXiBoundaryReadoutCrossingMediatedAll.of_centeredAddressBalanced
    ctx.centeredAddressBalanced

/-- Spectral reality plus the sigma-fixed accepted-realization law builds the
    existing final live hinge. -/
def G8ActualXiSpectralRealityContext.toFinalLiveHinge
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8ActualXiSpectralRealityContext)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8FinalLiveHinge model :=
  G8FinalLiveHinge.ofCrossingMediatedAll
    ctx.toCrossingMediatedAll realization

/-- Spectral reality plus the sigma-fixed accepted-realization law supplies
    the pointwise accepted centered-address coverage target. -/
theorem G8ActualXiSpectralRealityContext.pointwiseCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8ActualXiSpectralRealityContext)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8BookIIIPointwiseAcceptedCenteredAddressCoverage model :=
  (ctx.toFinalLiveHinge realization).pointwiseCoverage

/-- Spectral reality plus the sigma-fixed accepted-realization law forwards
    through the existing conditional Mathlib handoff. -/
theorem G8ActualXiSpectralRealityContext.mathlibRiemannHypothesis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8ActualXiSpectralRealityContext)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    RiemannHypothesis :=
  (ctx.toFinalLiveHinge realization).mathlibRiemannHypothesis

-- ============================================================
-- FINAL LIVE-HINGE ADAPTERS
-- ============================================================

/-- Source-paper landing context plus the sigma-fixed accepted-realization law
    builds the existing final live hinge. -/
def G8ActualXiCrossingMediatedLandingContext.toFinalLiveHinge
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8ActualXiCrossingMediatedLandingContext)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8FinalLiveHinge model :=
  G8FinalLiveHinge.ofCrossingMediatedAll
    ctx.toCrossingMediatedAll realization

/-- Source-paper landing context plus accepted realization supplies pointwise
    accepted centered-address coverage. -/
theorem G8ActualXiCrossingMediatedLandingContext.pointwiseCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8ActualXiCrossingMediatedLandingContext)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8BookIIIPointwiseAcceptedCenteredAddressCoverage model :=
  (ctx.toFinalLiveHinge realization).pointwiseCoverage

/-- Source-paper landing context plus accepted realization forwards to the
    existing conditional Mathlib handoff. -/
theorem G8ActualXiCrossingMediatedLandingContext.mathlibRiemannHypothesis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8ActualXiCrossingMediatedLandingContext)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    RiemannHypothesis :=
  (ctx.toFinalLiveHinge realization).mathlibRiemannHypothesis

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- Two-channel but non-sigma-fixed actual `xi` evidence refutes pointwise
    crossing-mediated landing evidence. -/
theorem G8TwoChannelButNotSigmaFixedWitness.refutesLandingEvidence
    (w : G8TwoChannelButNotSigmaFixedWitness)
    (e : G8ActualXiCrossingMediatedLandingEvidence w.z) :
    False :=
  w.refutesCrossingMediated e.toCrossingMediated

/-- Two-channel but non-sigma-fixed actual `xi` evidence refutes a global
    crossing-mediated landing context. -/
theorem G8TwoChannelButNotSigmaFixedWitness.refutesLandingContext
    (w : G8TwoChannelButNotSigmaFixedWitness)
    (ctx : G8ActualXiCrossingMediatedLandingContext) :
    False :=
  w.refutesLandingEvidence (ctx.evidenceOf w.z)

/-- Landing evidence whose centered address is still imbalanced is a direct
    contradiction. -/
structure G8CrossingMediatedLandingButImbalancedWitness where
  z : OrthodoxXiZeroCarrier
  landingEvidence : G8ActualXiCrossingMediatedLandingEvidence z
  imbalance :
    TauBCImbalance
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf

/-- Landing-plus-imbalance evidence refutes itself. -/
theorem G8CrossingMediatedLandingButImbalancedWitness.refutes
    (w : G8CrossingMediatedLandingButImbalancedWitness) :
    False :=
  w.imbalance w.landingEvidence.centeredAddress_bcBalanced

/-- A sigma-fixed carrier with no accepted centered-address admission refutes
    the final landing assembly for the model. -/
theorem G8SigmaFixedWithoutAcceptedTowerWitness.refutesLandingAssembly
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (w : G8SigmaFixedWithoutAcceptedTowerWitness model)
    (_ctx : G8ActualXiCrossingMediatedLandingContext)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    False :=
  w.refutesRealization realization

/-- Wrong exact normal form in the accepted tower realization refutes the final
    landing assembly. -/
theorem G8SigmaFixedRealizationNormalFormMismatch.refutesLandingAssembly
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model}
    (w : G8SigmaFixedRealizationNormalFormMismatch realization)
    (_ctx : G8ActualXiCrossingMediatedLandingContext) :
    False :=
  w.refutes

/-- A carrier-level off-critical actual `xi` witness refutes pointwise
    crossing-mediated evidence through the theorem-backed binary address
    construction. -/
theorem G8ActualXiOffCriticalCarrierFalsifier.refutesCrossingMediated
    (w : G8ActualXiOffCriticalCarrierFalsifier) :
    ¬ G8ActualXiBoundaryReadoutCrossingMediated w.z := by
  intro hCrossing
  have hOffAxis :
      ShadowOffAxis (orthodoxXiCarrierCenteredShadow w.z) :=
    (orthodoxXiCarrierOffCritical_iff_shadowOffAxis w.z).mp
      w.offCritical
  have hImbalance :
      TauBCImbalance
        (orthodoxXiCarrierCenteredBoundaryPointAddress w.z).normalize.nf :=
    orthodoxXiCarrierCenteredBoundaryPointAddress_bcImbalance
      w.z hOffAxis
  exact hImbalance hCrossing.centeredAddress_bcBalanced

/-- A carrier-level off-critical actual `xi` witness refutes pointwise
    source-paper landing evidence. -/
theorem G8ActualXiOffCriticalCarrierFalsifier.refutesLandingEvidence
    (w : G8ActualXiOffCriticalCarrierFalsifier)
    (e : G8ActualXiCrossingMediatedLandingEvidence w.z) :
    False :=
  w.refutesCrossingMediated e.toCrossingMediated

/-- A carrier-level off-critical actual `xi` witness refutes a global landing
    context. -/
theorem G8ActualXiOffCriticalCarrierFalsifier.refutesLandingContext
    (w : G8ActualXiOffCriticalCarrierFalsifier)
    (ctx : G8ActualXiCrossingMediatedLandingContext) :
    False :=
  w.refutesLandingEvidence (ctx.evidenceOf w.z)

end Tau.BookIII.Bridge
