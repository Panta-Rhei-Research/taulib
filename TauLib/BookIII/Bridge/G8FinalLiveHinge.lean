import TauLib.BookIII.Bridge.G8BookIIISigmaFixedCharacterAddressability

/-!
# TauLib.BookIII.Bridge.G8FinalLiveHinge

Final live-hinge package for the G8 accepted-realization route.

The current final spine has reduced the remaining mathematical work to two
load-bearing inputs:

* actual canonical `xi` boundary characters are sigma-fixed;
* sigma-fixed canonical characters are realized by accepted Book III tower
  witnesses with exact centered-address normal form.

This module packages exactly those inputs and forwards them through the
already theorem-backed chain:

```text
actual sigma-fixedness
  + sigma-fixed accepted tower realization
  -> pointwise accepted centered-address coverage
  -> accepted-realization proof package
  -> Mathlib RiemannHypothesis
```

It does not prove either live input and does not introduce any new primitive
assumption, placeholder proof, O3 proof, full divisor-transfer proof, or
unconditional RH claim.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- FINAL LIVE HINGE
-- ============================================================

/-- The final live hinge for a fixed Book III accepted tower model.

This is the compact handoff object for the remaining proof work.  It carries
only the two live obligations and leaves all previously discharged plumbing to
the existing adapters. -/
structure G8FinalLiveHinge
    (model : G8BookIIITowerAcceptedSpectralWitnessModel) where
  actualSigmaFixed : G8ActualXiBoundaryCharacterSigmaFixed
  sigmaFixedRealization :
    G8BookIIIAcceptedTowerRealizationFromSigmaFixed model
  status : G8OffCriticalExclusionStatus := .openObligation

/-- A closed final live-hinge package carries the accepted tower model together
    with the final live hinge for that model. -/
structure G8ClosedFinalLiveHinge where
  model : G8BookIIITowerAcceptedSpectralWitnessModel
  hinge : G8FinalLiveHinge model

-- ============================================================
-- FORWARD SELECTORS
-- ============================================================

/-- The final live hinge supplies pointwise accepted centered-address coverage. -/
theorem G8FinalLiveHinge.pointwiseCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (hinge : G8FinalLiveHinge model) :
    G8BookIIIPointwiseAcceptedCenteredAddressCoverage model :=
  hinge.sigmaFixedRealization.pointwiseCoverage
    hinge.actualSigmaFixed

/-- The final live hinge supplies the accepted-realization proof package. -/
def G8FinalLiveHinge.toProofPackage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (hinge : G8FinalLiveHinge model) :
    G8BookIIICharacterAcceptedRealizationProofPackage model :=
  hinge.sigmaFixedRealization.toProofPackage
    hinge.actualSigmaFixed

/-- The final live hinge supplies the older accepted-realization interface. -/
def G8FinalLiveHinge.toAcceptedRealization
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (hinge : G8FinalLiveHinge model) :
    G8BookIIICharacterAcceptedRealization model :=
  hinge.sigmaFixedRealization.toAcceptedRealization
    hinge.actualSigmaFixed

/-- The final live hinge supplies accepted `xi` coverage. -/
theorem G8FinalLiveHinge.acceptedXiCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (hinge : G8FinalLiveHinge model) :
    G8BookIIIAcceptedXiCoversMathlibNontrivialZetaZeros model :=
  hinge.toProofPackage.acceptedXiCoverage

/-- The final live hinge rejects carrier-level off-criticality pointwise. -/
theorem G8FinalLiveHinge.notCarrierOffCritical
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (hinge : G8FinalLiveHinge model)
    (z : OrthodoxXiZeroCarrier) :
    ¬ OrthodoxXiCarrierOffCritical z :=
  hinge.sigmaFixedRealization.notCarrierOffCritical
    hinge.actualSigmaFixed z

/-- The final live hinge supplies Mathlib's formal `RiemannHypothesis` target
    through the existing accepted-realization handoff. -/
theorem G8FinalLiveHinge.mathlibRiemannHypothesis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (hinge : G8FinalLiveHinge model) :
    RiemannHypothesis :=
  hinge.toProofPackage.mathlibRiemannHypothesis

/-- Closed final live-hinge packages supply pointwise accepted centered-address
    coverage for their model. -/
theorem G8ClosedFinalLiveHinge.pointwiseCoverage
    (closed : G8ClosedFinalLiveHinge) :
    G8BookIIIPointwiseAcceptedCenteredAddressCoverage closed.model :=
  closed.hinge.pointwiseCoverage

/-- Closed final live-hinge packages supply the accepted-realization proof
    package for their model. -/
def G8ClosedFinalLiveHinge.toProofPackage
    (closed : G8ClosedFinalLiveHinge) :
    G8BookIIICharacterAcceptedRealizationProofPackage closed.model :=
  closed.hinge.toProofPackage

/-- Closed final live-hinge packages supply Mathlib's formal
    `RiemannHypothesis` target. -/
theorem G8ClosedFinalLiveHinge.mathlibRiemannHypothesis
    (closed : G8ClosedFinalLiveHinge) :
    RiemannHypothesis :=
  closed.hinge.mathlibRiemannHypothesis

-- ============================================================
-- REFUTATION SURFACES
-- ============================================================

/-- Failure of actual sigma-fixedness refutes the final live hinge. -/
theorem G8TwoChannelButNotSigmaFixedWitness.refutesFinalLiveHinge
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (w : G8TwoChannelButNotSigmaFixedWitness)
    (hinge : G8FinalLiveHinge model) :
    False :=
  w.refutesActualSigmaFixed hinge.actualSigmaFixed

/-- A sigma-fixed carrier without accepted centered-address admission refutes
    the final live hinge for that model. -/
theorem G8SigmaFixedWithoutAcceptedTowerWitness.refutesFinalLiveHinge
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (w : G8SigmaFixedWithoutAcceptedTowerWitness model)
    (hinge : G8FinalLiveHinge model) :
    False :=
  w.refutesRealization hinge.sigmaFixedRealization

/-- An accepted realization with wrong exact normal form refutes the final live
    hinge through the selected sigma-fixed realization law. -/
theorem G8SigmaFixedRealizationNormalFormMismatch.refutesFinalLiveHinge
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    {realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model}
    (w : G8SigmaFixedRealizationNormalFormMismatch realization)
    (hinge : G8FinalLiveHinge model)
    (hSame :
      hinge.sigmaFixedRealization = realization) :
    False := by
  subst hSame
  exact w.refutes

end Tau.BookIII.Bridge
