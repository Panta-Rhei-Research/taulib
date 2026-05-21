import TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightSpectralCore
import TauLib.BookIII.Bridge.G8ActualXiZeroHeightAxisGuard
import TauLib.BookIII.Bridge.G8EtaModTwoPairedPositiveHalfPlaneClosure

/-!
# TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightSpectralReality

Nonzero-height Lane-A spectral-reality corridor.

The zero-height branch is now theorem-backed by the eta/open-unit discharge.
This module therefore sharpens the remaining Lane-A payload:

```text
zero-height carrier    -> zero-height axis guard
nonzero-height carrier -> real centered quadratic parameter
```

Only the nonzero-height branch still needs the spectral-reality theorem.  This
is weaker than the older global `spectralParameterReal` field, which asked for
the centered quadratic parameter to be real even on carriers already handled by
the zero-height guard.

No theorem here proves the spectral-reality payload from RH, accepted coverage,
the final live hinge, O3, full divisor transfer, or analytic-completion
uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

/-- Height-split Lane-A inputs with the theorem-backed zero-height branch and
    the weaker nonzero-height-only spectral-reality payload. -/
structure G8ActualXiNonzeroHeightSpectralRealityInputs where
  nonzeroSpectralParameterReal :
    G8ActualXiNonzeroHeightSpectralParameterReal
  zeroHeightAxis : G8ActualXiZeroHeightAxisGuard
  status : G8OffCriticalExclusionStatus := .openObligation

-- ============================================================
-- HEIGHT-SPLIT CONSEQUENCES
-- ============================================================

/-- The sharpened input package forces nonzero-height carriers onto the
    critical axis. -/
theorem G8ActualXiNonzeroHeightSpectralRealityInputs.nonzeroCarrierRe_eq_half
    (inputs : G8ActualXiNonzeroHeightSpectralRealityInputs)
    (z : G8ActualXiNonzeroHeightCarrier) :
    z.1.toZero.point.re = (1 / 2 : ℝ) :=
  g8NonzeroHeightSpectralParameterReal_forces_re_eq_half
    inputs.nonzeroSpectralParameterReal z

/-- The sharpened input package excludes off-criticality on nonzero-height
    carriers. -/
theorem G8ActualXiNonzeroHeightSpectralRealityInputs.noNonzeroCarrierOffCritical
    (inputs : G8ActualXiNonzeroHeightSpectralRealityInputs)
    (z : G8ActualXiNonzeroHeightCarrier) :
    ¬ OrthodoxXiCarrierOffCritical z.1 :=
  g8NonzeroHeightSpectralParameterReal_noOffCritical
    inputs.nonzeroSpectralParameterReal z

/-- The sharpened input package excludes all carrier-level off-criticality:
zero-height carriers are handled by the zero-height guard, and nonzero-height
carriers by spectral-parameter reality. -/
theorem G8ActualXiNonzeroHeightSpectralRealityInputs.noCarrierOffCritical
    (inputs : G8ActualXiNonzeroHeightSpectralRealityInputs)
    (z : OrthodoxXiZeroCarrier) :
    ¬ OrthodoxXiCarrierOffCritical z := by
  by_cases hZero : z.toZero.point.im = 0
  · exact inputs.zeroHeightAxis z hZero
  · exact inputs.noNonzeroCarrierOffCritical ⟨z, hZero⟩

/-- The sharpened input package supplies actual centered-address balance. -/
theorem G8ActualXiNonzeroHeightSpectralRealityInputs.centeredAddressBalanced
    (inputs : G8ActualXiNonzeroHeightSpectralRealityInputs) :
    G8ActualXiCenteredAddressBalanced :=
  g8ActualXiCenteredAddressBalanced_of_noCarrierOffCritical
    inputs.noCarrierOffCritical

/-- The sharpened input package supplies actual sigma-fixedness. -/
theorem G8ActualXiNonzeroHeightSpectralRealityInputs.actualSigmaFixed
    (inputs : G8ActualXiNonzeroHeightSpectralRealityInputs) :
    G8ActualXiBoundaryCharacterSigmaFixed :=
  G8ActualXiBoundaryCharacterSigmaFixed.of_centeredAddressBalanced
    inputs.centeredAddressBalanced

/-- The sharpened input package supplies global crossing-mediated readout
    evidence. -/
theorem G8ActualXiNonzeroHeightSpectralRealityInputs.toCrossingMediatedAll
    (inputs : G8ActualXiNonzeroHeightSpectralRealityInputs) :
    G8ActualXiBoundaryReadoutCrossingMediatedAll :=
  G8ActualXiBoundaryReadoutCrossingMediatedAll.of_centeredAddressBalanced
    inputs.centeredAddressBalanced

/-- The sharpened input package plus sigma-fixed accepted realization builds
    the existing final live hinge. -/
def G8ActualXiNonzeroHeightSpectralRealityInputs.toFinalLiveHinge
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (inputs : G8ActualXiNonzeroHeightSpectralRealityInputs)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8FinalLiveHinge model :=
  G8FinalLiveHinge.ofCrossingMediatedAll
    inputs.toCrossingMediatedAll realization

/-- The sharpened input package plus accepted realization supplies pointwise
    accepted centered-address coverage. -/
theorem G8ActualXiNonzeroHeightSpectralRealityInputs.pointwiseCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (inputs : G8ActualXiNonzeroHeightSpectralRealityInputs)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8BookIIIPointwiseAcceptedCenteredAddressCoverage model :=
  (inputs.toFinalLiveHinge realization).pointwiseCoverage

/-- The sharpened input package plus accepted realization forwards to the
    existing conditional Mathlib handoff. -/
theorem G8ActualXiNonzeroHeightSpectralRealityInputs.mathlibRiemannHypothesis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (inputs : G8ActualXiNonzeroHeightSpectralRealityInputs)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    RiemannHypothesis :=
  (inputs.toFinalLiveHinge realization).mathlibRiemannHypothesis

-- ============================================================
-- ADAPTERS FROM EXISTING SURFACES
-- ============================================================

/-- The older global height-split package implies the new nonzero-height-only
    package.  This direction is intentionally one-way: the new package is
    weaker and should not be inflated back to global spectral reality. -/
def G8ActualXiHeightSplitSpectralRealityInputs.toNonzeroHeightInputs
    (inputs : G8ActualXiHeightSplitSpectralRealityInputs) :
    G8ActualXiNonzeroHeightSpectralRealityInputs where
  nonzeroSpectralParameterReal := fun z => inputs.spectralParameterReal z.1
  zeroHeightAxis := inputs.zeroHeightAxis

/-- A zero-height discharge package plus the nonzero-height spectral payload
    supplies the sharpened Lane-A input package. -/
def G8ActualXiZeroHeightAxisGuardDischarge.toNonzeroHeightInputs
    (discharge : G8ActualXiZeroHeightAxisGuardDischarge)
    (hReal : G8ActualXiNonzeroHeightSpectralParameterReal) :
    G8ActualXiNonzeroHeightSpectralRealityInputs where
  nonzeroSpectralParameterReal := hReal
  zeroHeightAxis := discharge.zeroHeightAxisGuard

/-- The theorem-backed paired eta closure supplies the zero-height branch, so
    the only remaining Lane-A input here is nonzero-height spectral reality. -/
def G8ActualXiNonzeroHeightSpectralRealityInputs.ofPairedEtaClosure
    (hReal : G8ActualXiNonzeroHeightSpectralParameterReal) :
    G8ActualXiNonzeroHeightSpectralRealityInputs :=
  G8ActualXiZeroHeightAxisGuardDischarge.toNonzeroHeightInputs
    g8ActualXiZeroHeightAxisGuardDischarge_from_pairedPositiveHalfPlane hReal

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A nonzero-height off-critical carrier refutes the sharpened spectral
    payload. -/
structure G8ActualXiNonzeroHeightOffCriticalFalsifier where
  z : G8ActualXiNonzeroHeightCarrier
  offCritical : OrthodoxXiCarrierOffCritical z.1

/-- Nonzero-height off-critical evidence refutes the nonzero-height spectral
    payload. -/
theorem G8ActualXiNonzeroHeightOffCriticalFalsifier.refutesSpectralParameterReal
    (w : G8ActualXiNonzeroHeightOffCriticalFalsifier)
    (hReal : G8ActualXiNonzeroHeightSpectralParameterReal) :
    False :=
  g8NonzeroHeightSpectralParameterReal_noOffCritical hReal w.z w.offCritical

/-- Nonzero-height off-critical evidence refutes the sharpened input package. -/
theorem G8ActualXiNonzeroHeightOffCriticalFalsifier.refutesInputs
    (w : G8ActualXiNonzeroHeightOffCriticalFalsifier)
    (inputs : G8ActualXiNonzeroHeightSpectralRealityInputs) :
    False :=
  w.refutesSpectralParameterReal inputs.nonzeroSpectralParameterReal

/-- A nonzero-height carrier with non-real centered quadratic parameter refutes
    the sharpened input package. -/
theorem
    G8ActualXiNonzeroHeightCenteredQuadraticNonrealFalsifier.refutesNonzeroHeightInputs
    (w : G8ActualXiNonzeroHeightCenteredQuadraticNonrealFalsifier)
    (inputs : G8ActualXiNonzeroHeightSpectralRealityInputs) :
    False :=
  w.nonreal (inputs.nonzeroSpectralParameterReal w.z)

/-- Zero-height off-critical evidence still refutes the sharpened input package
    through its zero-height guard field. -/
theorem G8ActualXiZeroHeightOffCriticalFalsifier.refutesNonzeroHeightInputs
    (w : G8ActualXiZeroHeightOffCriticalFalsifier)
    (inputs : G8ActualXiNonzeroHeightSpectralRealityInputs) :
    False :=
  w.refutesZeroHeightAxis inputs.zeroHeightAxis

end Tau.BookIII.Bridge
