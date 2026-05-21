import TauLib.BookIII.Bridge.G8ActualXiSpectralRealityInstantiation
import TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightSpectralCore
import TauLib.BookIII.Bridge.G8ActualXiZeroHeightAxisGuardCore

/-!
# TauLib.BookIII.Bridge.G8ActualXiHeightSplitSpectralReality

Height-split Lane-A spectral-reality corridor.

The first spectral-reality package used the stronger global input that every
actual orthodox `xi` carrier has nonzero imaginary height.  This module weakens
that shape:

```text
zero-height carrier      -> explicit zero-height axis guard
nonzero-height carrier   -> real centered quadratic + algebra forces axis
```

The centered-quadratic algebra remains theorem-backed by
`orthodoxXiCarrierCenteredQuadratic_im`.  The two live inputs here are still
explicit: spectral-parameter reality and the zero-height axis guard.  Neither
is proved from O3, divisor transfer, accepted coverage, the final live hinge,
or any RH handoff.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- HEIGHT-SPLIT INPUTS
-- ============================================================

/-- Height-split Lane-A inputs.

The real spectral payload is `spectralParameterReal`.  The zero-height branch
is separated as `zeroHeightAxis`, so nonzero height is no longer required for
every carrier globally. -/
structure G8ActualXiHeightSplitSpectralRealityInputs where
  spectralParameterReal :
    ∀ z : OrthodoxXiZeroCarrier,
      (orthodoxXiCarrierCenteredQuadratic z).im = 0
  zeroHeightAxis : G8ActualXiZeroHeightAxisGuard

-- ============================================================
-- NONZERO-HEIGHT BRANCH
-- ============================================================

/-- On the nonzero-height subtype, spectral-parameter reality and the
    theorem-backed centered-quadratic readout force the critical axis. -/
theorem G8ActualXiHeightSplitSpectralRealityInputs.nonzeroCarrierRe_eq_half
    (inputs : G8ActualXiHeightSplitSpectralRealityInputs)
    (z : G8ActualXiNonzeroHeightCarrier) :
    z.1.toZero.point.re = (1 / 2 : ℝ) := by
  apply
    g8CenteredQuadraticReality_forces_re_eq_half
      (sigma := z.1.toZero.point.re)
      (gamma := z.1.toZero.point.im)
  · change orthodoxXiCarrierCenteredQuadraticImagReadout z.1 = 0
    rw [← orthodoxXiCarrierCenteredQuadratic_im z.1]
    exact inputs.spectralParameterReal z.1
  · exact z.2

/-- Nonzero-height carriers cannot be off-critical once the centered spectral
    parameter is real. -/
theorem G8ActualXiHeightSplitSpectralRealityInputs.noNonzeroCarrierOffCritical
    (inputs : G8ActualXiHeightSplitSpectralRealityInputs)
    (z : G8ActualXiNonzeroHeightCarrier) :
    ¬ OrthodoxXiCarrierOffCritical z.1 := by
  intro hOff
  exact hOff (inputs.nonzeroCarrierRe_eq_half z)

-- ============================================================
-- GLOBAL HEIGHT SPLIT
-- ============================================================

/-- Height-split spectral reality excludes carrier-level off-criticality:
zero-height carriers are handled by the explicit guard, while nonzero-height
carriers are forced onto the axis by spectral-parameter reality. -/
theorem G8ActualXiHeightSplitSpectralRealityInputs.noCarrierOffCritical
    (inputs : G8ActualXiHeightSplitSpectralRealityInputs)
    (z : OrthodoxXiZeroCarrier) :
    ¬ OrthodoxXiCarrierOffCritical z := by
  by_cases hZero : z.toZero.point.im = 0
  · exact inputs.zeroHeightAxis z hZero
  · exact inputs.noNonzeroCarrierOffCritical ⟨z, hZero⟩

/-- Height-split spectral reality supplies actual centered-address balance via
    the existing off-critical-exclusion reduction. -/
theorem G8ActualXiHeightSplitSpectralRealityInputs.centeredAddressBalanced
    (inputs : G8ActualXiHeightSplitSpectralRealityInputs) :
    G8ActualXiCenteredAddressBalanced :=
  g8ActualXiCenteredAddressBalanced_of_noCarrierOffCritical
    inputs.noCarrierOffCritical

/-- Height-split spectral reality supplies the actual sigma-fixed target. -/
theorem G8ActualXiHeightSplitSpectralRealityInputs.actualSigmaFixed
    (inputs : G8ActualXiHeightSplitSpectralRealityInputs) :
    G8ActualXiBoundaryCharacterSigmaFixed :=
  G8ActualXiBoundaryCharacterSigmaFixed.of_centeredAddressBalanced
    inputs.centeredAddressBalanced

/-- Height-split spectral reality supplies global crossing-mediated readout
    evidence. -/
theorem G8ActualXiHeightSplitSpectralRealityInputs.toCrossingMediatedAll
    (inputs : G8ActualXiHeightSplitSpectralRealityInputs) :
    G8ActualXiBoundaryReadoutCrossingMediatedAll :=
  G8ActualXiBoundaryReadoutCrossingMediatedAll.of_centeredAddressBalanced
    inputs.centeredAddressBalanced

/-- Height-split spectral reality plus sigma-fixed accepted realization builds
    the existing final live hinge. -/
def G8ActualXiHeightSplitSpectralRealityInputs.toFinalLiveHinge
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (inputs : G8ActualXiHeightSplitSpectralRealityInputs)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8FinalLiveHinge model :=
  G8FinalLiveHinge.ofCrossingMediatedAll
    inputs.toCrossingMediatedAll realization

/-- Height-split spectral reality plus accepted realization supplies pointwise
    accepted centered-address coverage. -/
theorem G8ActualXiHeightSplitSpectralRealityInputs.pointwiseCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (inputs : G8ActualXiHeightSplitSpectralRealityInputs)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8BookIIIPointwiseAcceptedCenteredAddressCoverage model :=
  (inputs.toFinalLiveHinge realization).pointwiseCoverage

/-- Height-split spectral reality plus accepted realization forwards to the
    existing conditional Mathlib handoff. -/
theorem G8ActualXiHeightSplitSpectralRealityInputs.mathlibRiemannHypothesis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (inputs : G8ActualXiHeightSplitSpectralRealityInputs)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    RiemannHypothesis :=
  (inputs.toFinalLiveHinge realization).mathlibRiemannHypothesis

-- ============================================================
-- COMPATIBILITY WITH THE STRONGER INPUT PACKAGE
-- ============================================================

/-- The earlier stronger spectral-reality package derives the height-split
    package by making the zero-height branch impossible. -/
def G8ActualXiSpectralRealityInputs.toHeightSplit :
    G8ActualXiSpectralRealityInputs →
      G8ActualXiHeightSplitSpectralRealityInputs :=
  fun inputs =>
    { spectralParameterReal := inputs.spectralParameterReal
      zeroHeightAxis := by
        intro z hZero
        exact False.elim (inputs.nontrivialHeight z hZero) }

/-- The existing Lane-A instantiation supplies height-split inputs through its
    stronger nonzero-height field. -/
def G8ActualXiSpectralRealityInstantiation.toHeightSplitInputs
    (inst : G8ActualXiSpectralRealityInstantiation) :
    G8ActualXiHeightSplitSpectralRealityInputs :=
  inst.inputs.toHeightSplit

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- Zero-height off-critical evidence refutes height-split spectral-reality
    inputs. -/
theorem G8ActualXiZeroHeightOffCriticalFalsifier.refutesHeightSplitInputs
    (w : G8ActualXiZeroHeightOffCriticalFalsifier)
    (inputs : G8ActualXiHeightSplitSpectralRealityInputs) :
    False :=
  w.refutesZeroHeightAxis inputs.zeroHeightAxis

/-- Nonzero-height non-real centered quadratic evidence refutes height-split
    spectral-reality inputs. -/
theorem
    G8ActualXiNonzeroHeightCenteredQuadraticNonrealFalsifier.refutesHeightSplitInputs
    (w : G8ActualXiNonzeroHeightCenteredQuadraticNonrealFalsifier)
    (inputs : G8ActualXiHeightSplitSpectralRealityInputs) :
    False :=
  w.nonreal (inputs.spectralParameterReal w.z.1)

/-- The old non-real centered quadratic falsifier also refutes the height-split
    package, since spectral-parameter reality is still global. -/
theorem G8ActualXiCenteredQuadraticNonrealFalsifier.refutesHeightSplitInputs
    (w : G8ActualXiCenteredQuadraticNonrealFalsifier)
    (inputs : G8ActualXiHeightSplitSpectralRealityInputs) :
    False :=
  w.nonreal (inputs.spectralParameterReal w.z)

/-- A centered-quadratic readout mismatch remains impossible independently of
    height splitting. -/
theorem
    G8ActualXiCenteredQuadraticReadoutMismatchFalsifier.refutesHeightSplitInputs
    (w : G8ActualXiCenteredQuadraticReadoutMismatchFalsifier)
    (_inputs : G8ActualXiHeightSplitSpectralRealityInputs) :
    False :=
  w.refutes

end Tau.BookIII.Bridge
