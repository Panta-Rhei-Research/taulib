import TauLib.BookIII.Bridge.G8ActualXiCrossingMediatedLanding

/-!
# TauLib.BookIII.Bridge.G8ActualXiSpectralRealityInstantiation

Lane-A instantiation surface for the spectral-reality route.

The pure centered-quadratic readout is theorem-backed in
`G8ActualXiSpectralRealityCore`.  This module packages the two remaining
spectral inputs and forwards them to crossing-mediated evidence through the
existing spectral-reality and landing adapters.  It does not construct those
inputs and does not use O3, full divisor transfer, accepted coverage, the final
live hinge, or an RH handoff to prove them.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- LANE-A INPUT PACKAGE
-- ============================================================

/-- Lane-A spectral-reality instantiation package.

The package is intentionally thin: it contains exactly the two genuine
spectral inputs, while the centered-quadratic imaginary readout is supplied by
the theorem-backed algebraic identity. -/
structure G8ActualXiSpectralRealityInstantiation where
  inputs : G8ActualXiSpectralRealityInputs
  status : G8OffCriticalExclusionStatus := .openObligation

/-- Expose the centered spectral-parameter reality input. -/
theorem G8ActualXiSpectralRealityInstantiation.spectralParameterReal
    (inst : G8ActualXiSpectralRealityInstantiation)
    (z : OrthodoxXiZeroCarrier) :
    (orthodoxXiCarrierCenteredQuadratic z).im = 0 :=
  inst.inputs.spectralParameterReal z

/-- Expose the nonzero-height input. -/
theorem G8ActualXiSpectralRealityInstantiation.nontrivialHeight
    (inst : G8ActualXiSpectralRealityInstantiation)
    (z : OrthodoxXiZeroCarrier) :
    z.toZero.point.im ≠ 0 :=
  inst.inputs.nontrivialHeight z

/-- The Lane-A instantiation supplies the existing spectral-reality context. -/
def G8ActualXiSpectralRealityInstantiation.toSpectralRealityContext
    (inst : G8ActualXiSpectralRealityInstantiation) :
    G8ActualXiSpectralRealityContext :=
  G8ActualXiSpectralRealityContext.ofInputs inst.inputs

/-- The Lane-A instantiation supplies global crossing-mediated evidence via
    the existing spectral-reality adapter. -/
theorem G8ActualXiSpectralRealityInstantiation.toCrossingMediatedAll
    (inst : G8ActualXiSpectralRealityInstantiation) :
    G8ActualXiBoundaryReadoutCrossingMediatedAll :=
  inst.toSpectralRealityContext.toCrossingMediatedAll

/-- The Lane-A instantiation supplies actual centered-address balance. -/
theorem G8ActualXiSpectralRealityInstantiation.centeredAddressBalanced
    (inst : G8ActualXiSpectralRealityInstantiation) :
    G8ActualXiCenteredAddressBalanced :=
  inst.toSpectralRealityContext.centeredAddressBalanced

/-- The Lane-A instantiation supplies actual sigma-fixedness, still
    conditionally on its two explicit spectral inputs. -/
theorem G8ActualXiSpectralRealityInstantiation.actualSigmaFixed
    (inst : G8ActualXiSpectralRealityInstantiation) :
    G8ActualXiBoundaryCharacterSigmaFixed :=
  inst.toSpectralRealityContext.actualSigmaFixed

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A zero-height carrier refutes a Lane-A instantiation. -/
theorem G8ActualXiZeroHeightFalsifier.refutesInstantiation
    (w : G8ActualXiZeroHeightFalsifier)
    (inst : G8ActualXiSpectralRealityInstantiation) :
    False :=
  w.refutesInputs inst.inputs

/-- A non-real centered quadratic parameter refutes a Lane-A instantiation. -/
theorem G8ActualXiCenteredQuadraticNonrealFalsifier.refutesInstantiation
    (w : G8ActualXiCenteredQuadraticNonrealFalsifier)
    (inst : G8ActualXiSpectralRealityInstantiation) :
    False :=
  w.refutesInputs inst.inputs

/-- A readout mismatch is impossible independently of any spectral input. -/
theorem G8ActualXiCenteredQuadraticReadoutMismatchFalsifier.refutesInstantiation
    (w : G8ActualXiCenteredQuadraticReadoutMismatchFalsifier)
    (_inst : G8ActualXiSpectralRealityInstantiation) :
    False :=
  w.refutes

/-- Existing off-critical carrier evidence refutes a Lane-A instantiation
    through the spectral-reality context. -/
theorem G8ActualXiOffCriticalCarrierFalsifier.refutesSpectralRealityInstantiation
    (w : G8ActualXiOffCriticalCarrierFalsifier)
    (inst : G8ActualXiSpectralRealityInstantiation) :
    False :=
  w.refutesSpectralRealityContext inst.toSpectralRealityContext

end Tau.BookIII.Bridge
