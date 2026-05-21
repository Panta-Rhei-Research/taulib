import TauLib.BookIII.Bridge.G8LemniscateStandardEigenvalueSpectrumSource
import TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightSpectralReadout

/-!
# TauLib.BookIII.Bridge.G8LemniscateStandardEigenvalueLaneAAssembly

Downstream Lane-A assembly for the standard lemniscate eigenvalue source.

The upstream source module proves that standard lemniscate eigenvalues are real.
This assembly module records the payoff of the remaining exact mode-index
target:

```text
canonical iota_tau^2 scaled actual-xi value = lambda_n
  -> nonzero-height spectral-parameter reality
  -> paired-eta zero-height closure + nonzero-height branch
  -> actual sigma-fixedness
  -> final live hinge, conditional on accepted tower realization
```

The mode-index theorem remains explicit.  This module does not construct that
mode from finite diagnostics and does not use downstream RH-facing machinery to
prove it.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- LANE-A CONSEQUENCES OF STANDARD MODE MEMBERSHIP
-- ============================================================

/-- Exact standard mode membership supplies the sharpened Lane-A input package:
    the zero-height branch comes from the paired-eta closure, and the
    nonzero-height branch comes from standard spectrum real-valuedness. -/
def
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource.toNonzeroHeightInputs
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
        operatorCtx operatorReady) :
    G8ActualXiNonzeroHeightSpectralRealityInputs :=
  G8ActualXiNonzeroHeightSpectralRealityInputs.ofPairedEtaClosure
    source.toSpectralParameterReal

/-- Exact standard mode membership supplies actual centered-address balance. -/
theorem
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource.centeredAddressBalanced
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
        operatorCtx operatorReady) :
    G8ActualXiCenteredAddressBalanced :=
  source.toNonzeroHeightInputs.centeredAddressBalanced

/-- Exact standard mode membership supplies actual sigma-fixedness. -/
theorem
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource.actualSigmaFixed
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
        operatorCtx operatorReady) :
    G8ActualXiBoundaryCharacterSigmaFixed :=
  source.toNonzeroHeightInputs.actualSigmaFixed

/-- Exact standard mode membership supplies crossing-mediated readout evidence. -/
theorem
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource.toCrossingMediatedAll
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
        operatorCtx operatorReady) :
    G8ActualXiBoundaryReadoutCrossingMediatedAll :=
  source.toNonzeroHeightInputs.toCrossingMediatedAll

/-- Exact standard mode membership plus sigma-fixed accepted realization builds
    the existing final live hinge. -/
def G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource.toFinalLiveHinge
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (source :
      G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
        operatorCtx operatorReady)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8FinalLiveHinge model :=
  source.toNonzeroHeightInputs.toFinalLiveHinge realization

/-- Exact standard mode membership plus accepted realization supplies pointwise
    accepted centered-address coverage. -/
theorem
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource.pointwiseCoverage
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (source :
      G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
        operatorCtx operatorReady)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8BookIIIPointwiseAcceptedCenteredAddressCoverage model :=
  (source.toFinalLiveHinge realization).pointwiseCoverage

/-- Exact standard mode membership plus accepted realization forwards through
    the existing conditional Mathlib handoff. -/
theorem
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource.mathlibRiemannHypothesis
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (source :
      G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
        operatorCtx operatorReady)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    RiemannHypothesis :=
  (source.toFinalLiveHinge realization).mathlibRiemannHypothesis

-- ============================================================
-- FALSIFIER
-- ============================================================

/-- A nonzero-height off-critical carrier refutes the standard mode-index
    source through its Lane-A consequences. -/
theorem
    G8ActualXiNonzeroHeightOffCriticalFalsifier.refutesStandardEigenvalueIndexSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w : G8ActualXiNonzeroHeightOffCriticalFalsifier)
    (source :
      G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
        operatorCtx operatorReady) :
    False :=
  w.refutesInputs source.toNonzeroHeightInputs

end Tau.BookIII.Bridge
