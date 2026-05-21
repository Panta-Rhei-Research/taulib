import TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightOperatorSpectralReadout
import TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightSpectralReality

/-!
# TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightSpectralReadout

Readout interface for the nonzero-height Lane-A spectral payload.

The previous wave isolated the remaining nonzero-height theorem:

```text
for each actual nonzero-height xi carrier,
the centered quadratic spectral parameter has imaginary part zero.
```

This module packages the next proof-facing surface.  A future Book III
operator/spectral theorem may supply a declared spectral value, prove that it
is exactly the centered quadratic value attached to the orthodox carrier, and
prove that the declared value is real.  Those two exact fields, not finite
diagnostics or downstream RH-facing machinery, are what discharge the local
payload.

No theorem here proves the readout from O3, accepted coverage, the final live
hinge, full divisor transfer, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- READOUT CONTEXT
-- ============================================================

/-- Diagnostic bookkeeping attached to a nonzero-height spectral readout.

These fields are deliberately not consumed by the proof of spectral reality.
They give future Book III operator work a place to record finite-stage or
self-adjointness evidence without treating such diagnostics as a global
readout theorem. -/
structure G8ActualXiNonzeroHeightSpectralReadoutDiagnostics where
  finiteSelfAdjointDiagnostic : Prop := True
  finiteSpectralCorrespondenceDiagnostic : Prop := True
  status : G8OffCriticalExclusionStatus := .openObligation

/-- A proof-facing spectral readout for actual nonzero-height `xi` carriers.

The load-bearing fields are the exact alignment with
`orthodoxXiCarrierCenteredQuadratic` and real-valuedness of the declared
spectral value.  Diagnostics are retained only as non-load-bearing evidence. -/
structure G8ActualXiNonzeroHeightSpectralReadoutContext where
  spectralValue : G8ActualXiNonzeroHeightCarrier → ℂ
  spectralValue_eq_centeredQuadratic :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      spectralValue z = orthodoxXiCarrierCenteredQuadratic z.1
  spectralValue_real :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      (spectralValue z).im = 0
  diagnostics : G8ActualXiNonzeroHeightSpectralReadoutDiagnostics := {}

-- ============================================================
-- ADAPTER FROM THE OPERATOR-SOURCE LAYER
-- ============================================================

/-- Forget the operator-specific diagnostics into the existing downstream
    readout diagnostic surface. -/
def G8ActualXiNonzeroHeightOperatorReadoutDiagnostics.toReadoutDiagnostics
    (diag : G8ActualXiNonzeroHeightOperatorReadoutDiagnostics) :
    G8ActualXiNonzeroHeightSpectralReadoutDiagnostics where
  finiteSelfAdjointDiagnostic := diag.finiteSelfAdjointDiagnostic
  finiteSpectralCorrespondenceDiagnostic :=
    diag.finiteSpectralCorrespondenceDiagnostic

/-- The clean operator-facing source context instantiates the existing
    downstream spectral-readout context. -/
def G8ActualXiNonzeroHeightOperatorSpectralReadoutContext.toSpectralReadoutContext
    (ctx : G8ActualXiNonzeroHeightOperatorSpectralReadoutContext) :
    G8ActualXiNonzeroHeightSpectralReadoutContext where
  spectralValue := ctx.spectralValue
  spectralValue_eq_centeredQuadratic :=
    ctx.spectralValue_eq_centeredQuadratic
  spectralValue_real := ctx.spectralValue_real
  diagnostics := ctx.diagnostics.toReadoutDiagnostics

-- ============================================================
-- ADAPTERS TO THE EXISTING LANE-A SPINE
-- ============================================================

/-- Exact spectral-value alignment plus real-valuedness supplies the
    nonzero-height spectral payload. -/
theorem G8ActualXiNonzeroHeightSpectralReadoutContext.toSpectralParameterReal
    (ctx : G8ActualXiNonzeroHeightSpectralReadoutContext) :
    G8ActualXiNonzeroHeightSpectralParameterReal := by
  intro z
  rw [← ctx.spectralValue_eq_centeredQuadratic z]
  exact ctx.spectralValue_real z

/-- The theorem-backed paired eta closure supplies the zero-height branch; the
    readout context supplies the nonzero-height branch. -/
def G8ActualXiNonzeroHeightSpectralReadoutContext.toInputs
    (ctx : G8ActualXiNonzeroHeightSpectralReadoutContext) :
    G8ActualXiNonzeroHeightSpectralRealityInputs :=
  G8ActualXiNonzeroHeightSpectralRealityInputs.ofPairedEtaClosure
    ctx.toSpectralParameterReal

/-- The readout context supplies actual centered-address balance. -/
theorem G8ActualXiNonzeroHeightSpectralReadoutContext.centeredAddressBalanced
    (ctx : G8ActualXiNonzeroHeightSpectralReadoutContext) :
    G8ActualXiCenteredAddressBalanced :=
  ctx.toInputs.centeredAddressBalanced

/-- The readout context supplies actual sigma-fixedness. -/
theorem G8ActualXiNonzeroHeightSpectralReadoutContext.actualSigmaFixed
    (ctx : G8ActualXiNonzeroHeightSpectralReadoutContext) :
    G8ActualXiBoundaryCharacterSigmaFixed :=
  ctx.toInputs.actualSigmaFixed

/-- The readout context supplies global crossing-mediated readout evidence. -/
theorem G8ActualXiNonzeroHeightSpectralReadoutContext.toCrossingMediatedAll
    (ctx : G8ActualXiNonzeroHeightSpectralReadoutContext) :
    G8ActualXiBoundaryReadoutCrossingMediatedAll :=
  ctx.toInputs.toCrossingMediatedAll

/-- The readout context plus sigma-fixed accepted realization builds the
    existing final live hinge. -/
def G8ActualXiNonzeroHeightSpectralReadoutContext.toFinalLiveHinge
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8ActualXiNonzeroHeightSpectralReadoutContext)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8FinalLiveHinge model :=
  ctx.toInputs.toFinalLiveHinge realization

/-- The readout context plus accepted realization supplies pointwise accepted
    centered-address coverage. -/
theorem G8ActualXiNonzeroHeightSpectralReadoutContext.pointwiseCoverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8ActualXiNonzeroHeightSpectralReadoutContext)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8BookIIIPointwiseAcceptedCenteredAddressCoverage model :=
  (ctx.toFinalLiveHinge realization).pointwiseCoverage

/-- The readout context plus accepted realization forwards through the existing
    conditional Mathlib handoff. -/
theorem G8ActualXiNonzeroHeightSpectralReadoutContext.mathlibRiemannHypothesis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (ctx : G8ActualXiNonzeroHeightSpectralReadoutContext)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    RiemannHypothesis :=
  (ctx.toFinalLiveHinge realization).mathlibRiemannHypothesis

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A mismatch between the declared spectral value and the centered quadratic
    value refutes the readout context. -/
structure G8ActualXiNonzeroHeightSpectralValueMismatch
    (ctx : G8ActualXiNonzeroHeightSpectralReadoutContext) where
  z : G8ActualXiNonzeroHeightCarrier
  mismatch :
    ctx.spectralValue z ≠ orthodoxXiCarrierCenteredQuadratic z.1

/-- Declared spectral-value mismatch is fatal for the readout context. -/
theorem G8ActualXiNonzeroHeightSpectralValueMismatch.refutes
    {ctx : G8ActualXiNonzeroHeightSpectralReadoutContext}
    (w : G8ActualXiNonzeroHeightSpectralValueMismatch ctx) :
    False :=
  w.mismatch (ctx.spectralValue_eq_centeredQuadratic w.z)

/-- A declared spectral value with nonzero imaginary part refutes the readout
    context. -/
structure G8ActualXiNonzeroHeightSpectralValueNonreal
    (ctx : G8ActualXiNonzeroHeightSpectralReadoutContext) where
  z : G8ActualXiNonzeroHeightCarrier
  nonreal : (ctx.spectralValue z).im ≠ 0

/-- Non-real declared spectral values are fatal for the readout context. -/
theorem G8ActualXiNonzeroHeightSpectralValueNonreal.refutes
    {ctx : G8ActualXiNonzeroHeightSpectralReadoutContext}
    (w : G8ActualXiNonzeroHeightSpectralValueNonreal ctx) :
    False :=
  w.nonreal (ctx.spectralValue_real w.z)

/-- Diagnostic-only self-adjoint evidence does not by itself supply the exact
    real-valued spectral readout required by this lane. -/
structure G8ActualXiNonzeroHeightSelfAdjointDiagnosticOnly where
  z : G8ActualXiNonzeroHeightCarrier
  spectralValue : ℂ
  finiteSelfAdjointDiagnostic : Prop
  diagnosticEvidence : finiteSelfAdjointDiagnostic
  spectralValue_nonreal : spectralValue.im ≠ 0

/-- A diagnostic-only record with the same declared value as a readout context
    refutes that context.  The contradiction uses exact real-valuedness, not
    the diagnostic proof field. -/
theorem G8ActualXiNonzeroHeightSelfAdjointDiagnosticOnly.refutesContext
    (w : G8ActualXiNonzeroHeightSelfAdjointDiagnosticOnly)
    (ctx : G8ActualXiNonzeroHeightSpectralReadoutContext)
    (hSame : ctx.spectralValue w.z = w.spectralValue) :
    False := by
  apply w.spectralValue_nonreal
  rw [← hSame]
  exact ctx.spectralValue_real w.z

end Tau.BookIII.Bridge
