import TauLib.BookIII.Bridge.G8ActualXiIotaTauTowerSpectralScale

/-!
# TauLib.BookIII.Bridge.G8ActualXiIotaTauOperatorSpectralImageSource

Proof-facing source layer for the nonzero-height Lane-A operator image payload.

The certified 500-digit `ιτ²` scale is already theorem-backed.  The remaining
operator theorem is now split into two exact fields:

* the selected Book III spectral image is exactly `ιτ²` times the centered
  quadratic of the actual `xi` carrier;
* the selected spectral image is real-valued.

This module only packages those fields and forwards them into the existing
scaled-source and nonzero-height spectral-realness corridors.  Finite
self-adjoint/K5/stage evidence remains diagnostic and never substitutes for
exact real-valuedness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- IOTA-TAU OPERATOR SPECTRAL IMAGE PAYLOAD
-- ============================================================

/-- Pointwise exact alignment of a selected spectral image with the certified
    `ιτ²`-scaled centered quadratic. -/
def G8ActualXiIotaTauScaledSpectralAlignment
    (operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ) : Prop :=
  ∀ z : G8ActualXiNonzeroHeightCarrier,
    operatorSpectralValue z =
      (g8IotaTau500dSquaredReal : ℂ) *
        orthodoxXiCarrierCenteredQuadratic z.1

/-- Pointwise real-valuedness of a selected operator spectral image. -/
def G8ActualXiIotaTauScaledSpectralReality
    (operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ) : Prop :=
  ∀ z : G8ActualXiNonzeroHeightCarrier,
    (operatorSpectralValue z).im = 0

/-- The exact nonzero-height operator image payload, split into alignment and
    real-valuedness. -/
structure G8ActualXiIotaTauOperatorSpectralImagePayload where
  operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ
  scaledAlignment :
    G8ActualXiIotaTauScaledSpectralAlignment operatorSpectralValue
  spectralReality :
    G8ActualXiIotaTauScaledSpectralReality operatorSpectralValue

/-- Source context for the certified `ιτ²` operator spectral image.

The load-bearing fields are `scaledAlignment` and `spectralReality`.  Operator
readiness and finite diagnostics record the intended Book III source lane but do
not by themselves prove the global real-valued readout. -/
structure G8ActualXiIotaTauOperatorSpectralImageSourceContext where
  operatorCtx : LemniscateOperatorContext
  operatorReady : LemniscateOperatorReady operatorCtx
  operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ
  scaledAlignment :
    G8ActualXiIotaTauScaledSpectralAlignment operatorSpectralValue
  spectralReality :
    G8ActualXiIotaTauScaledSpectralReality operatorSpectralValue
  scaleCertificate : G8IotaTau500dTowerScaleCertificate :=
    g8IotaTau500dTowerScaleCertificate
  diagnostics : G8ActualXiNonzeroHeightScaledOperatorDiagnostics := {}

/-- The source context as a compact payload. -/
def G8ActualXiIotaTauOperatorSpectralImageSourceContext.payload
    (ctx : G8ActualXiIotaTauOperatorSpectralImageSourceContext) :
    G8ActualXiIotaTauOperatorSpectralImagePayload where
  operatorSpectralValue := ctx.operatorSpectralValue
  scaledAlignment := ctx.scaledAlignment
  spectralReality := ctx.spectralReality

-- ============================================================
-- ADAPTERS
-- ============================================================

/-- The source context is exactly the previously defined certified tower-scale
    scaled spectral image context. -/
def
    G8ActualXiIotaTauOperatorSpectralImageSourceContext.toTowerScaledOperatorSpectralImageContext
    (ctx : G8ActualXiIotaTauOperatorSpectralImageSourceContext) :
    G8ActualXiIotaTauTowerScaledOperatorSpectralImageContext where
  operatorCtx := ctx.operatorCtx
  operatorReady := ctx.operatorReady
  operatorSpectralValue := ctx.operatorSpectralValue
  operatorSpectralValue_eq_iotaTauSquaredCenteredQuadratic :=
    ctx.scaledAlignment
  operatorSpectralValue_real := ctx.spectralReality
  scaleCertificate := ctx.scaleCertificate
  diagnostics := ctx.diagnostics

/-- The source context supplies the nonzero-height spectral-realness payload
    once exact `ιτ²` alignment and real-valuedness are supplied. -/
theorem
    G8ActualXiIotaTauOperatorSpectralImageSourceContext.toSpectralParameterReal
    (ctx : G8ActualXiIotaTauOperatorSpectralImageSourceContext) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  ctx.toTowerScaledOperatorSpectralImageContext.toSpectralParameterReal

/-- The source context feeds the existing unscaled nonzero-height operator
    readout corridor by dividing out the certified nonzero real scale. -/
def
    G8ActualXiIotaTauOperatorSpectralImageSourceContext.toOperatorSpectralReadoutContext
    (ctx : G8ActualXiIotaTauOperatorSpectralImageSourceContext) :
    G8ActualXiNonzeroHeightOperatorSpectralReadoutContext :=
  ctx.toTowerScaledOperatorSpectralImageContext
    |>.toScaledOperatorSpectralImageContext
    |>.toOperatorSpectralReadoutContext

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- Wrong exact `ιτ²` alignment refutes a source context. -/
structure G8ActualXiIotaTauScaledAlignmentMismatch
    (ctx : G8ActualXiIotaTauOperatorSpectralImageSourceContext) where
  z : G8ActualXiNonzeroHeightCarrier
  mismatch :
    ctx.operatorSpectralValue z ≠
      (g8IotaTau500dSquaredReal : ℂ) *
        orthodoxXiCarrierCenteredQuadratic z.1

/-- Scaled alignment mismatch is fatal for the source context. -/
theorem G8ActualXiIotaTauScaledAlignmentMismatch.refutes
    {ctx : G8ActualXiIotaTauOperatorSpectralImageSourceContext}
    (w : G8ActualXiIotaTauScaledAlignmentMismatch ctx) :
    False :=
  w.mismatch (ctx.scaledAlignment w.z)

/-- Non-real selected operator spectral values refute a source context. -/
structure G8ActualXiIotaTauScaledSpectralRealityMismatch
    (ctx : G8ActualXiIotaTauOperatorSpectralImageSourceContext) where
  z : G8ActualXiNonzeroHeightCarrier
  nonreal : (ctx.operatorSpectralValue z).im ≠ 0

/-- Spectral non-reality is fatal for the source context. -/
theorem G8ActualXiIotaTauScaledSpectralRealityMismatch.refutes
    {ctx : G8ActualXiIotaTauOperatorSpectralImageSourceContext}
    (w : G8ActualXiIotaTauScaledSpectralRealityMismatch ctx) :
    False :=
  w.nonreal (ctx.spectralReality w.z)

/-- Finite Book III diagnostics without exact real-valuedness are not the
    operator spectral image theorem. -/
structure G8ActualXiIotaTauFiniteDiagnosticsOnly where
  z : G8ActualXiNonzeroHeightCarrier
  operatorSpectralValue : ℂ
  scaleCertificate : G8IotaTau500dTowerScaleCertificate
  finiteSelfAdjointDiagnostic : Prop
  finiteK5DiagonalDiagnostic : Prop
  finiteSpectralCorrespondenceDiagnostic : Prop
  selfAdjointEvidence : finiteSelfAdjointDiagnostic
  k5Evidence : finiteK5DiagonalDiagnostic
  correspondenceEvidence : finiteSpectralCorrespondenceDiagnostic
  operatorSpectralValue_nonreal : operatorSpectralValue.im ≠ 0

/-- A finite-diagnostics-only record cannot be identified with a source context
    if its declared value is non-real. -/
theorem G8ActualXiIotaTauFiniteDiagnosticsOnly.refutesContext
    (w : G8ActualXiIotaTauFiniteDiagnosticsOnly)
    (ctx : G8ActualXiIotaTauOperatorSpectralImageSourceContext)
    (hSame : ctx.operatorSpectralValue w.z = w.operatorSpectralValue) :
    False := by
  apply w.operatorSpectralValue_nonreal
  rw [← hSame]
  exact ctx.spectralReality w.z

/-- Axis-offset or weaker projection data cannot replace exact scaled
    centered-quadratic alignment. -/
structure G8ActualXiIotaTauAxisOffsetOnlySpectralAttempt where
  z : G8ActualXiNonzeroHeightCarrier
  operatorSpectralValue : ℂ
  axisOffsetAgreementDiagnostic : Prop
  axisOffsetAgreementEvidence : axisOffsetAgreementDiagnostic
  exactScaledAlignmentFails :
    operatorSpectralValue ≠
      (g8IotaTau500dSquaredReal : ℂ) *
        orthodoxXiCarrierCenteredQuadratic z.1

/-- A projection-only attempt is refuted if it is promoted to an exact source
    context with the same declared spectral value. -/
theorem G8ActualXiIotaTauAxisOffsetOnlySpectralAttempt.refutesContext
    (w : G8ActualXiIotaTauAxisOffsetOnlySpectralAttempt)
    (ctx : G8ActualXiIotaTauOperatorSpectralImageSourceContext)
    (hSame : ctx.operatorSpectralValue w.z = w.operatorSpectralValue) :
    False := by
  apply w.exactScaledAlignmentFails
  rw [← hSame]
  exact ctx.scaledAlignment w.z

end Tau.BookIII.Bridge
