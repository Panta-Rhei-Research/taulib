import TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightOperatorSpectralReadout

/-!
# TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightScaledOperatorSpectralImage

Scaled operator spectral-image source contract for the nonzero-height Lane-A
payload.

Book III's operator picture reads the centered quadratic through a nonzero real
scale, manuscript-wise `iota_tau^2 * (s * (1 - s) - 1/4)`.  The downstream Lean
spine consumes the unscaled centered quadratic.  This module closes exactly the
safe algebraic step:

```text
real nonzero scale * centered quadratic is real
  -> centered quadratic is real.
```

The actual global operator theorem remains explicit as the real-valuedness of
the scaled operator spectral image.  Finite and determinant diagnostics stay
non-load-bearing.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- SCALED OPERATOR SOURCE
-- ============================================================

/-- Abstract nonzero real scale for the Book III spectral image.

The intended manuscript instance is `iota_tau^2`, but this bridge keeps the
scale abstract so the nonzero-scale algebra can be reused without importing the
heavier constant layer. -/
structure G8ActualXiSpectralScale where
  scale : ℝ
  scale_ne_zero : scale ≠ 0
  intendedIotaTauSquaredDiagnostic : Prop := True

/-- The unit scale used to view the older unscaled readout as a scaled source. -/
def G8ActualXiSpectralScale.unit : G8ActualXiSpectralScale where
  scale := 1
  scale_ne_zero := by norm_num
  intendedIotaTauSquaredDiagnostic := True

/-- A nonzero real scale transfers real-valuedness from the scaled complex
    value to the unscaled complex value. -/
theorem g8_im_eq_zero_of_scaled_real_nonzero
    (spectralScale : G8ActualXiSpectralScale)
    {q : ℂ}
    (hScaled : (((spectralScale.scale : ℂ) * q).im = 0)) :
    q.im = 0 := by
  have hMul : spectralScale.scale * q.im = 0 := by
    simpa [Complex.mul_im] using hScaled
  rcases mul_eq_zero.mp hMul with hScale | hIm
  · exact False.elim (spectralScale.scale_ne_zero hScale)
  · exact hIm

/-- Diagnostic evidence attached to the scaled operator source.

These fields deliberately do not prove the global real-valued readout.  The
load-bearing proof fields are exact scaled alignment and exact real-valuedness
of the selected spectral image. -/
structure G8ActualXiNonzeroHeightScaledOperatorDiagnostics where
  finiteSelfAdjointDiagnostic : Prop := True
  finiteK5DiagonalDiagnostic : Prop := True
  finiteSpectralCorrespondenceDiagnostic : Prop := True
  determinantBridgeDiagnostic : Prop := True
  status : SpineStatus := .conditional_interface

/-- Scaled operator-facing readout contract for nonzero-height actual `xi`
    carriers.

`operatorSpectralValue` is allowed to be the Book III scaled spectral image.
The adapter below removes the nonzero real scale and returns the existing
unscaled operator readout context. -/
structure G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext where
  operatorCtx : LemniscateOperatorContext
  operatorReady : LemniscateOperatorReady operatorCtx
  spectralScale : G8ActualXiSpectralScale
  operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ
  operatorSpectralValue_eq_scaledCenteredQuadratic :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      operatorSpectralValue z =
        (spectralScale.scale : ℂ) *
          orthodoxXiCarrierCenteredQuadratic z.1
  operatorSpectralValue_real :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      (operatorSpectralValue z).im = 0
  diagnostics : G8ActualXiNonzeroHeightScaledOperatorDiagnostics := {}

/-- Exact scaled alignment plus real-valuedness supplies the clean
    nonzero-height spectral payload. -/
theorem
    G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext.toSpectralParameterReal
    (ctx : G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext) :
    G8ActualXiNonzeroHeightSpectralParameterReal := by
  intro z
  apply g8_im_eq_zero_of_scaled_real_nonzero ctx.spectralScale
  rw [← ctx.operatorSpectralValue_eq_scaledCenteredQuadratic z]
  exact ctx.operatorSpectralValue_real z

/-- A scaled operator source converts into the existing unscaled operator
    readout context by dividing out the nonzero real scale at the level of
    imaginary parts. -/
def
    G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext.toOperatorSpectralReadoutContext
    (ctx : G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext) :
    G8ActualXiNonzeroHeightOperatorSpectralReadoutContext where
  operatorCtx := ctx.operatorCtx
  operatorReady := ctx.operatorReady
  spectralValue := fun z => orthodoxXiCarrierCenteredQuadratic z.1
  spectralValue_eq_centeredQuadratic := by
    intro z
    rfl
  spectralValue_real := ctx.toSpectralParameterReal
  diagnostics := {}

/-- The older unscaled operator readout is the special case with unit scale. -/
def
    G8ActualXiNonzeroHeightOperatorSpectralReadoutContext.toScaledOperatorSpectralImageContext
    (ctx : G8ActualXiNonzeroHeightOperatorSpectralReadoutContext) :
    G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext where
  operatorCtx := ctx.operatorCtx
  operatorReady := ctx.operatorReady
  spectralScale := G8ActualXiSpectralScale.unit
  operatorSpectralValue := ctx.spectralValue
  operatorSpectralValue_eq_scaledCenteredQuadratic := by
    intro z
    rw [ctx.spectralValue_eq_centeredQuadratic z]
    simp [G8ActualXiSpectralScale.unit]
  operatorSpectralValue_real := ctx.spectralValue_real
  diagnostics := {}

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A claimed zero value of a spectral scale refutes the scale certificate. -/
structure G8ActualXiSpectralScaleZeroFalsifier
    (spectralScale : G8ActualXiSpectralScale) where
  scale_zero : spectralScale.scale = 0

/-- Zero scale is fatal for a nonzero-scale certificate. -/
theorem G8ActualXiSpectralScaleZeroFalsifier.refutes
    {spectralScale : G8ActualXiSpectralScale}
    (w : G8ActualXiSpectralScaleZeroFalsifier spectralScale) :
    False :=
  spectralScale.scale_ne_zero w.scale_zero

/-- A mismatch between the selected spectral image and the scaled centered
    quadratic refutes the scaled source context. -/
structure G8ActualXiScaledOperatorSpectralValueMismatch
    (ctx : G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext) where
  z : G8ActualXiNonzeroHeightCarrier
  mismatch :
    ctx.operatorSpectralValue z ≠
      (ctx.spectralScale.scale : ℂ) *
        orthodoxXiCarrierCenteredQuadratic z.1

/-- Scaled spectral-value mismatch is fatal for the source context. -/
theorem G8ActualXiScaledOperatorSpectralValueMismatch.refutes
    {ctx : G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext}
    (w : G8ActualXiScaledOperatorSpectralValueMismatch ctx) :
    False :=
  w.mismatch (ctx.operatorSpectralValue_eq_scaledCenteredQuadratic w.z)

/-- A non-real declared scaled operator spectral image refutes the scaled
    source context. -/
structure G8ActualXiScaledOperatorSpectralValueNonreal
    (ctx : G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext) where
  z : G8ActualXiNonzeroHeightCarrier
  nonreal : (ctx.operatorSpectralValue z).im ≠ 0

/-- Non-real scaled spectral images are fatal for the source context. -/
theorem G8ActualXiScaledOperatorSpectralValueNonreal.refutes
    {ctx : G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext}
    (w : G8ActualXiScaledOperatorSpectralValueNonreal ctx) :
    False :=
  w.nonreal (ctx.operatorSpectralValue_real w.z)

/-- Finite and determinant diagnostics without exact real-valuedness do not
    instantiate the scaled source theorem. -/
structure G8ActualXiScaledOperatorDiagnosticOnly where
  z : G8ActualXiNonzeroHeightCarrier
  spectralScale : G8ActualXiSpectralScale
  operatorSpectralValue : ℂ
  finiteSelfAdjointDiagnostic : Prop
  finiteK5DiagonalDiagnostic : Prop
  finiteSpectralCorrespondenceDiagnostic : Prop
  determinantBridgeDiagnostic : Prop
  selfAdjointEvidence : finiteSelfAdjointDiagnostic
  k5Evidence : finiteK5DiagonalDiagnostic
  correspondenceEvidence : finiteSpectralCorrespondenceDiagnostic
  determinantEvidence : determinantBridgeDiagnostic
  operatorSpectralValue_nonreal : operatorSpectralValue.im ≠ 0

/-- A diagnostic-only record with the same declared scaled value as a source
    context refutes that context through exact real-valuedness. -/
theorem G8ActualXiScaledOperatorDiagnosticOnly.refutesContext
    (w : G8ActualXiScaledOperatorDiagnosticOnly)
    (ctx : G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext)
    (hSame : ctx.operatorSpectralValue w.z = w.operatorSpectralValue) :
    False := by
  apply w.operatorSpectralValue_nonreal
  rw [← hSame]
  exact ctx.operatorSpectralValue_real w.z

end Tau.BookIII.Bridge
