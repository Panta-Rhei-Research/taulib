import TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightScaledOperatorSpectralImage
import TauLib.BookI.Boundary.TauRealIotaTauBBP

/-!
# TauLib.BookIII.Bridge.G8ActualXiIotaTauTowerSpectralScale

Certified 500-digit `ιτ²` tower scale for the nonzero-height Lane-A spectral
source.

This module instantiates the abstract nonzero scale from
`G8ActualXiNonzeroHeightScaledOperatorSpectralImage` with the 500-digit fiat
`ιτ` value certified against the BBP `TauReal.iota_tau_bbp` approximation.  It
does not prove the operator spectral image theorem: exact alignment with the
scaled centered quadratic and exact real-valuedness remain explicit fields.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.Boundary

-- ============================================================
-- 500-DIGIT IOTA-TAU SCALE
-- ============================================================

/-- The certified 500-digit fiat `ιτ` tower value read as a real scalar. -/
def g8IotaTau500dReal : ℝ :=
  ((TauRat.iota_tau_fiat_500d).toRat : ℝ)

/-- The intended Book III scale `ιτ²`, using the certified 500-digit tower
    value. -/
def g8IotaTau500dSquaredReal : ℝ :=
  g8IotaTau500dReal * g8IotaTau500dReal

/-- The 500-digit fiat `ιτ` tower value is positive. -/
theorem g8IotaTau500dReal_pos : 0 < g8IotaTau500dReal := by
  norm_num [g8IotaTau500dReal, TauRat.iota_tau_fiat_500d, TauRat.toRat,
    TauInt.toInt]

/-- The 500-digit fiat `ιτ` tower value is nonzero. -/
theorem g8IotaTau500dReal_ne_zero : g8IotaTau500dReal ≠ 0 :=
  ne_of_gt g8IotaTau500dReal_pos

/-- The certified 500-digit `ιτ²` tower scale is positive. -/
theorem g8IotaTau500dSquaredReal_pos : 0 < g8IotaTau500dSquaredReal := by
  unfold g8IotaTau500dSquaredReal
  exact mul_pos g8IotaTau500dReal_pos g8IotaTau500dReal_pos

/-- The certified 500-digit `ιτ²` tower scale is nonzero. -/
theorem g8IotaTau500dSquaredReal_ne_zero :
    g8IotaTau500dSquaredReal ≠ 0 :=
  ne_of_gt g8IotaTau500dSquaredReal_pos

/-- Diagnostic certificate recording the BBP-backed 500-digit source of the
    tower scale.  This evidence supports the scale choice but does not supply
    the operator real-valuedness theorem. -/
structure G8IotaTau500dTowerScaleCertificate where
  certified500d :
    TauRat.lt
      (((TauReal.iota_tau_bbp.approx 1850).sub
        TauRat.iota_tau_fiat_500d).abs)
      (TauRat.ofNatRecip (10^499 - 1))
  status : SpineStatus := .conditional_interface

/-- The shipped BBP/native-decision certificate for the 500-digit tower scale. -/
def g8IotaTau500dTowerScaleCertificate :
    G8IotaTau500dTowerScaleCertificate where
  certified500d := TauReal.iota_tau_bbp_certified_500d

/-- The certified 500-digit `ιτ²` scale as a `G8ActualXiSpectralScale`. -/
def g8IotaTau500dSquaredSpectralScale : G8ActualXiSpectralScale where
  scale := g8IotaTau500dSquaredReal
  scale_ne_zero := g8IotaTau500dSquaredReal_ne_zero
  intendedIotaTauSquaredDiagnostic := True

-- ============================================================
-- TOWER-SCALE SOURCE ADAPTERS
-- ============================================================

/-- Operator-facing readout contract specialized to the certified 500-digit
    `ιτ²` tower scale. -/
structure G8ActualXiIotaTauTowerScaledOperatorSpectralImageContext where
  operatorCtx : LemniscateOperatorContext
  operatorReady : LemniscateOperatorReady operatorCtx
  operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ
  operatorSpectralValue_eq_iotaTauSquaredCenteredQuadratic :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      operatorSpectralValue z =
        (g8IotaTau500dSquaredReal : ℂ) *
          orthodoxXiCarrierCenteredQuadratic z.1
  operatorSpectralValue_real :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      (operatorSpectralValue z).im = 0
  scaleCertificate : G8IotaTau500dTowerScaleCertificate :=
    g8IotaTau500dTowerScaleCertificate
  diagnostics : G8ActualXiNonzeroHeightScaledOperatorDiagnostics := {}

/-- The specialized tower-scale readout is an instance of the existing scaled
    operator spectral-image context. -/
def
    G8ActualXiIotaTauTowerScaledOperatorSpectralImageContext.toScaledOperatorSpectralImageContext
    (ctx : G8ActualXiIotaTauTowerScaledOperatorSpectralImageContext) :
    G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext where
  operatorCtx := ctx.operatorCtx
  operatorReady := ctx.operatorReady
  spectralScale := g8IotaTau500dSquaredSpectralScale
  operatorSpectralValue := ctx.operatorSpectralValue
  operatorSpectralValue_eq_scaledCenteredQuadratic := by
    intro z
    simpa [g8IotaTau500dSquaredSpectralScale] using
      ctx.operatorSpectralValue_eq_iotaTauSquaredCenteredQuadratic z
  operatorSpectralValue_real := ctx.operatorSpectralValue_real
  diagnostics := ctx.diagnostics

/-- The certified tower-scale source supplies the nonzero-height spectral
    parameter realness payload once exact operator alignment and
    real-valuedness are supplied. -/
theorem
    G8ActualXiIotaTauTowerScaledOperatorSpectralImageContext.toSpectralParameterReal
    (ctx : G8ActualXiIotaTauTowerScaledOperatorSpectralImageContext) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  ctx.toScaledOperatorSpectralImageContext.toSpectralParameterReal

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A claimed zero value for the certified 500-digit `ιτ²` scale refutes the
    scale certificate. -/
structure G8IotaTau500dTowerScaleZeroFalsifier where
  scale_zero : g8IotaTau500dSquaredReal = 0

/-- The 500-digit `ιτ²` tower scale cannot be zero. -/
theorem G8IotaTau500dTowerScaleZeroFalsifier.refutes
    (w : G8IotaTau500dTowerScaleZeroFalsifier) :
    False :=
  g8IotaTau500dSquaredReal_ne_zero w.scale_zero

/-- A scaled context whose scale differs from the certified tower scale is not
    the tower-scale specialization. -/
structure G8IotaTauTowerScaleMismatch
    (ctx : G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext) where
  scale_mismatch :
    ctx.spectralScale.scale ≠ g8IotaTau500dSquaredReal

/-- Tower-scale mismatch refutes an identification of a scaled context with the
    certified `ιτ²` specialization. -/
theorem G8IotaTauTowerScaleMismatch.refutesTowerScaleIdentification
    {ctx : G8ActualXiNonzeroHeightScaledOperatorSpectralImageContext}
    (w : G8IotaTauTowerScaleMismatch ctx)
    (hScale : ctx.spectralScale.scale = g8IotaTau500dSquaredReal) :
    False :=
  w.scale_mismatch hScale

/-- The 500-digit numerical certificate alone is not an operator spectral
    readout theorem. -/
structure G8IotaTauTowerScaleDiagnosticOnly where
  z : G8ActualXiNonzeroHeightCarrier
  operatorSpectralValue : ℂ
  scaleCertificate : G8IotaTau500dTowerScaleCertificate
  operatorSpectralValue_nonreal : operatorSpectralValue.im ≠ 0

/-- If a diagnostic-only record is identified with an exact tower-scale source,
    it is refuted by the source's real-valuedness field. -/
theorem G8IotaTauTowerScaleDiagnosticOnly.refutesContext
    (w : G8IotaTauTowerScaleDiagnosticOnly)
    (ctx : G8ActualXiIotaTauTowerScaledOperatorSpectralImageContext)
    (hSame : ctx.operatorSpectralValue w.z = w.operatorSpectralValue) :
    False := by
  apply w.operatorSpectralValue_nonreal
  rw [← hSame]
  exact ctx.operatorSpectralValue_real w.z

end Tau.BookIII.Bridge
