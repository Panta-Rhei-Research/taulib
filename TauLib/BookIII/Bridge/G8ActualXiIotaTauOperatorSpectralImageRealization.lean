import TauLib.BookIII.Bridge.G8ActualXiIotaTauOperatorSpectralImageSource

/-!
# TauLib.BookIII.Bridge.G8ActualXiIotaTauOperatorSpectralImageRealization

Proof-facing realization layer for the Book III `ιτ²` operator spectral image.

The certified scale and scaled-real-to-unscaled-real algebra are already
available downstream of `G8ActualXiIotaTauOperatorSpectralImageSource`.  This
module names the exact Book III payload still needed from independent operator
machinery:

* exact alignment with the `ιτ²`-scaled centered quadratic;
* exact real-valuedness of the selected operator spectral image.

Finite self-adjoint, K5, spectral-resolution, and finite-correspondence checks
may support provenance, but they do not discharge either exact field here.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- BOOK III REALIZATION TARGETS
-- ============================================================

/-- The exact scaled-alignment theorem target for the Book III operator
    spectral image. -/
def G8ActualXiIotaTauBookIIIScaledAlignmentTarget
    (operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ) : Prop :=
  G8ActualXiIotaTauScaledSpectralAlignment operatorSpectralValue

/-- The exact real-valuedness theorem target for the Book III operator
    spectral image. -/
def G8ActualXiIotaTauBookIIISpectralRealityTarget
    (operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ) : Prop :=
  G8ActualXiIotaTauScaledSpectralReality operatorSpectralValue

/-- Compact package for the two exact Book III operator-image targets. -/
structure G8ActualXiIotaTauBookIIISpectralImageTargets where
  operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ
  scaledAlignment :
    G8ActualXiIotaTauBookIIIScaledAlignmentTarget operatorSpectralValue
  spectralReality :
    G8ActualXiIotaTauBookIIISpectralRealityTarget operatorSpectralValue

-- ============================================================
-- REALIZATION CONTEXT
-- ============================================================

/-- Book III realization context for the `ιτ²` operator spectral image.

`bookIIIImageEvidence` records the intended independent operator/spectral source
for each carrier.  The load-bearing fields remain the exact scaled alignment
and exact spectral reality targets. -/
structure G8ActualXiIotaTauOperatorSpectralImageRealizationContext where
  operatorCtx : LemniscateOperatorContext
  operatorReady : LemniscateOperatorReady operatorCtx
  operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ
  bookIIIImageEvidence : G8ActualXiNonzeroHeightCarrier → Prop
  bookIIIImageEvidence_holds :
    ∀ z : G8ActualXiNonzeroHeightCarrier, bookIIIImageEvidence z
  scaledAlignment :
    G8ActualXiIotaTauBookIIIScaledAlignmentTarget operatorSpectralValue
  spectralReality :
    G8ActualXiIotaTauBookIIISpectralRealityTarget operatorSpectralValue
  scaleCertificate : G8IotaTau500dTowerScaleCertificate :=
    g8IotaTau500dTowerScaleCertificate
  diagnostics : G8ActualXiNonzeroHeightScaledOperatorDiagnostics := {}

/-- The realization context as the compact pair of exact Book III targets. -/
def G8ActualXiIotaTauOperatorSpectralImageRealizationContext.targets
    (ctx : G8ActualXiIotaTauOperatorSpectralImageRealizationContext) :
    G8ActualXiIotaTauBookIIISpectralImageTargets where
  operatorSpectralValue := ctx.operatorSpectralValue
  scaledAlignment := ctx.scaledAlignment
  spectralReality := ctx.spectralReality

-- ============================================================
-- ADAPTERS
-- ============================================================

/-- A Book III realization context instantiates the existing `ιτ²` operator
    spectral image source context. -/
def G8ActualXiIotaTauOperatorSpectralImageRealizationContext.toSourceContext
    (ctx : G8ActualXiIotaTauOperatorSpectralImageRealizationContext) :
    G8ActualXiIotaTauOperatorSpectralImageSourceContext where
  operatorCtx := ctx.operatorCtx
  operatorReady := ctx.operatorReady
  operatorSpectralValue := ctx.operatorSpectralValue
  scaledAlignment := ctx.scaledAlignment
  spectralReality := ctx.spectralReality
  scaleCertificate := ctx.scaleCertificate
  diagnostics := ctx.diagnostics

/-- A Book III realization context supplies the nonzero-height spectral
    parameter reality payload through the existing source corridor. -/
theorem
    G8ActualXiIotaTauOperatorSpectralImageRealizationContext.toSpectralParameterReal
    (ctx : G8ActualXiIotaTauOperatorSpectralImageRealizationContext) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  ctx.toSourceContext.toSpectralParameterReal

/-- A Book III realization context feeds the existing nonzero-height operator
    readout route. -/
def
    G8ActualXiIotaTauOperatorSpectralImageRealizationContext.toOperatorSpectralReadoutContext
    (ctx : G8ActualXiIotaTauOperatorSpectralImageRealizationContext) :
    G8ActualXiNonzeroHeightOperatorSpectralReadoutContext :=
  ctx.toSourceContext.toOperatorSpectralReadoutContext

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A pointwise mismatch refutes the Book III scaled-alignment target. -/
structure G8ActualXiIotaTauBookIIIScaledAlignmentTargetMismatch
    (operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ) where
  z : G8ActualXiNonzeroHeightCarrier
  mismatch :
    operatorSpectralValue z ≠
      (g8IotaTau500dSquaredReal : ℂ) *
        orthodoxXiCarrierCenteredQuadratic z.1

/-- Scaled-alignment mismatch is fatal for the exact Book III alignment target. -/
theorem G8ActualXiIotaTauBookIIIScaledAlignmentTargetMismatch.refutes
    {operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ}
    (w :
      G8ActualXiIotaTauBookIIIScaledAlignmentTargetMismatch
        operatorSpectralValue)
    (hTarget :
      G8ActualXiIotaTauBookIIIScaledAlignmentTarget
        operatorSpectralValue) :
    False :=
  w.mismatch (hTarget w.z)

/-- A pointwise non-real value refutes the Book III spectral-reality target. -/
structure G8ActualXiIotaTauBookIIISpectralRealityTargetMismatch
    (operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ) where
  z : G8ActualXiNonzeroHeightCarrier
  nonreal : (operatorSpectralValue z).im ≠ 0

/-- Spectral non-reality is fatal for the exact Book III reality target. -/
theorem G8ActualXiIotaTauBookIIISpectralRealityTargetMismatch.refutes
    {operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ}
    (w :
      G8ActualXiIotaTauBookIIISpectralRealityTargetMismatch
        operatorSpectralValue)
    (hTarget :
      G8ActualXiIotaTauBookIIISpectralRealityTarget
        operatorSpectralValue) :
    False :=
  w.nonreal (hTarget w.z)

/-- Book III image evidence by itself is not the scaled-alignment theorem. -/
structure G8ActualXiIotaTauBookIIIImageEvidenceOnly where
  operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ
  bookIIIImageEvidence : G8ActualXiNonzeroHeightCarrier → Prop
  bookIIIImageEvidence_holds :
    ∀ z : G8ActualXiNonzeroHeightCarrier, bookIIIImageEvidence z
  z : G8ActualXiNonzeroHeightCarrier
  exactScaledAlignmentFails :
    operatorSpectralValue z ≠
      (g8IotaTau500dSquaredReal : ℂ) *
        orthodoxXiCarrierCenteredQuadratic z.1

/-- Evidence-only records refute an attempted promotion to the exact alignment
    target when their declared value is not exactly aligned. -/
theorem G8ActualXiIotaTauBookIIIImageEvidenceOnly.refutesAlignmentTarget
    (w : G8ActualXiIotaTauBookIIIImageEvidenceOnly)
    (hTarget :
      G8ActualXiIotaTauBookIIIScaledAlignmentTarget
        w.operatorSpectralValue) :
    False :=
  w.exactScaledAlignmentFails (hTarget w.z)

end Tau.BookIII.Bridge
