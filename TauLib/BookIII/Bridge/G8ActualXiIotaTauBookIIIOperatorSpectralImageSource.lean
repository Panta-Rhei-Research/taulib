import TauLib.BookIII.Bridge.G8ActualXiIotaTauOperatorSpectralImageRealization

/-!
# TauLib.BookIII.Bridge.G8ActualXiIotaTauBookIIIOperatorSpectralImageSource

Sharper Book III source split for the nonzero-height Lane-A operator image.

The previous realization layer names the two exact payloads:

* the selected Book III spectral image is the certified `ιτ²`-scaled centered
  quadratic;
* that selected spectral image is real-valued.

This module separates those fields into their intended Book III origins:

* a scaled-image law source;
* a self-adjoint spectral-reality source for values known to belong to the
  operator spectrum.

The finite operator checks remain provenance/diagnostic evidence only.  They do
not prove global real-valuedness or any downstream RH-facing statement.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- SCALED IMAGE LAW SOURCE
-- ============================================================

/-- Source-side evidence that a nonzero-height carrier has a Book III scaled
    operator image.  The evidence predicate is provenance; the exact equality is
    the load-bearing field. -/
structure G8ActualXiIotaTauBookIIIScaledImageLawSource
    (operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ) where
  bookIIIImageEvidence : G8ActualXiNonzeroHeightCarrier → Prop
  bookIIIImageEvidence_holds :
    ∀ z : G8ActualXiNonzeroHeightCarrier, bookIIIImageEvidence z
  scaledAlignment :
    G8ActualXiIotaTauBookIIIScaledAlignmentTarget operatorSpectralValue

-- ============================================================
-- SELF-ADJOINT REALITY SOURCE
-- ============================================================

/-- Source-side evidence that the selected Book III operator images are spectral
    values of a self-adjoint operator package.  Membership is provenance; the
    exact real-valuedness selector is the load-bearing field. -/
structure G8ActualXiIotaTauBookIIISelfAdjointRealitySource
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx)
    (operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ) where
  spectralMembership : G8ActualXiNonzeroHeightCarrier → Prop
  spectralMembership_holds :
    ∀ z : G8ActualXiNonzeroHeightCarrier, spectralMembership z
  selfAdjointSpectralReality :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      spectralMembership z → (operatorSpectralValue z).im = 0
  diagnostics : G8ActualXiNonzeroHeightScaledOperatorDiagnostics := {}

/-- A self-adjoint reality source supplies the exact spectral-reality target. -/
def G8ActualXiIotaTauBookIIISelfAdjointRealitySource.spectralReality
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ}
    (source :
      G8ActualXiIotaTauBookIIISelfAdjointRealitySource
        operatorCtx operatorReady operatorSpectralValue) :
    G8ActualXiIotaTauBookIIISpectralRealityTarget operatorSpectralValue :=
  fun z => source.selfAdjointSpectralReality z (source.spectralMembership_holds z)

-- ============================================================
-- COMBINED BOOK III SOURCE
-- ============================================================

/-- Combined Book III source package for the `ιτ²` operator spectral image.

This is the current nonzero-height Lane-A source theorem written in its most
proof-facing form: image-law alignment plus self-adjoint spectral reality. -/
structure G8ActualXiIotaTauBookIIIOperatorSpectralImageSource where
  operatorCtx : LemniscateOperatorContext
  operatorReady : LemniscateOperatorReady operatorCtx
  operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ
  imageLaw :
    G8ActualXiIotaTauBookIIIScaledImageLawSource operatorSpectralValue
  selfAdjointReality :
    G8ActualXiIotaTauBookIIISelfAdjointRealitySource
      operatorCtx operatorReady operatorSpectralValue

/-- The combined source instantiates the previous realization context. -/
def G8ActualXiIotaTauBookIIIOperatorSpectralImageSource.toRealizationContext
    (source : G8ActualXiIotaTauBookIIIOperatorSpectralImageSource) :
    G8ActualXiIotaTauOperatorSpectralImageRealizationContext where
  operatorCtx := source.operatorCtx
  operatorReady := source.operatorReady
  operatorSpectralValue := source.operatorSpectralValue
  bookIIIImageEvidence := source.imageLaw.bookIIIImageEvidence
  bookIIIImageEvidence_holds := source.imageLaw.bookIIIImageEvidence_holds
  scaledAlignment := source.imageLaw.scaledAlignment
  spectralReality := source.selfAdjointReality.spectralReality
  diagnostics := source.selfAdjointReality.diagnostics

/-- The combined Book III source supplies nonzero-height spectral-parameter
    reality through the existing `ιτ²` source corridor. -/
theorem G8ActualXiIotaTauBookIIIOperatorSpectralImageSource.toSpectralParameterReal
    (source : G8ActualXiIotaTauBookIIIOperatorSpectralImageSource) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  source.toRealizationContext.toSpectralParameterReal

/-- The combined Book III source feeds the existing operator readout corridor. -/
def
    G8ActualXiIotaTauBookIIIOperatorSpectralImageSource.toOperatorSpectralReadoutContext
    (source : G8ActualXiIotaTauBookIIIOperatorSpectralImageSource) :
    G8ActualXiNonzeroHeightOperatorSpectralReadoutContext :=
  source.toRealizationContext.toOperatorSpectralReadoutContext

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- Book III scaled-image evidence without exact scaled equality is not enough
    to instantiate the scaled-image law source. -/
structure G8ActualXiIotaTauBookIIIScaledImageEvidenceMismatch
    (operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ) where
  bookIIIImageEvidence : G8ActualXiNonzeroHeightCarrier → Prop
  bookIIIImageEvidence_holds :
    ∀ z : G8ActualXiNonzeroHeightCarrier, bookIIIImageEvidence z
  z : G8ActualXiNonzeroHeightCarrier
  mismatch :
    operatorSpectralValue z ≠
      (g8IotaTau500dSquaredReal : ℂ) *
        orthodoxXiCarrierCenteredQuadratic z.1

/-- Scaled-image evidence with a pointwise mismatch refutes the exact image-law
    source. -/
theorem G8ActualXiIotaTauBookIIIScaledImageEvidenceMismatch.refutes
    {operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ}
    (w :
      G8ActualXiIotaTauBookIIIScaledImageEvidenceMismatch
        operatorSpectralValue)
    (source :
      G8ActualXiIotaTauBookIIIScaledImageLawSource
        operatorSpectralValue) :
    False :=
  w.mismatch (source.scaledAlignment w.z)

/-- Spectral membership evidence without exact real-valuedness is not enough to
    instantiate the self-adjoint reality source. -/
structure G8ActualXiIotaTauBookIIISpectralMembershipNonreal
    (operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ) where
  z : G8ActualXiNonzeroHeightCarrier
  spectralMembership : Prop
  membershipEvidence : spectralMembership
  nonreal : (operatorSpectralValue z).im ≠ 0

/-- A non-real selected spectral value refutes any self-adjoint reality source
    whose membership predicate includes that point. -/
theorem G8ActualXiIotaTauBookIIISpectralMembershipNonreal.refutes
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ}
    (w :
      G8ActualXiIotaTauBookIIISpectralMembershipNonreal
        operatorSpectralValue)
    (source :
      G8ActualXiIotaTauBookIIISelfAdjointRealitySource
        operatorCtx operatorReady operatorSpectralValue)
    (hMembership :
      source.spectralMembership w.z = w.spectralMembership) :
    False := by
  apply w.nonreal
  exact
    source.selfAdjointSpectralReality w.z
      (by
        rw [hMembership]
        exact w.membershipEvidence)

/-- Operator readiness plus finite diagnostics alone do not produce the Book III
    source when the selected value is explicitly non-real. -/
structure G8ActualXiIotaTauBookIIIOperatorDiagnosticsOnly where
  operatorCtx : LemniscateOperatorContext
  operatorReady : LemniscateOperatorReady operatorCtx
  operatorSpectralValue : G8ActualXiNonzeroHeightCarrier → ℂ
  z : G8ActualXiNonzeroHeightCarrier
  finiteSelfAdjointDiagnostic : Prop
  finiteK5DiagonalDiagnostic : Prop
  finiteSpectralCorrespondenceDiagnostic : Prop
  selfAdjointEvidence : finiteSelfAdjointDiagnostic
  k5Evidence : finiteK5DiagonalDiagnostic
  correspondenceEvidence : finiteSpectralCorrespondenceDiagnostic
  nonreal : (operatorSpectralValue z).im ≠ 0

/-- Diagnostics-only records are refuted by an actual combined Book III source
    with the same selected value. -/
theorem G8ActualXiIotaTauBookIIIOperatorDiagnosticsOnly.refutesSource
    (w : G8ActualXiIotaTauBookIIIOperatorDiagnosticsOnly)
    (source : G8ActualXiIotaTauBookIIIOperatorSpectralImageSource)
    (hSame :
      source.operatorSpectralValue = w.operatorSpectralValue) :
    False := by
  apply w.nonreal
  rw [← hSame]
  exact source.selfAdjointReality.spectralReality w.z

end Tau.BookIII.Bridge
