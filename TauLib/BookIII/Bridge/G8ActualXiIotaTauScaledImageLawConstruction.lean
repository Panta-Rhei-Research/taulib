import TauLib.BookIII.Bridge.G8ActualXiIotaTauBookIIIOperatorSpectralImageSource

/-!
# TauLib.BookIII.Bridge.G8ActualXiIotaTauScaledImageLawConstruction

Canonical construction of the `ιτ²` scaled-image law for nonzero-height Lane A.

The previous source split isolated two obligations:

* exact scaled-image alignment;
* exact self-adjoint spectral real-valuedness.

This module closes the first obligation for the canonical selected value

```text
z ↦ ιτ² * orthodoxXiCarrierCenteredQuadratic z.
```

It does not prove that this selected value belongs to the spectrum of the Book
III operator, and it does not prove self-adjoint spectral real-valuedness.  The
remaining source theorem is exactly the self-adjoint reality source for this
canonical selected value.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- CANONICAL SCALED IMAGE LAW
-- ============================================================

/-- Canonical `ιτ²`-scaled operator spectral value selected by the Lane-A Book
    III image law. -/
def g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue
    (z : G8ActualXiNonzeroHeightCarrier) : ℂ :=
  (g8IotaTau500dSquaredReal : ℂ) *
    orthodoxXiCarrierCenteredQuadratic z.1

/-- Provenance predicate for the canonical Book III scaled-image readout.

The predicate is intentionally just the exact definitional readout equation.
It is not spectral membership and it is not real-valuedness. -/
def G8ActualXiIotaTauCanonicalScaledImageReadout
    (z : G8ActualXiNonzeroHeightCarrier) : Prop :=
  g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z =
    (g8IotaTau500dSquaredReal : ℂ) *
      orthodoxXiCarrierCenteredQuadratic z.1

/-- The canonical scaled-image readout holds by definition. -/
theorem g8ActualXiIotaTauCanonicalScaledImageReadout_holds
    (z : G8ActualXiNonzeroHeightCarrier) :
    G8ActualXiIotaTauCanonicalScaledImageReadout z :=
  rfl

/-- The canonical selected value satisfies the exact `ιτ²` scaled-alignment
    target by definition. -/
theorem g8ActualXiIotaTauCanonicalScaledAlignment :
    G8ActualXiIotaTauBookIIIScaledAlignmentTarget
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue := by
  intro z
  rfl

/-- The canonical selected value closes the Book III scaled-image law source. -/
def g8ActualXiIotaTauCanonicalScaledImageLawSource :
    G8ActualXiIotaTauBookIIIScaledImageLawSource
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue where
  bookIIIImageEvidence := G8ActualXiIotaTauCanonicalScaledImageReadout
  bookIIIImageEvidence_holds :=
    g8ActualXiIotaTauCanonicalScaledImageReadout_holds
  scaledAlignment := g8ActualXiIotaTauCanonicalScaledAlignment

-- ============================================================
-- REMAINING SELF-ADJOINT REALITY TARGET
-- ============================================================

/-- The remaining nonzero-height operator theorem after the canonical
    scaled-image law is closed: the canonical selected values must be spectral
    values of a ready self-adjoint Book III operator package and therefore real. -/
def G8ActualXiIotaTauCanonicalSelfAdjointRealityTarget
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) : Type 2 :=
  G8ActualXiIotaTauBookIIISelfAdjointRealitySource
    operatorCtx operatorReady
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue

/-- The canonical scaled-image law plus the remaining self-adjoint reality
    source builds the combined Book III operator spectral-image source. -/
def g8ActualXiIotaTauBookIIISource_ofCanonicalSelfAdjointReality
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (selfAdjointReality :
      G8ActualXiIotaTauCanonicalSelfAdjointRealityTarget
        operatorCtx operatorReady) :
    G8ActualXiIotaTauBookIIIOperatorSpectralImageSource where
  operatorCtx := operatorCtx
  operatorReady := operatorReady
  operatorSpectralValue :=
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue
  imageLaw := g8ActualXiIotaTauCanonicalScaledImageLawSource
  selfAdjointReality := selfAdjointReality

/-- A canonical self-adjoint reality source supplies the nonzero-height
    spectral-parameter reality payload through the Book III source corridor. -/
theorem
    g8ActualXiIotaTauSpectralParameterReal_ofCanonicalSelfAdjointReality
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (selfAdjointReality :
      G8ActualXiIotaTauCanonicalSelfAdjointRealityTarget
        operatorCtx operatorReady) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  (g8ActualXiIotaTauBookIIISource_ofCanonicalSelfAdjointReality
    selfAdjointReality).toSpectralParameterReal

/-- A canonical self-adjoint reality source feeds the existing operator readout
    route. -/
def
    g8ActualXiIotaTauOperatorReadout_ofCanonicalSelfAdjointReality
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (selfAdjointReality :
      G8ActualXiIotaTauCanonicalSelfAdjointRealityTarget
        operatorCtx operatorReady) :
    G8ActualXiNonzeroHeightOperatorSpectralReadoutContext :=
  (g8ActualXiIotaTauBookIIISource_ofCanonicalSelfAdjointReality
    selfAdjointReality).toOperatorSpectralReadoutContext

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- The canonical scaled-image law cannot be refuted by an alleged scaled
    mismatch. -/
theorem G8ActualXiIotaTauBookIIIScaledImageEvidenceMismatch.refutesCanonical
    (w :
      G8ActualXiIotaTauBookIIIScaledImageEvidenceMismatch
        g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue) :
    False :=
  w.refutes g8ActualXiIotaTauCanonicalScaledImageLawSource

/-- After the canonical image law construction, the only remaining way to block
    the combined source is failure of self-adjoint spectral reality. -/
structure G8ActualXiIotaTauCanonicalSelfAdjointRealityGap
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  noRealitySource :
    G8ActualXiIotaTauCanonicalSelfAdjointRealityTarget
      operatorCtx operatorReady → False

/-- A self-adjoint-reality gap refutes any attempted combined source whose
    selected value is the canonical scaled image and whose self-adjoint source is
    transported along that equality. -/
theorem G8ActualXiIotaTauCanonicalSelfAdjointRealityGap.refutesCanonicalSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (gap :
      G8ActualXiIotaTauCanonicalSelfAdjointRealityGap
        operatorCtx operatorReady)
    (selfAdjointReality :
      G8ActualXiIotaTauCanonicalSelfAdjointRealityTarget
        operatorCtx operatorReady) :
    False :=
  gap.noRealitySource selfAdjointReality

end Tau.BookIII.Bridge
