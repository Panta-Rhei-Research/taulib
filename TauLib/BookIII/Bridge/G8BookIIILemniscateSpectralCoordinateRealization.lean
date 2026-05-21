import TauLib.BookIII.Bridge.G8CanonicalXiSpectralModeCorrespondenceSource

/-!
# TauLib.BookIII.Bridge.G8BookIIILemniscateSpectralCoordinateRealization

Book III spectral-coordinate realization target for the remaining Lane-A
nonzero-height source theorem.

The previous layer decomposed exact mode membership through the finite
`spectral_parameter spectralIndex stage` readout.  This module names the
global realization theorem needed from the Book III operator/spectral machine:

```text
actual nonzero-height xi carrier
  -> spectral index and finite stage
  -> canonical iota_tau^2 scaled value
     = lemniscate_eigenvalue (spectral_parameter index stage).
```

All downstream consequences are theorem-backed adapters.  The equality above is
the mathematical payload; finite self-adjoint, K5, nesting, or stage checks
remain diagnostic evidence only.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- GLOBAL REALIZATION TARGET
-- ============================================================

/-- The pure global Book III coordinate-realization theorem target.

It says every actual nonzero-height `xi` carrier has a Book III spectral
coordinate and finite stage whose computed `spectral_parameter` mode has exactly
the canonical `iota_tau^2` scaled value as its lemniscate eigenvalue. -/
def G8BookIIILemniscateSpectralCoordinateRealizationTarget : Prop :=
  ∀ z : G8ActualXiNonzeroHeightCarrier,
    ∃ spectralIndex stage : Tau.Denotation.TauIdx,
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z =
        (Tau.BookIII.Doors.lemniscate_eigenvalue
          (g8CanonicalXiSpectralCoordinateMode spectralIndex stage) : ℂ)

/-- Proof-facing source package for the Book III spectral-coordinate
realization theorem.

The operator fields record the intended source side.  The load-bearing theorem
field remains the exact coordinate-mode eigenvalue equality. -/
structure G8BookIIILemniscateSpectralCoordinateRealizationSource where
  operatorCtx : LemniscateOperatorContext
  operatorReady : LemniscateOperatorReady operatorCtx
  spectralIndexOf :
    G8ActualXiNonzeroHeightCarrier → Tau.Denotation.TauIdx
  stageOf :
    G8ActualXiNonzeroHeightCarrier → Tau.Denotation.TauIdx
  canonicalValue_eq_coordinateMode :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z =
        (Tau.BookIII.Doors.lemniscate_eigenvalue
          (g8CanonicalXiSpectralCoordinateMode
            (spectralIndexOf z) (stageOf z)) : ℂ)
  diagnostics : G8CanonicalXiSpectralCoordinateDiagnostics := {}

/-- A realization source supplies the pure global target. -/
theorem G8BookIIILemniscateSpectralCoordinateRealizationSource.target
    (source : G8BookIIILemniscateSpectralCoordinateRealizationSource) :
    G8BookIIILemniscateSpectralCoordinateRealizationTarget := by
  intro z
  exact
    ⟨source.spectralIndexOf z, source.stageOf z,
      source.canonicalValue_eq_coordinateMode z⟩

/-- The pure global target can be packaged as a source once an operator package
is supplied.  This is classical choice only; it does not prove the target. -/
def g8BookIIILemniscateSpectralCoordinateRealizationSource_ofTarget
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx)
    (target : G8BookIIILemniscateSpectralCoordinateRealizationTarget) :
    G8BookIIILemniscateSpectralCoordinateRealizationSource where
  operatorCtx := operatorCtx
  operatorReady := operatorReady
  spectralIndexOf := fun z => Classical.choose (target z)
  stageOf := fun z =>
    Classical.choose (Classical.choose_spec (target z))
  canonicalValue_eq_coordinateMode := fun z =>
    Classical.choose_spec (Classical.choose_spec (target z))

-- ============================================================
-- ADAPTERS TO THE EXISTING LANE-A SPINE
-- ============================================================

/-- A realization source builds the existing coordinate-correspondence source. -/
def G8BookIIILemniscateSpectralCoordinateRealizationSource.toCorrespondenceSource
    (source : G8BookIIILemniscateSpectralCoordinateRealizationSource) :
    G8CanonicalXiSpectralModeCorrespondenceSource where
  certificate := fun z =>
    { spectralIndex := source.spectralIndexOf z
      stage := source.stageOf z
      canonicalValue_eq_coordinateMode :=
        source.canonicalValue_eq_coordinateMode z
      diagnostics :=
        g8CanonicalXiSpectralCoordinateDiagnostics (source.stageOf z) }
  diagnostics := source.diagnostics

/-- The pure global target builds the existing coordinate-correspondence source
by choice. -/
def g8CanonicalXiSpectralModeCorrespondenceSource_ofRealizationTarget
    (target : G8BookIIILemniscateSpectralCoordinateRealizationTarget) :
    G8CanonicalXiSpectralModeCorrespondenceSource where
  certificate := fun z =>
    { spectralIndex := Classical.choose (target z)
      stage := Classical.choose (Classical.choose_spec (target z))
      canonicalValue_eq_coordinateMode :=
        Classical.choose_spec (Classical.choose_spec (target z))
      diagnostics :=
        g8CanonicalXiSpectralCoordinateDiagnostics
          (Classical.choose (Classical.choose_spec (target z))) }

/-- A realization source supplies global pointwise mode membership. -/
theorem
    G8BookIIILemniscateSpectralCoordinateRealizationSource.membershipAll
    (source : G8BookIIILemniscateSpectralCoordinateRealizationSource) :
    G8CanonicalXiSpectralModeMembershipAll :=
  source.toCorrespondenceSource.membershipAll

/-- A realization source builds the standard eigenvalue index source. -/
def
    G8BookIIILemniscateSpectralCoordinateRealizationSource.toStandardEigenvalueIndexSource
    (source : G8BookIIILemniscateSpectralCoordinateRealizationSource) :
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
      source.operatorCtx source.operatorReady :=
  source.toCorrespondenceSource.toStandardEigenvalueIndexSource
    (operatorCtx := source.operatorCtx)
    (operatorReady := source.operatorReady)

/-- A realization source supplies the canonical standard-eigenvalue membership
target. -/
theorem
    G8BookIIILemniscateSpectralCoordinateRealizationSource.toStandardMembershipTarget
    (source : G8BookIIILemniscateSpectralCoordinateRealizationSource) :
    G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
      source.operatorCtx source.operatorReady :=
  source.toStandardEigenvalueIndexSource.toMembershipTarget

/-- A realization source supplies the canonical self-adjoint reality source via
the standard eigenvalue corridor. -/
def
    G8BookIIILemniscateSpectralCoordinateRealizationSource.toCanonicalSelfAdjointSource
    (source : G8BookIIILemniscateSpectralCoordinateRealizationSource) :
    G8ActualXiIotaTauCanonicalSelfAdjointRealitySource
      source.operatorCtx source.operatorReady :=
  source.toStandardEigenvalueIndexSource.toCanonicalSelfAdjointSource

/-- A realization source supplies the combined Book III operator spectral-image
source through the existing canonical self-adjoint route. -/
def
    G8BookIIILemniscateSpectralCoordinateRealizationSource.toBookIIIOperatorSpectralImageSource
    (source : G8BookIIILemniscateSpectralCoordinateRealizationSource) :
    G8ActualXiIotaTauBookIIIOperatorSpectralImageSource :=
  source.toCanonicalSelfAdjointSource.toBookIIISource

/-- A realization source supplies nonzero-height spectral-parameter reality. -/
theorem
    G8BookIIILemniscateSpectralCoordinateRealizationSource.toSpectralParameterReal
    (source : G8BookIIILemniscateSpectralCoordinateRealizationSource) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  source.toCorrespondenceSource.toSpectralParameterReal
    (operatorCtx := source.operatorCtx)
    (operatorReady := source.operatorReady)

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A single carrier with no exact Book III coordinate refutes the global
realization target. -/
structure G8BookIIILemniscateSpectralCoordinateRealizationGap where
  z : G8ActualXiNonzeroHeightCarrier
  noCoordinate :
    ∀ spectralIndex stage : Tau.Denotation.TauIdx,
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
        (Tau.BookIII.Doors.lemniscate_eigenvalue
          (g8CanonicalXiSpectralCoordinateMode spectralIndex stage) : ℂ)

/-- A pointwise coordinate gap refutes the pure global target. -/
theorem G8BookIIILemniscateSpectralCoordinateRealizationGap.refutesTarget
    (gap : G8BookIIILemniscateSpectralCoordinateRealizationGap)
    (target : G8BookIIILemniscateSpectralCoordinateRealizationTarget) :
    False := by
  rcases target gap.z with ⟨spectralIndex, stage, hEq⟩
  exact gap.noCoordinate spectralIndex stage hEq

/-- A pointwise coordinate gap refutes a packaged realization source. -/
theorem G8BookIIILemniscateSpectralCoordinateRealizationGap.refutesSource
    (gap : G8BookIIILemniscateSpectralCoordinateRealizationGap)
    (source : G8BookIIILemniscateSpectralCoordinateRealizationSource) :
    False :=
  gap.refutesTarget source.target

/-- Finite diagnostics without exact coordinate-mode equality do not construct
the Book III realization target. -/
structure G8BookIIILemniscateSpectralCoordinateDiagnosticsOnly where
  z : G8ActualXiNonzeroHeightCarrier
  spectralIndex : Tau.Denotation.TauIdx
  stage : Tau.Denotation.TauIdx
  spectralParamDiagnostic :
    Tau.BookIII.Doors.spectral_param_check stage stage = true
  finiteCorrespondenceDiagnostic :
    Tau.BookIII.Doors.spectral_correspondence_finite stage = true
  eigenvalueNestingDiagnostic :
    Tau.BookIII.Doors.eigenvalue_nesting_check stage = true
  noExactEquality :
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
      (Tau.BookIII.Doors.lemniscate_eigenvalue
        (g8CanonicalXiSpectralCoordinateMode spectralIndex stage) : ℂ)

/-- Diagnostics-only data refutes a source that chooses the same coordinate. -/
theorem
    G8BookIIILemniscateSpectralCoordinateDiagnosticsOnly.refutesSameCoordinateSource
    (w : G8BookIIILemniscateSpectralCoordinateDiagnosticsOnly)
    (source : G8BookIIILemniscateSpectralCoordinateRealizationSource)
    (hIndex : source.spectralIndexOf w.z = w.spectralIndex)
    (hStage : source.stageOf w.z = w.stage) :
    False := by
  apply w.noExactEquality
  simpa [hIndex, hStage] using source.canonicalValue_eq_coordinateMode w.z

/-- A bounded coordinate mode without exact eigenvalue equality is still not a
realization source. -/
structure G8BookIIILemniscateSpectralCoordinateBoundedOnly where
  z : G8ActualXiNonzeroHeightCarrier
  spectralIndex : Tau.Denotation.TauIdx
  stage : Tau.Denotation.TauIdx
  modeBounded :
    g8CanonicalXiSpectralCoordinateMode spectralIndex stage ≤ stage
  noExactEquality :
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
      (Tau.BookIII.Doors.lemniscate_eigenvalue
        (g8CanonicalXiSpectralCoordinateMode spectralIndex stage) : ℂ)

/-- Bounded mode data refutes a source that claims the same coordinate but lacks
the required exact equality. -/
theorem
    G8BookIIILemniscateSpectralCoordinateBoundedOnly.refutesSameCoordinateSource
    (w : G8BookIIILemniscateSpectralCoordinateBoundedOnly)
    (source : G8BookIIILemniscateSpectralCoordinateRealizationSource)
    (hIndex : source.spectralIndexOf w.z = w.spectralIndex)
    (hStage : source.stageOf w.z = w.stage) :
    False := by
  apply w.noExactEquality
  simpa [hIndex, hStage] using source.canonicalValue_eq_coordinateMode w.z

end Tau.BookIII.Bridge
