import TauLib.BookIII.Bridge.G8CanonicalXiSpectralModeMembership
import TauLib.BookIII.Doors.SpectralCorrespondenceFinite

/-!
# TauLib.BookIII.Bridge.G8CanonicalXiSpectralModeCorrespondenceSource

Book III spectral-coordinate source surface for the remaining Lane-A
nonzero-height mode theorem.

The previous layer named the exact target:

```text
canonical iota_tau^2 scaled xi value = lemniscate_eigenvalue mode.
```

This module decomposes `mode` through the finite Book III coordinate readout
`spectral_parameter spectralIndex stage`.  The finite checks are recorded as
diagnostics only.  The load-bearing field is still exact equality with the
lemniscate eigenvalue at the computed coordinate mode.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- SPECTRAL COORDINATE DIAGNOSTICS
-- ============================================================

/-- Non-load-bearing finite diagnostics attached to a Book III spectral
    coordinate readout. -/
structure G8CanonicalXiSpectralCoordinateDiagnostics where
  spectralParamDiagnostic : Prop := True
  finiteCorrespondenceDiagnostic : Prop := True
  eigenvalueNestingDiagnostic : Prop := True

/-- The standard finite diagnostic propositions for a chosen stage. -/
def g8CanonicalXiSpectralCoordinateDiagnostics
    (stage : Tau.Denotation.TauIdx) :
    G8CanonicalXiSpectralCoordinateDiagnostics where
  spectralParamDiagnostic :=
    Tau.BookIII.Doors.spectral_param_check stage stage = true
  finiteCorrespondenceDiagnostic :=
    Tau.BookIII.Doors.spectral_correspondence_finite stage = true
  eigenvalueNestingDiagnostic :=
    Tau.BookIII.Doors.eigenvalue_nesting_check stage = true

-- ============================================================
-- POINTWISE CORRESPONDENCE CERTIFICATE
-- ============================================================

/-- The Book III coordinate mode associated to a spectral index and stage. -/
def g8CanonicalXiSpectralCoordinateMode
    (spectralIndex stage : Tau.Denotation.TauIdx) : Tau.Denotation.TauIdx :=
  Tau.BookIII.Doors.spectral_parameter spectralIndex stage

/-- The coordinate mode is bounded by its finite stage. -/
theorem g8CanonicalXiSpectralCoordinateMode_le_stage
    (spectralIndex stage : Tau.Denotation.TauIdx) :
    g8CanonicalXiSpectralCoordinateMode spectralIndex stage ≤ stage := by
  by_cases hStage : stage = 0
  · subst stage
    simp [g8CanonicalXiSpectralCoordinateMode,
      Tau.BookIII.Doors.spectral_parameter]
  · have hlt :
        spectralIndex % (stage + 1) < stage + 1 :=
      Nat.mod_lt spectralIndex (Nat.succ_pos stage)
    have hle : spectralIndex % (stage + 1) ≤ stage :=
      Nat.lt_succ_iff.mp hlt
    simpa [g8CanonicalXiSpectralCoordinateMode,
      Tau.BookIII.Doors.spectral_parameter, hStage] using hle

/-- A pointwise Book III spectral-coordinate certificate for the canonical
    scaled actual-`xi` value.

The finite coordinate fields explain where the mode came from; the equality
field is the actual theorem payload. -/
structure G8CanonicalXiSpectralModeCorrespondenceCertificate
    (z : G8ActualXiNonzeroHeightCarrier) where
  spectralIndex : Tau.Denotation.TauIdx
  stage : Tau.Denotation.TauIdx
  canonicalValue_eq_coordinateMode :
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z =
      (Tau.BookIII.Doors.lemniscate_eigenvalue
        (g8CanonicalXiSpectralCoordinateMode spectralIndex stage) : ℂ)
  diagnostics : G8CanonicalXiSpectralCoordinateDiagnostics :=
    g8CanonicalXiSpectralCoordinateDiagnostics stage

/-- The computed mode of a pointwise correspondence certificate. -/
def G8CanonicalXiSpectralModeCorrespondenceCertificate.mode
    {z : G8ActualXiNonzeroHeightCarrier}
    (cert : G8CanonicalXiSpectralModeCorrespondenceCertificate z) :
    Tau.Denotation.TauIdx :=
  g8CanonicalXiSpectralCoordinateMode cert.spectralIndex cert.stage

/-- The certificate mode is bounded by its finite stage. -/
theorem G8CanonicalXiSpectralModeCorrespondenceCertificate.mode_le_stage
    {z : G8ActualXiNonzeroHeightCarrier}
    (cert : G8CanonicalXiSpectralModeCorrespondenceCertificate z) :
    cert.mode ≤ cert.stage :=
  g8CanonicalXiSpectralCoordinateMode_le_stage
    cert.spectralIndex cert.stage

/-- The eigenvalue selected by the coordinate mode is definitionally `mode^2`. -/
theorem G8CanonicalXiSpectralModeCorrespondenceCertificate.eigenvalue_formula
    {z : G8ActualXiNonzeroHeightCarrier}
    (cert : G8CanonicalXiSpectralModeCorrespondenceCertificate z) :
    Tau.BookIII.Doors.lemniscate_eigenvalue cert.mode =
      cert.mode * cert.mode :=
  rfl

/-- A coordinate certificate converts to the previously isolated mode
    certificate. -/
def G8CanonicalXiSpectralModeCorrespondenceCertificate.toModeCertificate
    {z : G8ActualXiNonzeroHeightCarrier}
    (cert : G8CanonicalXiSpectralModeCorrespondenceCertificate z) :
    G8CanonicalXiSpectralModeCertificate z where
  mode := cert.mode
  canonicalValue_eq_mode := cert.canonicalValue_eq_coordinateMode
  diagnostics := g8StandardLemniscateSpectrumRealityDiagnostics

-- ============================================================
-- GLOBAL SOURCE AND ADAPTERS
-- ============================================================

/-- Global Book III spectral-coordinate source for every actual nonzero-height
    carrier. -/
structure G8CanonicalXiSpectralModeCorrespondenceSource where
  certificate :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      G8CanonicalXiSpectralModeCorrespondenceCertificate z
  diagnostics : G8CanonicalXiSpectralCoordinateDiagnostics := {}

/-- A correspondence source builds the pointwise mode-membership source. -/
def G8CanonicalXiSpectralModeCorrespondenceSource.toModeMembershipSource
    (source : G8CanonicalXiSpectralModeCorrespondenceSource) :
    G8CanonicalXiSpectralModeMembershipSource where
  certificate := fun z => (source.certificate z).toModeCertificate
  diagnostics := g8StandardLemniscateSpectrumRealityDiagnostics

/-- A correspondence source supplies global mode membership. -/
theorem G8CanonicalXiSpectralModeCorrespondenceSource.membershipAll
    (source : G8CanonicalXiSpectralModeCorrespondenceSource) :
    G8CanonicalXiSpectralModeMembershipAll :=
  source.toModeMembershipSource.membershipAll

/-- A correspondence source builds the existing standard eigenvalue index
    source. -/
def G8CanonicalXiSpectralModeCorrespondenceSource.toStandardEigenvalueIndexSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source : G8CanonicalXiSpectralModeCorrespondenceSource) :
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
      operatorCtx operatorReady :=
  source.toModeMembershipSource.toStandardEigenvalueIndexSource
    (operatorCtx := operatorCtx)
    (operatorReady := operatorReady)

/-- A correspondence source supplies the nonzero-height spectral-parameter
    reality payload through the standard eigenvalue corridor. -/
theorem G8CanonicalXiSpectralModeCorrespondenceSource.toSpectralParameterReal
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source : G8CanonicalXiSpectralModeCorrespondenceSource) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  source.toModeMembershipSource.toSpectralParameterReal
    (operatorCtx := operatorCtx)
    (operatorReady := operatorReady)

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- Finite coordinate diagnostics without the exact eigenvalue equality do not
    form a pointwise correspondence certificate. -/
structure G8CanonicalXiSpectralCoordinateDiagnosticsOnly where
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

/-- Diagnostics-only data refutes a certificate using the same coordinate. -/
theorem
    G8CanonicalXiSpectralCoordinateDiagnosticsOnly.refutesSameCoordinateCertificate
    (w : G8CanonicalXiSpectralCoordinateDiagnosticsOnly)
    (cert :
      G8CanonicalXiSpectralModeCorrespondenceCertificate w.z)
    (hIndex : cert.spectralIndex = w.spectralIndex)
    (hStage : cert.stage = w.stage) :
    False := by
  apply w.noExactEquality
  simpa [hIndex, hStage] using cert.canonicalValue_eq_coordinateMode

/-- A claimed extracted mode that differs from the coordinate mode refutes the
    certificate's mode selector. -/
structure G8CanonicalXiSpectralCoordinateWrongMode
    (z : G8ActualXiNonzeroHeightCarrier) where
  certificate : G8CanonicalXiSpectralModeCorrespondenceCertificate z
  claimedMode : Tau.Denotation.TauIdx
  wrongMode :
    claimedMode ≠
      g8CanonicalXiSpectralCoordinateMode
        certificate.spectralIndex certificate.stage

/-- The only mode extracted from a coordinate certificate is its computed
    `spectral_parameter` mode. -/
theorem G8CanonicalXiSpectralCoordinateWrongMode.refutesClaimedMode
    {z : G8ActualXiNonzeroHeightCarrier}
    (w : G8CanonicalXiSpectralCoordinateWrongMode z)
    (hClaimed : w.claimedMode = w.certificate.mode) :
    False := by
  exact w.wrongMode (by simpa [G8CanonicalXiSpectralModeCorrespondenceCertificate.mode] using hClaimed)

/-- A carrier with no exact coordinate-mode equality refutes a global
    correspondence source. -/
structure G8CanonicalXiSpectralCoordinateExactEqualityMissing where
  z : G8ActualXiNonzeroHeightCarrier
  noCoordinateEquality :
    ∀ spectralIndex stage : Tau.Denotation.TauIdx,
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
        (Tau.BookIII.Doors.lemniscate_eigenvalue
          (g8CanonicalXiSpectralCoordinateMode spectralIndex stage) : ℂ)

/-- Missing exact equality is fatal for global correspondence. -/
theorem
    G8CanonicalXiSpectralCoordinateExactEqualityMissing.refutesCorrespondenceSource
    (w : G8CanonicalXiSpectralCoordinateExactEqualityMissing)
    (source : G8CanonicalXiSpectralModeCorrespondenceSource) :
    False := by
  let cert := source.certificate w.z
  exact
    w.noCoordinateEquality cert.spectralIndex cert.stage
      cert.canonicalValue_eq_coordinateMode

/-- Boundedness of the coordinate mode alone does not replace the exact
    eigenvalue equality. -/
structure G8CanonicalXiSpectralCoordinateBoundedOnly where
  z : G8ActualXiNonzeroHeightCarrier
  spectralIndex : Tau.Denotation.TauIdx
  stage : Tau.Denotation.TauIdx
  modeBounded :
    g8CanonicalXiSpectralCoordinateMode spectralIndex stage ≤ stage
  noExactEquality :
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
      (Tau.BookIII.Doors.lemniscate_eigenvalue
        (g8CanonicalXiSpectralCoordinateMode spectralIndex stage) : ℂ)

/-- Bounded mode data plus missing equality refutes a certificate using that
    same coordinate. -/
theorem
    G8CanonicalXiSpectralCoordinateBoundedOnly.refutesSameCoordinateCertificate
    (w : G8CanonicalXiSpectralCoordinateBoundedOnly)
    (cert :
      G8CanonicalXiSpectralModeCorrespondenceCertificate w.z)
    (hIndex : cert.spectralIndex = w.spectralIndex)
    (hStage : cert.stage = w.stage) :
    False := by
  apply w.noExactEquality
  simpa [hIndex, hStage] using cert.canonicalValue_eq_coordinateMode

end Tau.BookIII.Bridge
