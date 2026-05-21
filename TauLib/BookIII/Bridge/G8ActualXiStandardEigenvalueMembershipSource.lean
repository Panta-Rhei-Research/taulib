import TauLib.BookIII.Bridge.G8BookIIILemniscateSpectralCoordinateReadout
import TauLib.BookIII.Doors.SpectralDecomp

/-!
# TauLib.BookIII.Bridge.G8ActualXiStandardEigenvalueMembershipSource

Proof-facing source layer for the remaining actual-`xi` standard-eigenvalue
membership theorem.

The coordinate readout layer proved that Book III finite coordinates add no
extra mathematical strength beyond exact standard lemniscate eigenvalue
membership.  This module therefore names the bare metal payload:

```text
actual nonzero-height xi carrier
  -> standard lemniscate mode n
  -> canonical iota_tau^2 scaled value = lemniscate_eigenvalue n.
```

Finite projector, spectral-resolution, finite-correspondence, and
self-adjoint checks remain diagnostic evidence only.  They are intentionally
not promoted into global actual-`xi` spectral membership.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- DIAGNOSTICS
-- ============================================================

/-- Non-load-bearing Book III diagnostics attached to a claimed standard
    eigenvalue mode for an actual `xi` carrier. -/
structure G8ActualXiCanonicalStandardEigenvalueDiagnostics where
  spectralProjectorDiagnostic : Prop := True
  spectralResolutionDiagnostic : Prop := True
  finiteCorrespondenceDiagnostic : Prop := True
  selfAdjointDiagnostic : Prop := True

/-- The standard finite diagnostic propositions attached to a mode.  These
    propositions record finite scaffolding only; they are not consumed as a
    proof of exact actual-`xi` spectral membership. -/
def g8ActualXiCanonicalStandardEigenvalueDiagnostics
    (mode : Nat) :
    G8ActualXiCanonicalStandardEigenvalueDiagnostics where
  spectralProjectorDiagnostic :=
    Tau.BookIII.Doors.projector_check (mode + 1) = true
  spectralResolutionDiagnostic :=
    Tau.BookIII.Doors.spectral_resolution_check (mode + 1) = true
  finiteCorrespondenceDiagnostic :=
    Tau.BookIII.Doors.spectral_correspondence_finite (mode + 1) = true
  selfAdjointDiagnostic :=
    Tau.BookIII.Doors.self_adjoint_check (mode + 1) = true

-- ============================================================
-- POINTWISE CERTIFICATE
-- ============================================================

/-- Pointwise certificate that the canonical `iota_tau^2` scaled actual-`xi`
    value is exactly a standard Book III lemniscate eigenvalue.

The equality field is the load-bearing theorem payload.  The diagnostics field
records finite operator evidence without using it to prove membership. -/
structure G8ActualXiCanonicalStandardEigenvalueMembershipCertificate
    (z : G8ActualXiNonzeroHeightCarrier) where
  mode : Nat
  canonicalValue_eq_eigenvalue :
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z =
      (Tau.BookIII.Doors.lemniscate_eigenvalue mode : ℂ)
  diagnostics : G8ActualXiCanonicalStandardEigenvalueDiagnostics :=
    g8ActualXiCanonicalStandardEigenvalueDiagnostics mode

/-- A pointwise standard-eigenvalue certificate gives the standard membership
    witness for the carrier. -/
theorem
    G8ActualXiCanonicalStandardEigenvalueMembershipCertificate.toMembership
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {z : G8ActualXiNonzeroHeightCarrier}
    (cert :
      G8ActualXiCanonicalStandardEigenvalueMembershipCertificate z) :
    G8StandardLemniscateEigenvalueSpectrum
      operatorCtx operatorReady
      (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z) := by
  exact ⟨cert.mode, cert.canonicalValue_eq_eigenvalue⟩

/-- A pointwise standard-eigenvalue certificate converts to the existing
    canonical mode certificate. -/
def
    G8ActualXiCanonicalStandardEigenvalueMembershipCertificate.toModeCertificate
    {z : G8ActualXiNonzeroHeightCarrier}
    (cert :
      G8ActualXiCanonicalStandardEigenvalueMembershipCertificate z) :
    G8CanonicalXiSpectralModeCertificate z where
  mode := cert.mode
  canonicalValue_eq_mode := cert.canonicalValue_eq_eigenvalue
  diagnostics := g8StandardLemniscateSpectrumRealityDiagnostics

-- ============================================================
-- THEOREM-TARGET SPLIT
-- ============================================================

/-- Mode extraction target: choose the standard lemniscate mode attached to each
    actual nonzero-height carrier. -/
abbrev G8ActualXiCanonicalModeExtractionTarget : Type 2 :=
  G8ActualXiNonzeroHeightCarrier → Nat

/-- Alignment target for a selected standard mode function.  This is the exact
    equality theorem; it is not a finite diagnostic or approximation. -/
def G8ActualXiCanonicalModeEigenvalueAlignmentTarget
    (modeOf : G8ActualXiCanonicalModeExtractionTarget) : Prop :=
  ∀ z : G8ActualXiNonzeroHeightCarrier,
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z =
      (Tau.BookIII.Doors.lemniscate_eigenvalue (modeOf z) : ℂ)

-- ============================================================
-- GLOBAL SOURCE AND ADAPTERS
-- ============================================================

/-- Global proof-facing source for exact actual-`xi` standard eigenvalue
    membership. -/
structure G8ActualXiCanonicalStandardEigenvalueMembershipSource
    (_operatorCtx : LemniscateOperatorContext)
    (_operatorReady : LemniscateOperatorReady _operatorCtx) where
  certificateOf :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      G8ActualXiCanonicalStandardEigenvalueMembershipCertificate z
  diagnostics : G8ActualXiCanonicalStandardEigenvalueDiagnostics := {}

/-- The global source induces the selected mode function. -/
def G8ActualXiCanonicalStandardEigenvalueMembershipSource.modeOf
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSource
        operatorCtx operatorReady) :
    G8ActualXiCanonicalModeExtractionTarget :=
  fun z => (source.certificateOf z).mode

/-- The global source satisfies the exact eigenvalue-alignment target for its
    selected modes. -/
theorem
    G8ActualXiCanonicalStandardEigenvalueMembershipSource.modeAlignment
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSource
        operatorCtx operatorReady) :
    G8ActualXiCanonicalModeEigenvalueAlignmentTarget source.modeOf := by
  intro z
  exact (source.certificateOf z).canonicalValue_eq_eigenvalue

/-- A mode extraction plus exact eigenvalue alignment packages the global
    standard-eigenvalue membership source. -/
def
    g8ActualXiCanonicalStandardEigenvalueMembershipSource_ofModeTargets
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx)
    (modeOf : G8ActualXiCanonicalModeExtractionTarget)
    (alignment :
      G8ActualXiCanonicalModeEigenvalueAlignmentTarget modeOf) :
    G8ActualXiCanonicalStandardEigenvalueMembershipSource
      operatorCtx operatorReady where
  certificateOf := fun z =>
    { mode := modeOf z
      canonicalValue_eq_eigenvalue := alignment z }

/-- The global source builds the existing standard eigenvalue index source. -/
def
    G8ActualXiCanonicalStandardEigenvalueMembershipSource.toStandardEigenvalueIndexSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSource
        operatorCtx operatorReady) :
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
      operatorCtx operatorReady where
  modeOf := source.modeOf
  canonicalValue_eq_eigenvalue := source.modeAlignment
  diagnostics := g8StandardLemniscateSpectrumRealityDiagnostics

/-- The global source proves the standard eigenvalue membership target. -/
theorem
    G8ActualXiCanonicalStandardEigenvalueMembershipSource.toMembershipTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSource
        operatorCtx operatorReady) :
    G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
      operatorCtx operatorReady :=
  source.toStandardEigenvalueIndexSource.toMembershipTarget

/-- The global source builds the coordinate realization source through the
    already-closed self-stage readout. -/
def
    G8ActualXiCanonicalStandardEigenvalueMembershipSource.toCoordinateRealizationSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSource
        operatorCtx operatorReady) :
    G8BookIIILemniscateSpectralCoordinateRealizationSource :=
  source.toStandardEigenvalueIndexSource.toCoordinateRealizationSource

/-- The global source builds the coordinate correspondence source. -/
def
    G8ActualXiCanonicalStandardEigenvalueMembershipSource.toCoordinateCorrespondenceSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSource
        operatorCtx operatorReady) :
    G8CanonicalXiSpectralModeCorrespondenceSource :=
  source.toStandardEigenvalueIndexSource.toCoordinateCorrespondenceSource

/-- The global source supplies the nonzero-height spectral-parameter reality
    payload through the standard eigenvalue corridor. -/
theorem
    G8ActualXiCanonicalStandardEigenvalueMembershipSource.toSpectralParameterReal
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSource
        operatorCtx operatorReady) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  source.toStandardEigenvalueIndexSource.toSpectralParameterReal_viaCoordinateReadout

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- Finite spectral diagnostics at a mode do not construct a certificate when
    exact equality with the standard eigenvalue is absent. -/
structure G8ActualXiStandardEigenvalueFiniteDiagnosticsOnly
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  z : G8ActualXiNonzeroHeightCarrier
  mode : Nat
  spectralProjectorDiagnostic :
    Tau.BookIII.Doors.projector_check (mode + 1) = true
  spectralResolutionDiagnostic :
    Tau.BookIII.Doors.spectral_resolution_check (mode + 1) = true
  finiteCorrespondenceDiagnostic :
    Tau.BookIII.Doors.spectral_correspondence_finite (mode + 1) = true
  selfAdjointDiagnostic :
    Tau.BookIII.Doors.self_adjoint_check (mode + 1) = true
  noExactEquality :
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
      (Tau.BookIII.Doors.lemniscate_eigenvalue mode : ℂ)

/-- Diagnostics-only data refutes a certificate that claims the same mode. -/
theorem
    G8ActualXiStandardEigenvalueFiniteDiagnosticsOnly.refutesSameModeCertificate
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8ActualXiStandardEigenvalueFiniteDiagnosticsOnly
        operatorCtx operatorReady)
    (cert :
      G8ActualXiCanonicalStandardEigenvalueMembershipCertificate w.z)
    (hMode : cert.mode = w.mode) :
    False := by
  apply w.noExactEquality
  simpa [hMode] using cert.canonicalValue_eq_eigenvalue

/-- A claimed mode different from the certificate mode refutes that claim. -/
structure G8ActualXiStandardEigenvalueWrongMode
    (z : G8ActualXiNonzeroHeightCarrier) where
  certificate :
    G8ActualXiCanonicalStandardEigenvalueMembershipCertificate z
  claimedMode : Nat
  wrongMode : claimedMode ≠ certificate.mode

/-- The certificate's selected mode is the only mode extracted by this source
    layer. -/
theorem G8ActualXiStandardEigenvalueWrongMode.refutesClaimedMode
    {z : G8ActualXiNonzeroHeightCarrier}
    (w : G8ActualXiStandardEigenvalueWrongMode z)
    (hClaimed : w.claimedMode = w.certificate.mode) :
    False :=
  w.wrongMode hClaimed

/-- A carrier with no exact standard eigenvalue mode refutes the global source. -/
structure G8ActualXiStandardEigenvalueExactMembershipMissing where
  z : G8ActualXiNonzeroHeightCarrier
  noExactMode :
    ∀ mode : Nat,
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
        (Tau.BookIII.Doors.lemniscate_eigenvalue mode : ℂ)

/-- Missing exact equality is fatal for the global standard-membership source. -/
theorem
    G8ActualXiStandardEigenvalueExactMembershipMissing.refutesSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w : G8ActualXiStandardEigenvalueExactMembershipMissing)
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSource
        operatorCtx operatorReady) :
    False := by
  let cert := source.certificateOf w.z
  exact w.noExactMode cert.mode cert.canonicalValue_eq_eigenvalue

/-- Approximate or external evidence for a mode is not exact membership. -/
structure G8ActualXiStandardEigenvalueApproximateOnly
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  z : G8ActualXiNonzeroHeightCarrier
  approximateMode : Nat
  approximateEvidence : Prop
  evidenceHolds : approximateEvidence
  noExactMode :
    ∀ mode : Nat,
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
        (Tau.BookIII.Doors.lemniscate_eigenvalue mode : ℂ)

/-- Approximate mode evidence is refuted by any global exact-membership source
    for the same carrier. -/
theorem
    G8ActualXiStandardEigenvalueApproximateOnly.refutesSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8ActualXiStandardEigenvalueApproximateOnly
        operatorCtx operatorReady)
    (source :
      G8ActualXiCanonicalStandardEigenvalueMembershipSource
        operatorCtx operatorReady) :
    False := by
  let cert := source.certificateOf w.z
  exact w.noExactMode cert.mode cert.canonicalValue_eq_eigenvalue

end Tau.BookIII.Bridge
