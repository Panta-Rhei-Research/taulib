import TauLib.BookIII.Bridge.G8LemniscateStandardEigenvalueSpectrumSource

/-!
# TauLib.BookIII.Bridge.G8CanonicalXiSpectralModeMembership

Pointwise mode-membership surface for the remaining Lane-A nonzero-height
spectral correspondence theorem.

The standard lemniscate source has already reduced real-valuedness to exact
membership in the Book III eigenvalue ladder:

```text
canonical iota_tau^2 scaled xi value = lemniscate_eigenvalue n.
```

This module packages that as a pointwise certificate and proves it is exactly
the same data as the existing standard-eigenvalue membership/index source.  It
does not construct the mode from finite checks, accepted coverage, O3, divisor
transfer, or any RH-facing downstream handoff.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- POINTWISE MODE CERTIFICATES
-- ============================================================

/-- A pointwise exact mode certificate for the canonical scaled actual-`xi`
    value.

The load-bearing field is exact equality with the native Book III eigenvalue
`lemniscate_eigenvalue mode`; this is stronger than approximate evidence,
axis-offset data, or finite diagnostic checks. -/
structure G8CanonicalXiSpectralModeCertificate
    (z : G8ActualXiNonzeroHeightCarrier) where
  mode : Nat
  canonicalValue_eq_mode :
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z =
      (Tau.BookIII.Doors.lemniscate_eigenvalue mode : ℂ)
  diagnostics : G8LemniscateSpectrumRealityDiagnostics :=
    g8StandardLemniscateSpectrumRealityDiagnostics

/-- Pointwise mode membership for the canonical scaled actual-`xi` value. -/
def G8CanonicalXiSpectralModeMembership
    (z : G8ActualXiNonzeroHeightCarrier) : Prop :=
  Nonempty (G8CanonicalXiSpectralModeCertificate z)

/-- Global mode membership: every actual nonzero-height carrier has an exact
    standard lemniscate mode. -/
def G8CanonicalXiSpectralModeMembershipAll : Prop :=
  ∀ z : G8ActualXiNonzeroHeightCarrier,
    G8CanonicalXiSpectralModeMembership z

/-- A proof-facing source package for global canonical mode membership. -/
structure G8CanonicalXiSpectralModeMembershipSource where
  certificate :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      G8CanonicalXiSpectralModeCertificate z
  diagnostics : G8LemniscateSpectrumRealityDiagnostics :=
    g8StandardLemniscateSpectrumRealityDiagnostics

/-- A source package supplies global pointwise mode membership. -/
theorem G8CanonicalXiSpectralModeMembershipSource.membershipAll
    (source : G8CanonicalXiSpectralModeMembershipSource) :
    G8CanonicalXiSpectralModeMembershipAll := by
  intro z
  exact ⟨source.certificate z⟩

-- ============================================================
-- EQUIVALENCE WITH STANDARD EIGENVALUE MEMBERSHIP
-- ============================================================

/-- A pointwise mode certificate is exactly the standard eigenvalue-spectrum
    membership assertion for the canonical scaled value. -/
theorem g8CanonicalXiSpectralModeMembership_iff_standardEigenvalueMember
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (z : G8ActualXiNonzeroHeightCarrier) :
    G8CanonicalXiSpectralModeMembership z ↔
      G8StandardLemniscateEigenvalueSpectrum
        operatorCtx operatorReady
        (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.mode, cert.canonicalValue_eq_mode⟩
  · intro h
    rcases h with ⟨mode, hEq⟩
    exact
      ⟨{ mode := mode
         canonicalValue_eq_mode := hEq }⟩

/-- Global mode membership is equivalent to the existing standard-eigenvalue
    membership target. -/
theorem g8CanonicalXiSpectralModeMembershipAll_iff_standardMembershipTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx} :
    G8CanonicalXiSpectralModeMembershipAll ↔
      G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
        operatorCtx operatorReady := by
  constructor
  · intro hAll z
    exact
      (g8CanonicalXiSpectralModeMembership_iff_standardEigenvalueMember
        (operatorCtx := operatorCtx)
        (operatorReady := operatorReady)
        z).mp (hAll z)
  · intro hTarget z
    exact
      (g8CanonicalXiSpectralModeMembership_iff_standardEigenvalueMember
        (operatorCtx := operatorCtx)
        (operatorReady := operatorReady)
        z).mpr (hTarget z)

-- ============================================================
-- ADAPTERS TO THE EXISTING INDEX SOURCE
-- ============================================================

/-- A pointwise mode-membership source builds the existing function-valued
    standard eigenvalue index source. -/
def G8CanonicalXiSpectralModeMembershipSource.toStandardEigenvalueIndexSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source : G8CanonicalXiSpectralModeMembershipSource) :
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
      operatorCtx operatorReady where
  modeOf := fun z => (source.certificate z).mode
  canonicalValue_eq_eigenvalue :=
    fun z => (source.certificate z).canonicalValue_eq_mode
  diagnostics := source.diagnostics

/-- A global membership theorem builds the existing index source by classical
    choice.  This is a packaging adapter only; the mathematical content remains
    the pointwise certificate. -/
def g8CanonicalXiSpectralModeMembershipAll_toStandardEigenvalueIndexSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (hAll : G8CanonicalXiSpectralModeMembershipAll) :
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
      operatorCtx operatorReady where
  modeOf := fun z =>
    (Classical.choice (hAll z)).mode
  canonicalValue_eq_eigenvalue := fun z =>
    (Classical.choice (hAll z)).canonicalValue_eq_mode
  diagnostics := g8StandardLemniscateSpectrumRealityDiagnostics

/-- The existing index source is equivalent to global pointwise mode
    membership. -/
theorem
    g8CanonicalXiSpectralModeMembershipAll_iff_standardEigenvalueIndexSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx} :
    G8CanonicalXiSpectralModeMembershipAll ↔
      Nonempty
        (G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
          operatorCtx operatorReady) := by
  constructor
  · intro hAll
    exact
      ⟨g8CanonicalXiSpectralModeMembershipAll_toStandardEigenvalueIndexSource
        (operatorCtx := operatorCtx)
        (operatorReady := operatorReady)
        hAll⟩
  · intro hSource z
    rcases hSource with ⟨source⟩
    exact
      ⟨{ mode := source.modeOf z
         canonicalValue_eq_mode :=
          source.canonicalValue_eq_eigenvalue z
         diagnostics := source.diagnostics }⟩

/-- A mode-membership source supplies nonzero-height spectral-parameter
    reality through the standard eigenvalue corridor. -/
theorem G8CanonicalXiSpectralModeMembershipSource.toSpectralParameterReal
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source : G8CanonicalXiSpectralModeMembershipSource) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  (source.toStandardEigenvalueIndexSource
    (operatorCtx := operatorCtx)
    (operatorReady := operatorReady)).toSpectralParameterReal

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A carrier with no exact standard mode refutes pointwise mode membership. -/
structure G8CanonicalXiSpectralModeMissing
    (z : G8ActualXiNonzeroHeightCarrier) where
  noMode :
    ∀ mode : Nat,
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
        (Tau.BookIII.Doors.lemniscate_eigenvalue mode : ℂ)

/-- Missing exact mode membership is fatal for the pointwise certificate. -/
theorem G8CanonicalXiSpectralModeMissing.refutesMembership
    {z : G8ActualXiNonzeroHeightCarrier}
    (w : G8CanonicalXiSpectralModeMissing z)
    (hMember : G8CanonicalXiSpectralModeMembership z) :
    False := by
  rcases hMember with ⟨cert⟩
  exact w.noMode cert.mode cert.canonicalValue_eq_mode

/-- A single missing mode refutes global mode membership. -/
theorem G8CanonicalXiSpectralModeMissing.refutesMembershipAll
    {z : G8ActualXiNonzeroHeightCarrier}
    (w : G8CanonicalXiSpectralModeMissing z)
    (hAll : G8CanonicalXiSpectralModeMembershipAll) :
    False :=
  w.refutesMembership (hAll z)

/-- A claimed certificate with the wrong exact image equality is refuted by the
    equality field of the certificate itself. -/
structure G8CanonicalXiSpectralModeWrongImage
    (z : G8ActualXiNonzeroHeightCarrier) where
  certificate : G8CanonicalXiSpectralModeCertificate z
  mismatch :
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
      (Tau.BookIII.Doors.lemniscate_eigenvalue certificate.mode : ℂ)

/-- Wrong exact image equality is impossible for an actual mode certificate. -/
theorem G8CanonicalXiSpectralModeWrongImage.refutes
    {z : G8ActualXiNonzeroHeightCarrier}
    (w : G8CanonicalXiSpectralModeWrongImage z) :
    False :=
  w.mismatch w.certificate.canonicalValue_eq_mode

/-- Finite lemniscate diagnostics without a pointwise mode do not supply global
    canonical mode membership. -/
structure G8CanonicalXiSpectralModeDiagnosticsOnly where
  z : G8ActualXiNonzeroHeightCarrier
  finiteSelfAdjointDiagnostic :
    Tau.BookIII.Doors.self_adjoint_check 20 = true
  finiteK5DiagonalDiagnostic :
    Tau.BookIII.Doors.k5_diagonal_check 20 = true
  finiteSpectralCorrespondenceDiagnostic : True
  noMode :
    ∀ mode : Nat,
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
        (Tau.BookIII.Doors.lemniscate_eigenvalue mode : ℂ)

/-- Diagnostics-only evidence plus no exact mode refutes global mode
    membership. -/
theorem G8CanonicalXiSpectralModeDiagnosticsOnly.refutesMembershipAll
    (w : G8CanonicalXiSpectralModeDiagnosticsOnly)
    (hAll : G8CanonicalXiSpectralModeMembershipAll) :
    False :=
  (G8CanonicalXiSpectralModeMissing.mk w.noMode).refutesMembershipAll hAll

end Tau.BookIII.Bridge
