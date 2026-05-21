import TauLib.BookIII.Bridge.G8LemniscateSelfAdjointSpectrumReality

/-!
# TauLib.BookIII.Bridge.G8LemniscateStandardEigenvalueSpectrumSource

Theorem-backed standard eigenvalue spectrum source for the Lane-A lemniscate
operator route.

The previous layer made the self-adjoint spectrum theorem generic:

```text
spectral member -> imaginary part zero.
```

This module instantiates that generic theorem for the native Book III
lemniscate eigenvalue readout `lambda_n = n^2`.  The actual `xi` payload is kept
separate: one must still prove that the canonical `iota_tau^2` scaled actual
`xi` value is one of these standard lemniscate eigenvalues, with an exact mode
index.  Finite operator checks remain diagnostics, not membership proofs.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- STANDARD LEMNISCATE EIGENVALUE SPECTRUM
-- ============================================================

/-- The standard Book III lemniscate eigenvalue spectrum, read as complex
    spectral values. -/
def G8StandardLemniscateEigenvalueSpectrum
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) :
    G8LemniscateSpectrumMembership operatorCtx operatorReady :=
  fun spectralValue =>
    ∃ n : Nat,
      spectralValue =
        (Tau.BookIII.Doors.lemniscate_eigenvalue n : ℂ)

/-- Every standard lemniscate eigenvalue has zero imaginary coordinate after
    complex readout. -/
theorem g8StandardLemniscateEigenvalueSpectrum_real
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (spectralValue : ℂ)
    (hMember :
      G8StandardLemniscateEigenvalueSpectrum
        operatorCtx operatorReady spectralValue) :
    spectralValue.im = 0 := by
  rcases hMember with ⟨n, rfl⟩
  simp [Tau.BookIII.Doors.lemniscate_eigenvalue]

/-- The standard finite Book III lemniscate checks, recorded only as diagnostic
    propositions for this source. -/
def g8StandardLemniscateSpectrumRealityDiagnostics :
    G8LemniscateSpectrumRealityDiagnostics where
  finiteSelfAdjointDiagnostic :=
    Tau.BookIII.Doors.self_adjoint_check 20 = true
  finiteK5DiagonalDiagnostic :=
    Tau.BookIII.Doors.k5_diagonal_check 20 = true
  finiteSpectralCorrespondenceDiagnostic := True
  status := .conditional_interface

/-- The theorem-backed generic self-adjoint reality source for the standard
    Book III lemniscate eigenvalue spectrum. -/
def g8StandardLemniscateSelfAdjointSpectrumRealitySource
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) :
    G8LemniscateSelfAdjointSpectrumRealitySource
      operatorCtx operatorReady where
  spectralMembership :=
    G8StandardLemniscateEigenvalueSpectrum operatorCtx operatorReady
  selfAdjointSpectrumReality :=
    g8StandardLemniscateEigenvalueSpectrum_real
  diagnostics := g8StandardLemniscateSpectrumRealityDiagnostics

-- ============================================================
-- CANONICAL XI MEMBERSHIP TARGET
-- ============================================================

/-- The exact remaining actual-`xi` membership target for the standard
    lemniscate eigenvalue spectrum. -/
def G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) : Prop :=
  G8ActualXiIotaTauCanonicalLemniscateSpectralMembershipTarget
    (g8StandardLemniscateSelfAdjointSpectrumRealitySource
      operatorCtx operatorReady)

/-- A proof-facing index source for actual canonical values in the standard
    lemniscate eigenvalue spectrum.

The load-bearing field is exact equality with a Book III eigenvalue, not a
finite check and not approximate spectral evidence. -/
structure G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
    (_operatorCtx : LemniscateOperatorContext)
    (_operatorReady : LemniscateOperatorReady _operatorCtx) where
  modeOf : G8ActualXiNonzeroHeightCarrier → Nat
  canonicalValue_eq_eigenvalue :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z =
        (Tau.BookIII.Doors.lemniscate_eigenvalue (modeOf z) : ℂ)
  diagnostics : G8LemniscateSpectrumRealityDiagnostics :=
    g8StandardLemniscateSpectrumRealityDiagnostics

/-- A mode-index source proves canonical membership in the standard eigenvalue
    spectrum. -/
theorem
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource.toMembershipTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
        operatorCtx operatorReady) :
    G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
      operatorCtx operatorReady := by
  intro z
  exact ⟨source.modeOf z, source.canonicalValue_eq_eigenvalue z⟩

/-- Standard eigenvalue membership plus the theorem-backed standard spectrum
    reality source instantiates the canonical self-adjoint source. -/
def
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource.toCanonicalSelfAdjointSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
        operatorCtx operatorReady) :
    G8ActualXiIotaTauCanonicalSelfAdjointRealitySource
      operatorCtx operatorReady :=
  (g8StandardLemniscateSelfAdjointSpectrumRealitySource
    operatorCtx operatorReady).toCanonicalSelfAdjointSource
      source.toMembershipTarget

/-- A standard eigenvalue index source supplies the nonzero-height spectral
    parameter reality payload. -/
theorem
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource.toSpectralParameterReal
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
        operatorCtx operatorReady) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  source.toCanonicalSelfAdjointSource.toSpectralParameterReal

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A canonical value that is not any standard lemniscate eigenvalue refutes the
    standard membership target. -/
structure G8ActualXiIotaTauCanonicalNotStandardEigenvalue
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  z : G8ActualXiNonzeroHeightCarrier
  notEigenvalue :
    ∀ n : Nat,
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
        (Tau.BookIII.Doors.lemniscate_eigenvalue n : ℂ)

/-- A non-eigenvalue canonical value is fatal for the standard membership
    target. -/
theorem G8ActualXiIotaTauCanonicalNotStandardEigenvalue.refutesMembershipTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8ActualXiIotaTauCanonicalNotStandardEigenvalue
        operatorCtx operatorReady)
    (membership :
      G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
        operatorCtx operatorReady) :
    False := by
  rcases membership w.z with ⟨n, hEq⟩
  exact w.notEigenvalue n hEq

/-- A claimed standard eigenvalue with nonzero imaginary coordinate is impossible. -/
structure G8StandardLemniscateEigenvalueNonrealAttempt
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  spectralValue : ℂ
  member :
    G8StandardLemniscateEigenvalueSpectrum
      operatorCtx operatorReady spectralValue
  nonreal : spectralValue.im ≠ 0

/-- The standard eigenvalue spectrum itself refutes non-real members. -/
theorem G8StandardLemniscateEigenvalueNonrealAttempt.refutes
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8StandardLemniscateEigenvalueNonrealAttempt
        operatorCtx operatorReady) :
    False :=
  w.nonreal
    (g8StandardLemniscateEigenvalueSpectrum_real
      w.spectralValue w.member)

/-- Finite diagnostics cannot replace the exact mode-index equality needed for
    canonical actual-`xi` membership in the standard spectrum. -/
structure G8StandardLemniscateFiniteDiagnosticsMissingMode where
  z : G8ActualXiNonzeroHeightCarrier
  finiteSelfAdjointDiagnostic :
    Tau.BookIII.Doors.self_adjoint_check 20 = true
  finiteK5DiagonalDiagnostic :
    Tau.BookIII.Doors.k5_diagonal_check 20 = true
  finiteSpectralCorrespondenceDiagnostic : True
  noMode :
    ∀ n : Nat,
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
        (Tau.BookIII.Doors.lemniscate_eigenvalue n : ℂ)

/-- Diagnostics plus no exact mode still refute standard membership. -/
theorem G8StandardLemniscateFiniteDiagnosticsMissingMode.refutesMembershipTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w : G8StandardLemniscateFiniteDiagnosticsMissingMode)
    (membership :
      G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
        operatorCtx operatorReady) :
    False := by
  rcases membership w.z with ⟨n, hEq⟩
  exact w.noMode n hEq

end Tau.BookIII.Bridge
