import TauLib.BookIII.Bridge.G8BookIIILemniscateSpectralCoordinateRealization

/-!
# TauLib.BookIII.Bridge.G8BookIIILemniscateSpectralCoordinateReadout

Pure finite-coordinate readout split for the Lane-A Book III spectral
coordinate target.

The previous layer named the exact coordinate-realization theorem:

```text
canonical iota_tau^2 scaled xi value
  = lemniscate_eigenvalue (spectral_parameter spectralIndex stage).
```

This module closes the plumbing around the finite coordinate system.  Every
standard lemniscate eigenvalue mode `n` is represented by the coordinate
`spectral_parameter n n`.  Therefore the coordinate-realization target is
equivalent to the standard-eigenvalue membership target.  The latter remains
the real mathematical payload.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- PURE COORDINATE READOUT ALGEBRA
-- ============================================================

/-- The finite Book III coordinate readout represents mode `n` at its own
stage. -/
theorem g8CanonicalXiSpectralCoordinateMode_self_stage
    (n : Tau.Denotation.TauIdx) :
    g8CanonicalXiSpectralCoordinateMode n n = n := by
  by_cases h : n = 0
  · subst n
    simp [g8CanonicalXiSpectralCoordinateMode,
      Tau.BookIII.Doors.spectral_parameter]
  · have hlt : n < n + 1 := Nat.lt_succ_self n
    simp [g8CanonicalXiSpectralCoordinateMode,
      Tau.BookIII.Doors.spectral_parameter, h,
      Nat.mod_eq_of_lt hlt]

/-- Exact equality with a standard eigenvalue at mode `n` gives exact equality
with the finite coordinate readout at `(n,n)`. -/
theorem
    g8CanonicalValue_eq_coordinateMode_of_eq_standardEigenvalue
    {z : G8ActualXiNonzeroHeightCarrier}
    {n : Tau.Denotation.TauIdx}
    (hEq :
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z =
        (Tau.BookIII.Doors.lemniscate_eigenvalue n : ℂ)) :
    g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z =
      (Tau.BookIII.Doors.lemniscate_eigenvalue
        (g8CanonicalXiSpectralCoordinateMode n n) : ℂ) := by
  simpa [g8CanonicalXiSpectralCoordinateMode_self_stage] using hEq

-- ============================================================
-- EQUIVALENCE WITH STANDARD EIGENVALUE MEMBERSHIP
-- ============================================================

/-- Standard eigenvalue membership supplies the pure coordinate-realization
target.  This is only coordinate algebra; the membership theorem itself remains
the payload. -/
theorem
    g8BookIIILemniscateSpectralCoordinateRealizationTarget_ofStandardMembership
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (membership :
      G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
        operatorCtx operatorReady) :
    G8BookIIILemniscateSpectralCoordinateRealizationTarget := by
  intro z
  rcases membership z with ⟨n, hEq⟩
  exact
    ⟨n, n,
      g8CanonicalValue_eq_coordinateMode_of_eq_standardEigenvalue hEq⟩

/-- A coordinate-realization target supplies standard eigenvalue membership by
forgetting the coordinate decomposition and retaining the computed mode. -/
theorem
    g8StandardMembership_ofBookIIILemniscateSpectralCoordinateRealizationTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (target : G8BookIIILemniscateSpectralCoordinateRealizationTarget) :
    G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
      operatorCtx operatorReady := by
  intro z
  rcases target z with ⟨spectralIndex, stage, hEq⟩
  exact
    ⟨g8CanonicalXiSpectralCoordinateMode spectralIndex stage, hEq⟩

/-- The coordinate-realization target is exactly the standard-eigenvalue
membership target. -/
theorem
    g8BookIIILemniscateSpectralCoordinateRealizationTarget_iff_standardMembership
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx} :
    G8BookIIILemniscateSpectralCoordinateRealizationTarget ↔
      G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
        operatorCtx operatorReady := by
  constructor
  · exact
      g8StandardMembership_ofBookIIILemniscateSpectralCoordinateRealizationTarget
        (operatorCtx := operatorCtx)
        (operatorReady := operatorReady)
  · exact
      g8BookIIILemniscateSpectralCoordinateRealizationTarget_ofStandardMembership
        (operatorCtx := operatorCtx)
        (operatorReady := operatorReady)

-- ============================================================
-- PACKAGE ADAPTERS
-- ============================================================

/-- A standard eigenvalue index source builds the Book III coordinate
realization source by choosing the self-stage coordinate `(mode, mode)`. -/
def
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource.toCoordinateRealizationSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
        operatorCtx operatorReady) :
    G8BookIIILemniscateSpectralCoordinateRealizationSource where
  operatorCtx := operatorCtx
  operatorReady := operatorReady
  spectralIndexOf := source.modeOf
  stageOf := source.modeOf
  canonicalValue_eq_coordinateMode := fun z =>
    g8CanonicalValue_eq_coordinateMode_of_eq_standardEigenvalue
      (source.canonicalValue_eq_eigenvalue z)
  diagnostics := {}

/-- A standard eigenvalue index source supplies the coordinate correspondence
source through the realization package. -/
def
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource.toCoordinateCorrespondenceSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
        operatorCtx operatorReady) :
    G8CanonicalXiSpectralModeCorrespondenceSource :=
  source.toCoordinateRealizationSource.toCorrespondenceSource

/-- A standard eigenvalue index source supplies the existing nonzero-height
spectral-parameter reality payload through the coordinate readout corridor. -/
theorem
    G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource.toSpectralParameterReal_viaCoordinateReadout
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiIotaTauCanonicalStandardEigenvalueIndexSource
        operatorCtx operatorReady) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  source.toCoordinateRealizationSource.toSpectralParameterReal

/-- A standard eigenvalue membership theorem can be packaged as a coordinate
realization source when an operator package is supplied. -/
def
    g8BookIIILemniscateSpectralCoordinateRealizationSource_ofStandardMembership
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx)
    (membership :
      G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
        operatorCtx operatorReady) :
    G8BookIIILemniscateSpectralCoordinateRealizationSource :=
  g8BookIIILemniscateSpectralCoordinateRealizationSource_ofTarget
    operatorCtx operatorReady
    (g8BookIIILemniscateSpectralCoordinateRealizationTarget_ofStandardMembership
      membership)

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A finite coordinate readout without standard eigenvalue membership does not
construct the actual canonical membership theorem. -/
structure G8BookIIILemniscateCoordinateReadoutWithoutStandardMembership
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  target : G8BookIIILemniscateSpectralCoordinateRealizationTarget
  noStandardMembership :
    ¬ G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
      operatorCtx operatorReady

/-- Coordinate realization and standard membership are equivalent, so a claimed
coordinate readout without standard membership is impossible. -/
theorem
    G8BookIIILemniscateCoordinateReadoutWithoutStandardMembership.refutes
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8BookIIILemniscateCoordinateReadoutWithoutStandardMembership
        operatorCtx operatorReady) :
    False :=
  w.noStandardMembership
    (g8StandardMembership_ofBookIIILemniscateSpectralCoordinateRealizationTarget
      (operatorCtx := operatorCtx)
      (operatorReady := operatorReady)
      w.target)

/-- Finite diagnostics and bounded coordinate data alone still do not supply
standard eigenvalue membership. -/
structure G8BookIIILemniscateFiniteCoordinateDiagnosticsOnly
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  z : G8ActualXiNonzeroHeightCarrier
  spectralIndex : Tau.Denotation.TauIdx
  stage : Tau.Denotation.TauIdx
  modeBounded :
    g8CanonicalXiSpectralCoordinateMode spectralIndex stage ≤ stage
  spectralParamDiagnostic :
    Tau.BookIII.Doors.spectral_param_check stage stage = true
  finiteCorrespondenceDiagnostic :
    Tau.BookIII.Doors.spectral_correspondence_finite stage = true
  eigenvalueNestingDiagnostic :
    Tau.BookIII.Doors.eigenvalue_nesting_check stage = true
  noStandardMode :
    ∀ n : Nat,
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
        (Tau.BookIII.Doors.lemniscate_eigenvalue n : ℂ)

/-- Diagnostics-only finite coordinate data is fatal to a claimed standard
membership theorem if the selected carrier has no exact standard mode. -/
theorem
    G8BookIIILemniscateFiniteCoordinateDiagnosticsOnly.refutesStandardMembership
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8BookIIILemniscateFiniteCoordinateDiagnosticsOnly
        operatorCtx operatorReady)
    (membership :
      G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
        operatorCtx operatorReady) :
    False := by
  rcases membership w.z with ⟨n, hEq⟩
  exact w.noStandardMode n hEq

/-- Exact equality to an eigenvalue mode is the required payload; approximate or
diagnostic evidence is not part of this coordinate-readout closure. -/
structure G8BookIIILemniscateApproximateCoordinateOnly
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  z : G8ActualXiNonzeroHeightCarrier
  approximateMode : Tau.Denotation.TauIdx
  approximateEvidence : Prop
  evidenceHolds : approximateEvidence
  noExactStandardMode :
    ∀ n : Nat,
      g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z ≠
        (Tau.BookIII.Doors.lemniscate_eigenvalue n : ℂ)

/-- Approximate coordinate evidence is refuted by any actual standard
membership theorem when exact equality is absent. -/
theorem
    G8BookIIILemniscateApproximateCoordinateOnly.refutesStandardMembership
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8BookIIILemniscateApproximateCoordinateOnly
        operatorCtx operatorReady)
    (membership :
      G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
        operatorCtx operatorReady) :
    False := by
  rcases membership w.z with ⟨n, hEq⟩
  exact w.noExactStandardMode n hEq

end Tau.BookIII.Bridge
