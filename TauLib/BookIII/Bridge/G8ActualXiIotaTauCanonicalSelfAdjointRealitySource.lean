import TauLib.BookIII.Bridge.G8ActualXiIotaTauScaledImageLawConstruction

/-!
# TauLib.BookIII.Bridge.G8ActualXiIotaTauCanonicalSelfAdjointRealitySource

Proof-facing source layer for the remaining canonical self-adjoint reality target.

The canonical scaled image law is already closed:

```text
z |-> iota_tau^2 * orthodoxXiCarrierCenteredQuadratic z.
```

This module splits the remaining Book III source theorem into two exact pieces:

* the canonical scaled value is a spectral member of the ready lemniscate
  operator package;
* self-adjoint spectral membership forces that canonical value to be real.

Finite self-adjoint/K5/correspondence checks remain diagnostics only.  This
module does not import O3, determinant transfer, accepted coverage, or any
RH-facing final handoff.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- CANONICAL SPECTRAL MEMBERSHIP
-- ============================================================

/-- Predicate family for saying that the canonical `iota_tau^2` scaled image of
    a nonzero-height carrier is a spectral value of a ready Book III lemniscate
    operator package. -/
def G8ActualXiIotaTauCanonicalScaledSpectralMembership
    (_operatorCtx : LemniscateOperatorContext)
    (_operatorReady : LemniscateOperatorReady _operatorCtx) : Type 2 :=
  G8ActualXiNonzeroHeightCarrier → Prop

/-- Source package for canonical scaled-value spectral membership.

The predicate is deliberately supplied as a field.  The current finite Book III
checks can support diagnostics, but they do not construct global membership for
the actual `xi` stream. -/
structure G8ActualXiIotaTauCanonicalScaledSpectralMembershipSource
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  spectralMembership :
    G8ActualXiIotaTauCanonicalScaledSpectralMembership
      operatorCtx operatorReady
  spectralMembership_holds :
    ∀ z : G8ActualXiNonzeroHeightCarrier, spectralMembership z
  diagnostics : G8ActualXiNonzeroHeightScaledOperatorDiagnostics := {}

-- ============================================================
-- SELF-ADJOINT SPECTRAL REALITY
-- ============================================================

/-- Source package for the self-adjoint-spectrum reality selector.

This is the exact theorem shape needed from the operator side: once the
canonical value is known to be in the self-adjoint spectrum, its imaginary part
vanishes. -/
structure G8ActualXiIotaTauCanonicalSelfAdjointSpectrumRealitySource
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx)
    (spectralMembership :
      G8ActualXiIotaTauCanonicalScaledSpectralMembership
        operatorCtx operatorReady) where
  selfAdjointSpectrumReality :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      spectralMembership z →
        (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z).im = 0
  diagnostics : G8ActualXiNonzeroHeightScaledOperatorDiagnostics := {}

-- ============================================================
-- COMBINED CANONICAL SOURCE
-- ============================================================

/-- Combined canonical self-adjoint reality source.

This is the next nonzero-height Lane-A theorem target in source-facing form:
membership of every canonical scaled value plus real-valuedness of spectral
members of the ready self-adjoint operator. -/
structure G8ActualXiIotaTauCanonicalSelfAdjointRealitySource
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  membershipSource :
    G8ActualXiIotaTauCanonicalScaledSpectralMembershipSource
      operatorCtx operatorReady
  realitySource :
    G8ActualXiIotaTauCanonicalSelfAdjointSpectrumRealitySource
      operatorCtx operatorReady membershipSource.spectralMembership

/-- The combined canonical source is exactly sufficient for the existing
    canonical self-adjoint reality target. -/
def G8ActualXiIotaTauCanonicalSelfAdjointRealitySource.toTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiIotaTauCanonicalSelfAdjointRealitySource
        operatorCtx operatorReady) :
    G8ActualXiIotaTauCanonicalSelfAdjointRealityTarget
      operatorCtx operatorReady where
  spectralMembership := source.membershipSource.spectralMembership
  spectralMembership_holds := source.membershipSource.spectralMembership_holds
  selfAdjointSpectralReality :=
    source.realitySource.selfAdjointSpectrumReality
  diagnostics := source.realitySource.diagnostics

/-- Canonical membership plus self-adjoint reality builds the combined Book III
    operator spectral-image source. -/
def G8ActualXiIotaTauCanonicalSelfAdjointRealitySource.toBookIIISource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiIotaTauCanonicalSelfAdjointRealitySource
        operatorCtx operatorReady) :
    G8ActualXiIotaTauBookIIIOperatorSpectralImageSource :=
  g8ActualXiIotaTauBookIIISource_ofCanonicalSelfAdjointReality
    source.toTarget

/-- The canonical source supplies the nonzero-height spectral-parameter reality
    payload through the already-closed scaled-image law. -/
theorem G8ActualXiIotaTauCanonicalSelfAdjointRealitySource.toSpectralParameterReal
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiIotaTauCanonicalSelfAdjointRealitySource
        operatorCtx operatorReady) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  g8ActualXiIotaTauSpectralParameterReal_ofCanonicalSelfAdjointReality
    source.toTarget

/-- The canonical source feeds the existing nonzero-height operator readout
    corridor. -/
def G8ActualXiIotaTauCanonicalSelfAdjointRealitySource.toOperatorReadoutContext
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiIotaTauCanonicalSelfAdjointRealitySource
        operatorCtx operatorReady) :
    G8ActualXiNonzeroHeightOperatorSpectralReadoutContext :=
  g8ActualXiIotaTauOperatorReadout_ofCanonicalSelfAdjointReality
    source.toTarget

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A pointwise failure of canonical spectral membership refutes a membership
    source. -/
structure G8ActualXiIotaTauCanonicalSpectralMembershipGap
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  z : G8ActualXiNonzeroHeightCarrier
  notSpectralMember :
    ∀ source :
      G8ActualXiIotaTauCanonicalScaledSpectralMembershipSource
        operatorCtx operatorReady,
      ¬ source.spectralMembership z

/-- A membership gap is fatal for a claimed membership source. -/
theorem G8ActualXiIotaTauCanonicalSpectralMembershipGap.refutesMembershipSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (gap :
      G8ActualXiIotaTauCanonicalSpectralMembershipGap
        operatorCtx operatorReady)
    (source :
      G8ActualXiIotaTauCanonicalScaledSpectralMembershipSource
        operatorCtx operatorReady) :
    False :=
  gap.notSpectralMember source (source.spectralMembership_holds gap.z)

/-- A non-real canonical value at a member point refutes the self-adjoint reality
    source for that membership predicate. -/
structure G8ActualXiIotaTauCanonicalSpectralMemberNonreal
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (membershipSource :
      G8ActualXiIotaTauCanonicalScaledSpectralMembershipSource
        operatorCtx operatorReady) where
  z : G8ActualXiNonzeroHeightCarrier
  nonreal :
    (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z).im ≠ 0

/-- Spectral-member non-reality is fatal for the self-adjoint reality source. -/
theorem G8ActualXiIotaTauCanonicalSpectralMemberNonreal.refutesRealitySource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {membershipSource :
      G8ActualXiIotaTauCanonicalScaledSpectralMembershipSource
        operatorCtx operatorReady}
    (w :
      G8ActualXiIotaTauCanonicalSpectralMemberNonreal
        membershipSource)
    (realitySource :
      G8ActualXiIotaTauCanonicalSelfAdjointSpectrumRealitySource
        operatorCtx operatorReady membershipSource.spectralMembership) :
    False :=
  w.nonreal
    (realitySource.selfAdjointSpectrumReality w.z
      (membershipSource.spectralMembership_holds w.z))

/-- Finite diagnostics without canonical spectral membership and exact
    self-adjoint real-valuedness do not constitute the source theorem. -/
structure G8ActualXiIotaTauCanonicalDiagnosticsOnly where
  z : G8ActualXiNonzeroHeightCarrier
  finiteSelfAdjointDiagnostic : Prop
  finiteK5DiagonalDiagnostic : Prop
  finiteSpectralCorrespondenceDiagnostic : Prop
  selfAdjointEvidence : finiteSelfAdjointDiagnostic
  k5Evidence : finiteK5DiagonalDiagnostic
  correspondenceEvidence : finiteSpectralCorrespondenceDiagnostic
  canonicalValue_nonreal :
    (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z).im ≠ 0

/-- Diagnostics-only evidence is refuted by a genuine canonical self-adjoint
    reality source. -/
theorem G8ActualXiIotaTauCanonicalDiagnosticsOnly.refutesSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w : G8ActualXiIotaTauCanonicalDiagnosticsOnly)
    (source :
      G8ActualXiIotaTauCanonicalSelfAdjointRealitySource
        operatorCtx operatorReady) :
    False :=
  w.canonicalValue_nonreal
    (source.realitySource.selfAdjointSpectrumReality w.z
      (source.membershipSource.spectralMembership_holds w.z))

end Tau.BookIII.Bridge
