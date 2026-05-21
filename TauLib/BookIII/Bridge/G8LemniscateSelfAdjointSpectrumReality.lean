import TauLib.BookIII.Bridge.G8ActualXiIotaTauCanonicalSelfAdjointRealitySource

/-!
# TauLib.BookIII.Bridge.G8LemniscateSelfAdjointSpectrumReality

Generic self-adjoint spectrum-reality surface for the Lane-A lemniscate operator
route.

The canonical `iota_tau^2` scaled image is now definitionally fixed.  The next
source theorem should not mix the operator fact with actual `xi` membership.
This module therefore separates:

* a generic lemniscate spectral-membership predicate on complex values;
* a self-adjoint spectrum-reality selector for that predicate;
* the pointwise assertion that the canonical actual `xi` scaled value belongs to
  that predicate.

Only the last point is actual-`xi` specific.  Finite checks remain diagnostics;
they do not replace spectral membership or real-valuedness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- GENERIC LEMNISCATE SPECTRAL REALITY
-- ============================================================

/-- A spectral-membership predicate for a ready lemniscate operator package,
    stated at the level of complex spectral readouts. -/
def G8LemniscateSpectrumMembership
    (_operatorCtx : LemniscateOperatorContext)
    (_operatorReady : LemniscateOperatorReady _operatorCtx) : Type :=
  ℂ → Prop

/-- Non-load-bearing diagnostics for a lemniscate spectral-reality source. -/
structure G8LemniscateSpectrumRealityDiagnostics where
  finiteSelfAdjointDiagnostic : Prop := True
  finiteK5DiagonalDiagnostic : Prop := True
  finiteSpectralCorrespondenceDiagnostic : Prop := True
  status : SpineStatus := .conditional_interface

/-- Generic self-adjoint spectrum-reality source.

The load-bearing field is `selfAdjointSpectrumReality`: if a complex value is a
spectral member of the ready lemniscate operator package, then it is real-valued
in the sense that its imaginary coordinate vanishes. -/
structure G8LemniscateSelfAdjointSpectrumRealitySource
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  spectralMembership :
    G8LemniscateSpectrumMembership operatorCtx operatorReady
  selfAdjointSpectrumReality :
    ∀ spectralValue : ℂ,
      spectralMembership spectralValue → spectralValue.im = 0
  diagnostics : G8LemniscateSpectrumRealityDiagnostics := {}

/-- The generic source gives a compact theorem target: spectral members are real. -/
def G8LemniscateSelfAdjointSpectrumRealitySource.realOfMember
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8LemniscateSelfAdjointSpectrumRealitySource
        operatorCtx operatorReady)
    (spectralValue : ℂ)
    (hMember : source.spectralMembership spectralValue) :
    spectralValue.im = 0 :=
  source.selfAdjointSpectrumReality spectralValue hMember

-- ============================================================
-- CANONICAL XI MEMBERSHIP ADAPTER
-- ============================================================

/-- The actual-`xi` specific membership target: every nonzero-height carrier's
    canonical scaled value belongs to the generic lemniscate spectral predicate. -/
def G8ActualXiIotaTauCanonicalLemniscateSpectralMembershipTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8LemniscateSelfAdjointSpectrumRealitySource
        operatorCtx operatorReady) : Prop :=
  ∀ z : G8ActualXiNonzeroHeightCarrier,
    source.spectralMembership
      (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z)

/-- Generic lemniscate spectral reality plus pointwise canonical membership
    builds the canonical scaled spectral-membership source. -/
def
    G8LemniscateSelfAdjointSpectrumRealitySource.toCanonicalMembershipSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8LemniscateSelfAdjointSpectrumRealitySource
        operatorCtx operatorReady)
    (canonicalMembership :
      G8ActualXiIotaTauCanonicalLemniscateSpectralMembershipTarget
        source) :
    G8ActualXiIotaTauCanonicalScaledSpectralMembershipSource
      operatorCtx operatorReady where
  spectralMembership := fun z =>
    source.spectralMembership
      (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z)
  spectralMembership_holds := canonicalMembership

/-- Generic lemniscate spectral reality builds the canonical self-adjoint reality
    selector for the induced pointwise membership predicate. -/
def
    G8LemniscateSelfAdjointSpectrumRealitySource.toCanonicalSpectrumRealitySource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8LemniscateSelfAdjointSpectrumRealitySource
        operatorCtx operatorReady)
    (canonicalMembership :
      G8ActualXiIotaTauCanonicalLemniscateSpectralMembershipTarget
        source) :
    G8ActualXiIotaTauCanonicalSelfAdjointSpectrumRealitySource
      operatorCtx operatorReady
      (source.toCanonicalMembershipSource
        canonicalMembership).spectralMembership where
  selfAdjointSpectrumReality := by
    intro z hMember
    exact
      source.realOfMember
        (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z)
        hMember

/-- Generic lemniscate spectral reality plus canonical membership instantiates the
    existing canonical self-adjoint reality source. -/
def G8LemniscateSelfAdjointSpectrumRealitySource.toCanonicalSelfAdjointSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8LemniscateSelfAdjointSpectrumRealitySource
        operatorCtx operatorReady)
    (canonicalMembership :
      G8ActualXiIotaTauCanonicalLemniscateSpectralMembershipTarget
        source) :
    G8ActualXiIotaTauCanonicalSelfAdjointRealitySource
      operatorCtx operatorReady where
  membershipSource :=
    source.toCanonicalMembershipSource canonicalMembership
  realitySource :=
    source.toCanonicalSpectrumRealitySource canonicalMembership

/-- The generic source plus canonical membership feeds the nonzero-height
    spectral-parameter reality payload. -/
theorem
    G8LemniscateSelfAdjointSpectrumRealitySource.toSpectralParameterReal
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8LemniscateSelfAdjointSpectrumRealitySource
        operatorCtx operatorReady)
    (canonicalMembership :
      G8ActualXiIotaTauCanonicalLemniscateSpectralMembershipTarget
        source) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  (source.toCanonicalSelfAdjointSource
    canonicalMembership).toSpectralParameterReal

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A spectral member with nonzero imaginary part refutes a generic self-adjoint
    spectrum-reality source. -/
structure G8LemniscateSpectralMemberNonreal
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8LemniscateSelfAdjointSpectrumRealitySource
        operatorCtx operatorReady) where
  spectralValue : ℂ
  member : source.spectralMembership spectralValue
  nonreal : spectralValue.im ≠ 0

/-- A non-real spectral member is fatal for the generic source. -/
theorem G8LemniscateSpectralMemberNonreal.refutes
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {source :
      G8LemniscateSelfAdjointSpectrumRealitySource
        operatorCtx operatorReady}
    (w : G8LemniscateSpectralMemberNonreal source) :
    False :=
  w.nonreal (source.realOfMember w.spectralValue w.member)

/-- A canonical scaled value missing from the generic spectral predicate refutes
    the canonical membership target. -/
structure G8ActualXiIotaTauCanonicalMissingLemniscateSpectralMember
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8LemniscateSelfAdjointSpectrumRealitySource
        operatorCtx operatorReady) where
  z : G8ActualXiNonzeroHeightCarrier
  notMember :
    ¬ source.spectralMembership
      (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z)

/-- Missing canonical membership refutes the pointwise membership target. -/
theorem
    G8ActualXiIotaTauCanonicalMissingLemniscateSpectralMember.refutesTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {source :
      G8LemniscateSelfAdjointSpectrumRealitySource
        operatorCtx operatorReady}
    (w :
      G8ActualXiIotaTauCanonicalMissingLemniscateSpectralMember
        source)
    (canonicalMembership :
      G8ActualXiIotaTauCanonicalLemniscateSpectralMembershipTarget
        source) :
    False :=
  w.notMember (canonicalMembership w.z)

/-- Finite diagnostics alone still do not supply generic spectral reality. -/
structure G8LemniscateFiniteDiagnosticsNonrealMemberAttempt where
  spectralValue : ℂ
  finiteSelfAdjointDiagnostic : Prop
  finiteK5DiagonalDiagnostic : Prop
  finiteSpectralCorrespondenceDiagnostic : Prop
  selfAdjointEvidence : finiteSelfAdjointDiagnostic
  k5Evidence : finiteK5DiagonalDiagnostic
  correspondenceEvidence : finiteSpectralCorrespondenceDiagnostic
  nonreal : spectralValue.im ≠ 0

/-- A diagnostics-only attempt is refuted if promoted to a generic source whose
    spectral predicate contains the same non-real value. -/
theorem G8LemniscateFiniteDiagnosticsNonrealMemberAttempt.refutesSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w : G8LemniscateFiniteDiagnosticsNonrealMemberAttempt)
    (source :
      G8LemniscateSelfAdjointSpectrumRealitySource
        operatorCtx operatorReady)
    (hMember : source.spectralMembership w.spectralValue) :
    False :=
  w.nonreal (source.realOfMember w.spectralValue hMember)

end Tau.BookIII.Bridge
