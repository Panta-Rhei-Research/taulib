import TauLib.BookIII.Bridge.G8LemniscateSelfAdjointSpectrumReality

/-!
# TauLib.BookIII.Bridge.G8ActualXiCanonicalAbstractSpectralMembershipSource

Proof-facing source layer for the weak Lane-A nonzero-height route.

The strong standard-mode route asks every canonical scaled actual `xi` value to
equal a specific standard eigenvalue.  Lane A only needs the weaker statement
that the canonical scaled value is a genuine member of a self-adjoint
lemniscate spectral source, hence real-valued.

This module keeps that weaker route honest by separating:

* an operator-native spectral-membership predicate;
* self-adjoint real-valuedness for members of that predicate;
* canonical actual-`xi` membership in that predicate.

The `operatorNativeSource` field is intentionally explicit.  It is the next
mathematical payload, not a theorem manufactured from the canonical values.
Finite checks remain diagnostics unless they provide exact operator-native
membership and exact real-valuedness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- OPERATOR-NATIVE ABSTRACT MEMBERSHIP
-- ============================================================

/-- Classification tag for the intended meaning of an abstract lemniscate
    spectral-membership predicate.  The tag is diagnostic; the proof-bearing
    content is still carried by `operatorNativeSource` and
    `selfAdjointSpectrumReality`. -/
inductive G8LemniscateSpectralMembershipKind where
  | operatorSpectrum
  | pointSpectrum
  | spectralMeasureSupport
  | abstractReadout
deriving DecidableEq

/-- Operator-native legitimacy package for a lemniscate spectral predicate.

This is the source-facing version of the weak lane.  It prevents the useful
adapter from silently collapsing to a predicate chosen only to contain the
canonical values: the operator-native provenance is an explicit proof field. -/
structure G8LemniscateSpectralMembershipLegitimacy
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  spectralMembership :
    G8LemniscateSpectrumMembership operatorCtx operatorReady
  kind : G8LemniscateSpectralMembershipKind
  operatorNativeSource : Prop
  operatorNativeEvidence : operatorNativeSource
  selfAdjointSpectrumReality :
    ∀ spectralValue : ℂ,
      spectralMembership spectralValue → spectralValue.im = 0
  diagnostics : G8LemniscateSpectrumRealityDiagnostics := {}

/-- Forget the extra provenance fields and recover the existing generic
    self-adjoint spectrum-reality source. -/
def G8LemniscateSpectralMembershipLegitimacy.toSelfAdjointSpectrumRealitySource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (legitimacy :
      G8LemniscateSpectralMembershipLegitimacy
        operatorCtx operatorReady) :
    G8LemniscateSelfAdjointSpectrumRealitySource
      operatorCtx operatorReady where
  spectralMembership := legitimacy.spectralMembership
  selfAdjointSpectrumReality := legitimacy.selfAdjointSpectrumReality
  diagnostics := legitimacy.diagnostics

/-- Spectral members of a legitimate self-adjoint source are real-valued. -/
def G8LemniscateSpectralMembershipLegitimacy.realOfMember
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (legitimacy :
      G8LemniscateSpectralMembershipLegitimacy
        operatorCtx operatorReady)
    (spectralValue : ℂ)
    (hMember : legitimacy.spectralMembership spectralValue) :
    spectralValue.im = 0 :=
  legitimacy.selfAdjointSpectrumReality spectralValue hMember

-- ============================================================
-- CANONICAL ACTUAL-XI MEMBERSHIP SOURCE
-- ============================================================

/-- The actual-`xi` membership theorem for a legitimate abstract spectral
    source: every canonical scaled nonzero-height carrier value is a member of
    the operator-native predicate. -/
structure G8ActualXiCanonicalAbstractSpectralMembershipSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (legitimacy :
      G8LemniscateSpectralMembershipLegitimacy
        operatorCtx operatorReady) where
  canonicalMembership :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      legitimacy.spectralMembership
        (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z)
  diagnostics : G8ActualXiNonzeroHeightScaledOperatorDiagnostics := {}

/-- A canonical abstract membership source is exactly the existing pointwise
    membership target for the forgotten generic self-adjoint source. -/
def G8ActualXiCanonicalAbstractSpectralMembershipSource.toMembershipTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {legitimacy :
      G8LemniscateSpectralMembershipLegitimacy
        operatorCtx operatorReady}
    (source :
      G8ActualXiCanonicalAbstractSpectralMembershipSource
        legitimacy) :
    G8ActualXiIotaTauCanonicalLemniscateSpectralMembershipTarget
      legitimacy.toSelfAdjointSpectrumRealitySource :=
  source.canonicalMembership

/-- The abstract source instantiates the canonical self-adjoint reality source. -/
def G8ActualXiCanonicalAbstractSpectralMembershipSource.toCanonicalSelfAdjointSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {legitimacy :
      G8LemniscateSpectralMembershipLegitimacy
        operatorCtx operatorReady}
    (source :
      G8ActualXiCanonicalAbstractSpectralMembershipSource
        legitimacy) :
    G8ActualXiIotaTauCanonicalSelfAdjointRealitySource
      operatorCtx operatorReady :=
  legitimacy.toSelfAdjointSpectrumRealitySource.toCanonicalSelfAdjointSource
    source.toMembershipTarget

/-- The abstract source feeds the Book III operator spectral-image source. -/
def G8ActualXiCanonicalAbstractSpectralMembershipSource.toBookIIISource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {legitimacy :
      G8LemniscateSpectralMembershipLegitimacy
        operatorCtx operatorReady}
    (source :
      G8ActualXiCanonicalAbstractSpectralMembershipSource
        legitimacy) :
    G8ActualXiIotaTauBookIIIOperatorSpectralImageSource :=
  source.toCanonicalSelfAdjointSource.toBookIIISource

/-- The abstract source is Lane-A sufficient for nonzero-height spectral
    parameter reality. -/
theorem G8ActualXiCanonicalAbstractSpectralMembershipSource.toSpectralParameterReal
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {legitimacy :
      G8LemniscateSpectralMembershipLegitimacy
        operatorCtx operatorReady}
    (source :
      G8ActualXiCanonicalAbstractSpectralMembershipSource
        legitimacy) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  source.toCanonicalSelfAdjointSource.toSpectralParameterReal

/-- The abstract source also feeds the existing nonzero-height operator readout
    corridor. -/
def G8ActualXiCanonicalAbstractSpectralMembershipSource.toOperatorReadoutContext
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {legitimacy :
      G8LemniscateSpectralMembershipLegitimacy
        operatorCtx operatorReady}
    (source :
      G8ActualXiCanonicalAbstractSpectralMembershipSource
        legitimacy) :
    G8ActualXiNonzeroHeightOperatorSpectralReadoutContext :=
  source.toCanonicalSelfAdjointSource.toOperatorReadoutContext

/-- Combined weak-lane package: a legitimate operator-native spectral predicate
    plus canonical actual-`xi` membership in that predicate. -/
structure G8ActualXiCanonicalAbstractSelfAdjointRouteSource
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  legitimacy :
    G8LemniscateSpectralMembershipLegitimacy
      operatorCtx operatorReady
  membershipSource :
    G8ActualXiCanonicalAbstractSpectralMembershipSource legitimacy

/-- Combined package to the canonical self-adjoint source. -/
def G8ActualXiCanonicalAbstractSelfAdjointRouteSource.toCanonicalSelfAdjointSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (route :
      G8ActualXiCanonicalAbstractSelfAdjointRouteSource
        operatorCtx operatorReady) :
    G8ActualXiIotaTauCanonicalSelfAdjointRealitySource
      operatorCtx operatorReady :=
  route.membershipSource.toCanonicalSelfAdjointSource

/-- Combined package to nonzero-height spectral-parameter reality. -/
theorem G8ActualXiCanonicalAbstractSelfAdjointRouteSource.toSpectralParameterReal
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (route :
      G8ActualXiCanonicalAbstractSelfAdjointRouteSource
        operatorCtx operatorReady) :
    G8ActualXiNonzeroHeightSpectralParameterReal :=
  route.membershipSource.toSpectralParameterReal

-- ============================================================
-- RED-TEAM FALSIFIERS AND GUARDRAILS
-- ============================================================

/-- A non-real member refutes the operator-native legitimacy package. -/
structure G8LemniscateLegitimateSpectralMemberNonreal
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (legitimacy :
      G8LemniscateSpectralMembershipLegitimacy
        operatorCtx operatorReady) where
  spectralValue : ℂ
  member : legitimacy.spectralMembership spectralValue
  nonreal : spectralValue.im ≠ 0

/-- Non-real membership is fatal for a legitimate self-adjoint source. -/
theorem G8LemniscateLegitimateSpectralMemberNonreal.refutes
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {legitimacy :
      G8LemniscateSpectralMembershipLegitimacy
        operatorCtx operatorReady}
    (w :
      G8LemniscateLegitimateSpectralMemberNonreal
        legitimacy) :
    False :=
  w.nonreal (legitimacy.realOfMember w.spectralValue w.member)

/-- A missing canonical value refutes the actual-`xi` membership source for a
    legitimate operator-native predicate. -/
structure G8ActualXiCanonicalAbstractMembershipGap
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (legitimacy :
      G8LemniscateSpectralMembershipLegitimacy
        operatorCtx operatorReady) where
  z : G8ActualXiNonzeroHeightCarrier
  notMember :
    ¬ legitimacy.spectralMembership
      (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z)

/-- Missing canonical membership is fatal for a claimed abstract membership
    source. -/
theorem G8ActualXiCanonicalAbstractMembershipGap.refutesSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {legitimacy :
      G8LemniscateSpectralMembershipLegitimacy
        operatorCtx operatorReady}
    (gap :
      G8ActualXiCanonicalAbstractMembershipGap
        legitimacy)
    (source :
      G8ActualXiCanonicalAbstractSpectralMembershipSource
        legitimacy) :
    False :=
  gap.notMember (source.canonicalMembership gap.z)

/-- Diagnostic record for the forbidden shortcut where the predicate is only
    known to contain the canonical values, with no operator-native provenance. -/
structure G8CanonicalValuesOnlyMembershipAttempt
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  spectralMembership :
    G8LemniscateSpectrumMembership operatorCtx operatorReady
  containsCanonical :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      spectralMembership
        (g8ActualXiIotaTauCanonicalScaledOperatorSpectralValue z)
  missingOperatorNativeSource : Prop

/-- Diagnostic-only finite evidence does not supply the legitimate abstract
    self-adjoint membership route. -/
structure G8AbstractSpectralMembershipFiniteDiagnosticsOnly where
  finiteSelfAdjointDiagnostic : Prop
  finiteK5DiagonalDiagnostic : Prop
  finiteSpectralCorrespondenceDiagnostic : Prop
  selfAdjointEvidence : finiteSelfAdjointDiagnostic
  k5Evidence : finiteK5DiagonalDiagnostic
  correspondenceEvidence : finiteSpectralCorrespondenceDiagnostic

end Tau.BookIII.Bridge
