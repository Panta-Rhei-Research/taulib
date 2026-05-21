import TauLib.BookIII.Bridge.G8ActualXiCanonicalAbstractSpectralMembershipSource

/-!
# TauLib.BookIII.Bridge.G8LaneAOperatorNativeSelfAdjointSource

Proof-facing source layer for Lane-A gates A1/A2.

The quarantined Lane-A ledger splits the remaining weak nonzero-height route
into three gates:

1. a ready Book III lemniscate operator package;
2. an operator-native self-adjoint spectral predicate for that package;
3. canonical actual-`xi` membership in that legitimate predicate.

This module packages the first two gates without mentioning actual-`xi`
membership.  The actual-`xi` carrier theorem remains the separate A3 input.

Finite Book III checks may be carried as diagnostics, but they are not promoted
to global operator readiness, spectral membership, or self-adjoint spectral
reality.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- OPERATOR-NATIVE SPECTRAL PROVENANCE
-- ============================================================

/-- Source-level classification for an operator-native lemniscate spectral
    predicate.

Unlike `G8LemniscateSpectralMembershipKind`, this type deliberately has no
`abstractReadout` case.  A2 is meant to be operator-native; abstract readouts
belong on the A3/canonical-membership side of the split. -/
inductive G8OperatorNativeSpectralProvenanceKind where
  | operatorSpectrum
  | pointSpectrum
  | spectralMeasureSupport
deriving DecidableEq

/-- Forget the stricter operator-native source tag into the existing diagnostic
    membership-kind tag. -/
def G8OperatorNativeSpectralProvenanceKind.toMembershipKind :
    G8OperatorNativeSpectralProvenanceKind →
      G8LemniscateSpectralMembershipKind
  | .operatorSpectrum => .operatorSpectrum
  | .pointSpectrum => .pointSpectrum
  | .spectralMeasureSupport => .spectralMeasureSupport

/-- A strict provenance package for a lemniscate spectral predicate.

The load-bearing fields are:

* a native spectral predicate;
* exact agreement between the exported predicate and that native predicate;
* self-adjoint real-valuedness for every native member.

This is intentionally stronger than merely setting
`operatorNativeSource := True` in `G8LemniscateSpectralMembershipLegitimacy`. -/
structure G8OperatorNativeSpectralProvenance
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  spectralMembership :
    G8LemniscateSpectrumMembership operatorCtx operatorReady
  nativeMembership : ℂ → Prop
  kind : G8OperatorNativeSpectralProvenanceKind
  spectralMembership_iff_native :
    ∀ spectralValue : ℂ,
      spectralMembership spectralValue ↔ nativeMembership spectralValue
  selfAdjointReality_native :
    ∀ spectralValue : ℂ,
      nativeMembership spectralValue → spectralValue.im = 0
  diagnostics : G8LemniscateSpectrumRealityDiagnostics := {}

/-- Native members of a strict provenance package are real-valued. -/
def G8OperatorNativeSpectralProvenance.realOfNativeMember
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (provenance :
      G8OperatorNativeSpectralProvenance operatorCtx operatorReady)
    (spectralValue : ℂ)
    (hNative : provenance.nativeMembership spectralValue) :
    spectralValue.im = 0 :=
  provenance.selfAdjointReality_native spectralValue hNative

/-- Exported spectral members of a strict provenance package are real-valued. -/
def G8OperatorNativeSpectralProvenance.realOfSpectralMember
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (provenance :
      G8OperatorNativeSpectralProvenance operatorCtx operatorReady)
    (spectralValue : ℂ)
    (hMember : provenance.spectralMembership spectralValue) :
    spectralValue.im = 0 :=
  provenance.selfAdjointReality_native spectralValue
    ((provenance.spectralMembership_iff_native spectralValue).mp hMember)

/-- The structured operator-native proposition inserted into the older
    legitimacy surface.

This proposition records the native predicate, exact exported/native agreement,
and self-adjoint real-valuedness.  It is used instead of a bare `True`
operator-native source. -/
def G8OperatorNativeSpectralProvenance.operatorNativeSource
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (provenance :
      G8OperatorNativeSpectralProvenance operatorCtx operatorReady) : Prop :=
  ∃ nativeMembership : ℂ → Prop,
    (∀ spectralValue : ℂ,
      provenance.spectralMembership spectralValue ↔
        nativeMembership spectralValue) ∧
    (∀ spectralValue : ℂ,
      nativeMembership spectralValue → spectralValue.im = 0)

/-- Strict operator-native provenance produces the existing spectral-legitimacy
    package consumed by the weak Lane-A route. -/
def G8OperatorNativeSpectralProvenance.toLegitimacy
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (provenance :
      G8OperatorNativeSpectralProvenance operatorCtx operatorReady) :
    G8LemniscateSpectralMembershipLegitimacy
      operatorCtx operatorReady where
  spectralMembership := provenance.spectralMembership
  kind := provenance.kind.toMembershipKind
  operatorNativeSource := provenance.operatorNativeSource
  operatorNativeEvidence :=
    ⟨provenance.nativeMembership,
      provenance.spectralMembership_iff_native,
      provenance.selfAdjointReality_native⟩
  selfAdjointSpectrumReality := provenance.realOfSpectralMember
  diagnostics := provenance.diagnostics

/-- Strict provenance can never be exported as the abstract-readout kind. -/
theorem G8OperatorNativeSpectralProvenance.toLegitimacy_kind_ne_abstractReadout
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (provenance :
      G8OperatorNativeSpectralProvenance operatorCtx operatorReady) :
    provenance.toLegitimacy.kind ≠ .abstractReadout := by
  rcases provenance with
    ⟨_, _, kind, _, _, _⟩
  cases kind <;> simp [G8OperatorNativeSpectralProvenance.toLegitimacy,
    G8OperatorNativeSpectralProvenanceKind.toMembershipKind]

-- ============================================================
-- A1/A2 COMBINED SOURCE
-- ============================================================

/-- Combined proof-facing source for Lane-A gates A1/A2.

This package supplies a ready lemniscate operator context and a strict
operator-native self-adjoint spectral predicate for that context.  It does not
claim that canonical actual-`xi` values belong to the predicate; that is A3. -/
structure G8LaneAOperatorNativeSelfAdjointSource where
  operatorCtx : LemniscateOperatorContext
  operatorReady : LemniscateOperatorReady operatorCtx
  provenance :
    G8OperatorNativeSpectralProvenance operatorCtx operatorReady

/-- The spectral-legitimacy package exported by an A1/A2 source. -/
def G8LaneAOperatorNativeSelfAdjointSource.legitimacy
    (source : G8LaneAOperatorNativeSelfAdjointSource) :
    G8LemniscateSpectralMembershipLegitimacy
      source.operatorCtx source.operatorReady :=
  source.provenance.toLegitimacy

/-- The generic self-adjoint spectrum-reality source exported by an A1/A2
    source. -/
def G8LaneAOperatorNativeSelfAdjointSource.toSelfAdjointSpectrumRealitySource
    (source : G8LaneAOperatorNativeSelfAdjointSource) :
    G8LemniscateSelfAdjointSpectrumRealitySource
      source.operatorCtx source.operatorReady :=
  source.legitimacy.toSelfAdjointSpectrumRealitySource

/-- An A1/A2 source plus the separate A3 membership theorem builds the compact
    abstract self-adjoint route source. -/
def G8LaneAOperatorNativeSelfAdjointSource.toAbstractSelfAdjointRoute
    (source : G8LaneAOperatorNativeSelfAdjointSource)
    (membership :
      G8ActualXiCanonicalAbstractSpectralMembershipSource
        source.legitimacy) :
    G8ActualXiCanonicalAbstractSelfAdjointRouteSource
      source.operatorCtx source.operatorReady where
  legitimacy := source.legitimacy
  membershipSource := membership

/-- Prop-valued target for the combined A1/A2 source. -/
def G8LaneAOperatorNativeSelfAdjointSourceTarget : Prop :=
  Nonempty G8LaneAOperatorNativeSelfAdjointSource

-- ============================================================
-- GUARDRAILS AND FALSIFIERS
-- ============================================================

/-- A native member with nonzero imaginary part refutes strict operator-native
    spectral provenance. -/
structure G8OperatorNativeSpectralProvenanceNonrealNativeMember
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (provenance :
      G8OperatorNativeSpectralProvenance operatorCtx operatorReady) where
  spectralValue : ℂ
  nativeMember : provenance.nativeMembership spectralValue
  nonreal : spectralValue.im ≠ 0

/-- Non-real native membership is fatal for strict provenance. -/
theorem G8OperatorNativeSpectralProvenanceNonrealNativeMember.refutes
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {provenance :
      G8OperatorNativeSpectralProvenance operatorCtx operatorReady}
    (w :
      G8OperatorNativeSpectralProvenanceNonrealNativeMember
        provenance) :
    False :=
  w.nonreal
    (provenance.realOfNativeMember w.spectralValue w.nativeMember)

/-- A spectral member that is not native refutes exact exported/native
    agreement. -/
structure G8OperatorNativeSpectralProvenanceSpectralWithoutNative
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (provenance :
      G8OperatorNativeSpectralProvenance operatorCtx operatorReady) where
  spectralValue : ℂ
  spectralMember : provenance.spectralMembership spectralValue
  notNative : ¬ provenance.nativeMembership spectralValue

/-- Exported membership without native membership is impossible for strict
    provenance. -/
theorem G8OperatorNativeSpectralProvenanceSpectralWithoutNative.refutes
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {provenance :
      G8OperatorNativeSpectralProvenance operatorCtx operatorReady}
    (w :
      G8OperatorNativeSpectralProvenanceSpectralWithoutNative
        provenance) :
    False :=
  w.notNative
    ((provenance.spectralMembership_iff_native w.spectralValue).mp
      w.spectralMember)

/-- A native member that is not exported refutes exact exported/native
    agreement. -/
structure G8OperatorNativeSpectralProvenanceNativeWithoutSpectral
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (provenance :
      G8OperatorNativeSpectralProvenance operatorCtx operatorReady) where
  spectralValue : ℂ
  nativeMember : provenance.nativeMembership spectralValue
  notSpectral : ¬ provenance.spectralMembership spectralValue

/-- Native membership without exported membership is impossible for strict
    provenance. -/
theorem G8OperatorNativeSpectralProvenanceNativeWithoutSpectral.refutes
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {provenance :
      G8OperatorNativeSpectralProvenance operatorCtx operatorReady}
    (w :
      G8OperatorNativeSpectralProvenanceNativeWithoutSpectral
        provenance) :
    False :=
  w.notSpectral
    ((provenance.spectralMembership_iff_native w.spectralValue).mpr
      w.nativeMember)

/-- Finite diagnostics alone do not construct the combined A1/A2 source. -/
structure G8LaneAOperatorNativeSelfAdjointFiniteDiagnosticsOnly where
  diagnostics : G8AbstractSpectralMembershipFiniteDiagnosticsOnly
  noSource : ¬ G8LaneAOperatorNativeSelfAdjointSourceTarget

/-- Diagnostic-only finite evidence refutes a claimed A1/A2 source when it
    explicitly records that no such source is available. -/
theorem G8LaneAOperatorNativeSelfAdjointFiniteDiagnosticsOnly.refutesSource
    (w : G8LaneAOperatorNativeSelfAdjointFiniteDiagnosticsOnly)
    (source : G8LaneAOperatorNativeSelfAdjointSource) :
    False :=
  w.noSource ⟨source⟩

end Tau.BookIII.Bridge
