import TauLib.BookIII.Bridge.G8ActualXiStandardEigenvalueExactAlignment
import TauLib.BookIII.Bridge.G8LaneAOperatorNativeSelfAdjointSource
import TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightSpectralReality

/-!
# TauLib.BookIII.Bridge.G8ActualXiMinimalSelfAdjointMembershipRoute

Minimal Lane-A self-adjoint spectral-membership route.

The strong L3b-E route asks for exact membership in the standard discrete
lemniscate eigenvalue readout.  Lane A only needs the weaker operator-native
self-adjoint route:

```text
operator readiness
  + operator-native self-adjoint spectral legitimacy
  + canonical actual-xi membership in that legitimate spectral predicate
  -> nonzero-height spectral-parameter reality
  -> actual sigma-fixedness
```

This module packages that minimal target and forwards it through the existing
theorem-backed zero-height branch and final live-hinge adapters.  It does not
prove the weak gates; the quarantined Lane-A ledger remains the audit harness
for those obligations.

The standard exact-alignment route is preserved as a strengthening: exact
standard eigenvalue alignment implies the weak route, but the reverse is not
asserted.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- MINIMAL WEAK LANE-A TARGET
-- ============================================================

/-- Minimal Lane-A nonzero-height target: a proof-carrying abstract
    self-adjoint route for the given Book III operator context. -/
def G8ActualXiMinimalSelfAdjointMembershipTarget
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) : Prop :=
  Nonempty
    (G8ActualXiCanonicalAbstractSelfAdjointRouteSource
      operatorCtx operatorReady)

/-- Any explicit abstract self-adjoint route supplies the minimal target. -/
def G8ActualXiCanonicalAbstractSelfAdjointRouteSource.toMinimalTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (route :
      G8ActualXiCanonicalAbstractSelfAdjointRouteSource
        operatorCtx operatorReady) :
    G8ActualXiMinimalSelfAdjointMembershipTarget
      operatorCtx operatorReady :=
  ⟨route⟩

/-- A clean A1/A2 operator-native source plus the separate A3 membership theorem
    supplies the minimal weak Lane-A target. -/
def G8LaneAOperatorNativeSelfAdjointSource.toMinimalTarget
    (source : G8LaneAOperatorNativeSelfAdjointSource)
    (membership :
      G8ActualXiCanonicalAbstractSpectralMembershipSource
        source.legitimacy) :
    G8ActualXiMinimalSelfAdjointMembershipTarget
      source.operatorCtx source.operatorReady :=
  (source.toAbstractSelfAdjointRoute membership).toMinimalTarget

/-- The minimal target supplies the nonzero-height spectral-parameter reality
    payload. -/
theorem G8ActualXiMinimalSelfAdjointMembershipTarget.toSpectralParameterReal
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (target :
      G8ActualXiMinimalSelfAdjointMembershipTarget
        operatorCtx operatorReady) :
    G8ActualXiNonzeroHeightSpectralParameterReal := by
  rcases target with ⟨route⟩
  exact route.toSpectralParameterReal

/-- The minimal target plus the theorem-backed zero-height branch supplies the
    sharpened Lane-A input package. -/
def G8ActualXiMinimalSelfAdjointMembershipTarget.toNonzeroHeightInputs
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (target :
      G8ActualXiMinimalSelfAdjointMembershipTarget
        operatorCtx operatorReady) :
    G8ActualXiNonzeroHeightSpectralRealityInputs :=
  G8ActualXiNonzeroHeightSpectralRealityInputs.ofPairedEtaClosure
    target.toSpectralParameterReal

/-- The minimal target supplies actual sigma-fixedness. -/
theorem G8ActualXiMinimalSelfAdjointMembershipTarget.actualSigmaFixed
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (target :
      G8ActualXiMinimalSelfAdjointMembershipTarget
        operatorCtx operatorReady) :
    G8ActualXiBoundaryCharacterSigmaFixed :=
  target.toNonzeroHeightInputs.actualSigmaFixed

/-- The minimal target supplies crossing-mediated readout evidence. -/
theorem G8ActualXiMinimalSelfAdjointMembershipTarget.toCrossingMediatedAll
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (target :
      G8ActualXiMinimalSelfAdjointMembershipTarget
        operatorCtx operatorReady) :
    G8ActualXiBoundaryReadoutCrossingMediatedAll :=
  target.toNonzeroHeightInputs.toCrossingMediatedAll

/-- The minimal target plus accepted tower realization builds the existing
    final live hinge. -/
def G8ActualXiMinimalSelfAdjointMembershipTarget.toFinalLiveHinge
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (target :
      G8ActualXiMinimalSelfAdjointMembershipTarget
        operatorCtx operatorReady)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8FinalLiveHinge model :=
  target.toNonzeroHeightInputs.toFinalLiveHinge realization

/-- The minimal target plus accepted tower realization supplies pointwise
    accepted centered-address coverage. -/
theorem G8ActualXiMinimalSelfAdjointMembershipTarget.pointwiseCoverage
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (target :
      G8ActualXiMinimalSelfAdjointMembershipTarget
        operatorCtx operatorReady)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8BookIIIPointwiseAcceptedCenteredAddressCoverage model :=
  (target.toFinalLiveHinge realization).pointwiseCoverage

/-- The minimal target plus accepted tower realization forwards to the existing
    conditional Mathlib handoff. -/
theorem G8ActualXiMinimalSelfAdjointMembershipTarget.mathlibRiemannHypothesis
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (target :
      G8ActualXiMinimalSelfAdjointMembershipTarget
        operatorCtx operatorReady)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    RiemannHypothesis :=
  (target.toFinalLiveHinge realization).mathlibRiemannHypothesis

-- ============================================================
-- STANDARD ROUTE AS A STRICT STRENGTHENING
-- ============================================================

/-- The standard lemniscate eigenvalue readout is a theorem-backed legitimate
    self-adjoint spectral predicate. -/
def g8StandardLemniscateSpectralMembershipLegitimacy
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) :
    G8LemniscateSpectralMembershipLegitimacy
      operatorCtx operatorReady where
  spectralMembership :=
    G8StandardLemniscateEigenvalueSpectrum operatorCtx operatorReady
  kind := .pointSpectrum
  operatorNativeSource := True
  operatorNativeEvidence := trivial
  selfAdjointSpectrumReality := by
    intro spectralValue hMember
    exact g8StandardLemniscateEigenvalueSpectrum_real
      spectralValue hMember
  diagnostics := g8StandardLemniscateSpectrumRealityDiagnostics

/-- Exact standard-mode alignment gives an abstract self-adjoint route. -/
def G8ActualXiCanonicalSelectedModeExactAlignmentSource.toMinimalSelfAdjointRoute
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalSelectedModeExactAlignmentSource
        operatorCtx operatorReady) :
    G8ActualXiCanonicalAbstractSelfAdjointRouteSource
      operatorCtx operatorReady where
  legitimacy :=
    g8StandardLemniscateSpectralMembershipLegitimacy
      operatorCtx operatorReady
  membershipSource := {
    canonicalMembership := fun z => source.standardSpectrumMember z
  }

/-- Exact standard-mode alignment is stronger than the minimal weak route. -/
def G8ActualXiCanonicalSelectedModeExactAlignmentSource.toMinimalTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (source :
      G8ActualXiCanonicalSelectedModeExactAlignmentSource
        operatorCtx operatorReady) :
    G8ActualXiMinimalSelfAdjointMembershipTarget
      operatorCtx operatorReady :=
  source.toMinimalSelfAdjointRoute.toMinimalTarget

/-- The Prop-valued exact-alignment target implies the minimal weak target. -/
theorem
    G8ActualXiCanonicalSelectedModeExactAlignmentTarget.toMinimalTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (target :
      G8ActualXiCanonicalSelectedModeExactAlignmentTarget
        operatorCtx operatorReady) :
    G8ActualXiMinimalSelfAdjointMembershipTarget
      operatorCtx operatorReady := by
  rcases target with ⟨source⟩
  exact source.toMinimalTarget

-- ============================================================
-- GUARDRAILS AND FALSIFIERS
-- ============================================================

/-- Weak abstract self-adjoint membership does not by itself supply the strong
    standard eigenvalue membership target. -/
structure G8ActualXiMinimalSelfAdjointWithoutStandardEigenvalue
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  minimalTarget :
    G8ActualXiMinimalSelfAdjointMembershipTarget
      operatorCtx operatorReady
  noStandardMembership :
    ¬ G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
      operatorCtx operatorReady

/-- A weak-route witness with no standard membership refutes any claimed exact
    standard-mode alignment target. -/
theorem
    G8ActualXiMinimalSelfAdjointWithoutStandardEigenvalue.refutesExactAlignment
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8ActualXiMinimalSelfAdjointWithoutStandardEigenvalue
        operatorCtx operatorReady)
    (hExact :
      G8ActualXiCanonicalSelectedModeExactAlignmentTarget
        operatorCtx operatorReady) :
    False := by
  have hMembership :
      G8ActualXiIotaTauCanonicalStandardEigenvalueMembershipTarget
        operatorCtx operatorReady :=
    (g8ActualXiCanonicalSelectedModeExactAlignmentTarget_iff_membershipTarget
      (operatorCtx := operatorCtx)
      (operatorReady := operatorReady)).mp hExact
  exact w.noStandardMembership hMembership

/-- Knowing only a predicate containing the canonical values, without
    operator-native legitimacy, is not the minimal self-adjoint route. -/
structure G8ActualXiMinimalSelfAdjointCanonicalValuesOnlyAttempt
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  attempt :
    G8CanonicalValuesOnlyMembershipAttempt
      operatorCtx operatorReady
  noMinimalTarget :
    ¬ G8ActualXiMinimalSelfAdjointMembershipTarget
      operatorCtx operatorReady

/-- Canonical-values-only evidence refutes a claimed minimal target when the
    witness explicitly records that no such target is available. -/
theorem
    G8ActualXiMinimalSelfAdjointCanonicalValuesOnlyAttempt.refutesMinimalTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8ActualXiMinimalSelfAdjointCanonicalValuesOnlyAttempt
        operatorCtx operatorReady)
    (target :
      G8ActualXiMinimalSelfAdjointMembershipTarget
        operatorCtx operatorReady) :
    False :=
  w.noMinimalTarget target

/-- Finite diagnostics alone do not count as operator-native self-adjoint
    membership legitimacy. -/
structure G8ActualXiMinimalSelfAdjointFiniteDiagnosticsOnly
    (operatorCtx : LemniscateOperatorContext)
    (operatorReady : LemniscateOperatorReady operatorCtx) where
  diagnostics : G8AbstractSpectralMembershipFiniteDiagnosticsOnly
  noMinimalTarget :
    ¬ G8ActualXiMinimalSelfAdjointMembershipTarget
      operatorCtx operatorReady

/-- Diagnostic-only finite evidence refutes a claimed minimal target when it
    explicitly records that the operator-native route is still absent. -/
theorem
    G8ActualXiMinimalSelfAdjointFiniteDiagnosticsOnly.refutesMinimalTarget
    {operatorCtx : LemniscateOperatorContext}
    {operatorReady : LemniscateOperatorReady operatorCtx}
    (w :
      G8ActualXiMinimalSelfAdjointFiniteDiagnosticsOnly
        operatorCtx operatorReady)
    (target :
      G8ActualXiMinimalSelfAdjointMembershipTarget
        operatorCtx operatorReady) :
    False :=
  w.noMinimalTarget target

end Tau.BookIII.Bridge
