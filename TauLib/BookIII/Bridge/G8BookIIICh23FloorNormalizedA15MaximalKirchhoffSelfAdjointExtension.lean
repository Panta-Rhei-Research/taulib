import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA14BoundaryFormCancellation

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Maximal Kirchhoff Extension

This module is the selected-carrier A1.5 layer after the A1.4 boundary-form
cancellation theorem.

The closed A1.4 source proves that the Kirchhoff graph Laplacian is symmetric.
A1.5 is strictly stronger: it needs maximality of the Kirchhoff boundary
conditions, equivalently exhaustion of the adjoint domain by the same
continuity/Kirchhoff trace laws.  Current TauLib does not yet expose that
analytic graph-operator theorem as a closed constructor, so this module makes
the precise load-bearing input proof-facing:

```text
closed selected A1.4 symmetry
  + adjoint-domain trace classification
  + maximal isotropic/Kirchhoff boundary condition
  -> maximal Kirchhoff extension
  -> selected self-adjointness source
```

It deliberately does not claim compact resolvent, discrete spectrum,
operator-native point-spectrum provenance, or A3 actual-`xi` membership.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CLOSED SELECTED A1.4 INPUT
-- ============================================================

/-- A selected A1.4 cancellation source is the closed source constructed in the
    previous wave. -/
def G8BookIIICh23FloorNormalizedA15ClosedSelectedA14Cancellation
    (source :
      G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource) :
    Prop :=
  source =
    g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed

/-- The closed A1.4 cancellation source is selected by definition. -/
theorem
    g8BookIIICh23FloorNormalizedA15ClosedSelectedA14Cancellation_closed :
    G8BookIIICh23FloorNormalizedA15ClosedSelectedA14Cancellation
      g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed :=
  rfl

/-- A1.4 supplies the symmetric Kirchhoff operator input used by A1.5. -/
def G8BookIIICh23FloorNormalizedA15KirchhoffSymmetricOperator
    (source :
      G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15ClosedSelectedA14Cancellation
      source ∧
    G8BookIIICh23FloorNormalizedA14BoundaryFormCancellation
      source.laplacianSource ∧
    G8BookIIICh23FloorNormalizedA14KirchhoffSymmetryLaw
      source.laplacianSource

/-- The closed A1.4 source is a symmetric Kirchhoff operator input. -/
theorem
    g8BookIIICh23FloorNormalizedA15KirchhoffSymmetricOperator_closed :
    G8BookIIICh23FloorNormalizedA15KirchhoffSymmetricOperator
      g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed
      |>.boundaryFormCancellation,
    g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed
      |>.kirchhoffSymmetryLaw⟩

-- ============================================================
-- ADJOINT-DOMAIN EXHAUSTION INPUT
-- ============================================================

/-- Proof-carrying A1.5 input: the adjoint-domain boundary traces are exactly
    the Kirchhoff traces.

This is the analytic content of the maximality theorem.  It records the two
standard components:

* the adjoint-domain trace classification;
* maximality of the Kirchhoff boundary condition among symmetric boundary
  conditions.

The final equality field is the Lean-facing exhaustion statement consumed by
the selected self-adjointness adapter. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput
    (source :
      G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource) where
  closedCancellationSource :
    G8BookIIICh23FloorNormalizedA15ClosedSelectedA14Cancellation
      source
  symmetricOperator :
    G8BookIIICh23FloorNormalizedA15KirchhoffSymmetricOperator
      source
  adjointBoundaryTraceExists : Prop
  adjointBoundaryTraceExistsWitness :
    adjointBoundaryTraceExists
  adjointTraceClassifiedByBoundaryForm : Prop
  adjointTraceClassifiedByBoundaryFormWitness :
    adjointTraceClassifiedByBoundaryForm
  adjointTraceSatisfiesCrossingAgreement : Prop
  adjointTraceSatisfiesCrossingAgreementWitness :
    adjointTraceSatisfiesCrossingAgreement
  adjointTraceSatisfiesKirchhoffBalance : Prop
  adjointTraceSatisfiesKirchhoffBalanceWitness :
    adjointTraceSatisfiesKirchhoffBalance
  maximalIsotropicKirchhoffBoundaryCondition : Prop
  maximalIsotropicKirchhoffBoundaryConditionWitness :
    maximalIsotropicKirchhoffBoundaryCondition
  kirchhoffDomainContainedInAdjointDomain : Prop
  kirchhoffDomainContainedInAdjointDomainWitness :
    kirchhoffDomainContainedInAdjointDomain
  adjointDomainContainedInKirchhoffDomain : Prop
  adjointDomainContainedInKirchhoffDomainWitness :
    adjointDomainContainedInKirchhoffDomain
  adjointDomainEqualsKirchhoffDomain : Prop
  adjointDomainEqualsKirchhoffDomainWitness :
    adjointDomainEqualsKirchhoffDomain
  status : SpineStatus := .conditional_interface

/-- The exact A1.5 theorem target: adjoint-domain exhaustion for the closed
    selected A1.4 source. -/
def G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionTarget :
    Prop :=
  Nonempty
    (G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput
      g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed)

-- ============================================================
-- MAXIMALITY AND SELF-ADJOINTNESS FROM EXHAUSTION
-- ============================================================

/-- No proper symmetric extension remains once the adjoint domain is exhausted
    by the Kirchhoff domain and the Kirchhoff boundary condition is maximal. -/
def G8BookIIICh23FloorNormalizedA15NoProperSymmetricExtension
    {source :
      G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource}
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput
        source) :
    Prop :=
  input.adjointDomainEqualsKirchhoffDomain ∧
    input.maximalIsotropicKirchhoffBoundaryCondition

/-- Adjoint-domain exhaustion gives the no-proper-symmetric-extension law. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput.noProperSymmetricExtension
    {source :
      G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource}
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput
        source) :
    G8BookIIICh23FloorNormalizedA15NoProperSymmetricExtension
      input :=
  ⟨input.adjointDomainEqualsKirchhoffDomainWitness,
    input.maximalIsotropicKirchhoffBoundaryConditionWitness⟩

/-- Maximal Kirchhoff extension for the selected source. -/
def G8BookIIICh23FloorNormalizedA15MaximalKirchhoffExtension
    (source :
      G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource) :
    Prop :=
  ∃ input :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput
      source,
    G8BookIIICh23FloorNormalizedA15NoProperSymmetricExtension input

/-- An adjoint-domain exhaustion input proves maximality of the Kirchhoff
    extension. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput.maximalKirchhoffExtension
    {source :
      G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource}
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput
        source) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffExtension
      source :=
  ⟨input, input.noProperSymmetricExtension⟩

/-- Selected self-adjointness is symmetry plus maximal Kirchhoff extension. -/
def G8BookIIICh23FloorNormalizedA15SelfAdjointnessFromMaximality
    (source :
      G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15KirchhoffSymmetricOperator
      source ∧
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffExtension
      source

/-- An adjoint-domain exhaustion input proves selected self-adjointness from
    A1.4 symmetry plus A1.5 maximality. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput.selfAdjointnessFromMaximality
    {source :
      G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource}
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput
        source) :
    G8BookIIICh23FloorNormalizedA15SelfAdjointnessFromMaximality
      source :=
  ⟨input.symmetricOperator, input.maximalKirchhoffExtension⟩

-- ============================================================
-- A1.5 SOURCE
-- ============================================================

/-- Selected-carrier A1.5 source: maximal Kirchhoff self-adjointness of the
    graph Laplacian constructed in A1.3 and symmetrized in A1.4.

The source is intentionally parameterized by the adjoint-domain exhaustion
input.  This prevents A1.4 boundary-form cancellation from being mistaken for
the maximal self-adjointness theorem. -/
structure
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionSource where
  cancellationSource :
    G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource
  closedCancellationSource :
    G8BookIIICh23FloorNormalizedA15ClosedSelectedA14Cancellation
      cancellationSource
  symmetricOperator :
    G8BookIIICh23FloorNormalizedA15KirchhoffSymmetricOperator
      cancellationSource
  adjointDomainExhaustion :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput
      cancellationSource
  noProperSymmetricExtension :
    G8BookIIICh23FloorNormalizedA15NoProperSymmetricExtension
      adjointDomainExhaustion
  maximalKirchhoffExtension :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffExtension
      cancellationSource
  selfAdjointnessFromMaximality :
    G8BookIIICh23FloorNormalizedA15SelfAdjointnessFromMaximality
      cancellationSource
  compactResolventNotClaimed : Prop
  compactResolventNotClaimedWitness : compactResolventNotClaimed
  pointSpectrumRealityNotClaimed : Prop
  pointSpectrumRealityNotClaimedWitness : pointSpectrumRealityNotClaimed
  status : SpineStatus := .conditional_interface

/-- Target for selected-carrier A1.5 maximal Kirchhoff self-adjointness. -/
def
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionSource

/-- An A1.5 source proves the selected A1.5 target. -/
theorem
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionSource.toTarget
    (source :
      G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionSource) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  ⟨source⟩

/-- Build the selected A1.5 source from the exact adjoint-domain exhaustion
    theorem. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionSource.ofAdjointDomainExhaustion
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput
        g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionSource where
  cancellationSource :=
    g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed
  closedCancellationSource :=
    g8BookIIICh23FloorNormalizedA15ClosedSelectedA14Cancellation_closed
  symmetricOperator :=
    g8BookIIICh23FloorNormalizedA15KirchhoffSymmetricOperator_closed
  adjointDomainExhaustion := input
  noProperSymmetricExtension := input.noProperSymmetricExtension
  maximalKirchhoffExtension := input.maximalKirchhoffExtension
  selfAdjointnessFromMaximality := input.selfAdjointnessFromMaximality
  compactResolventNotClaimed := True
  compactResolventNotClaimedWitness := trivial
  pointSpectrumRealityNotClaimed := True
  pointSpectrumRealityNotClaimedWitness := trivial
  status := .conditional_interface

/-- The exact A1.5 adjoint-domain exhaustion theorem is sufficient for the
    selected-carrier A1.5 target. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofAdjointDomainExhaustion
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput
        g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  (G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionSource.ofAdjointDomainExhaustion
    input).toTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A1.4 symmetry alone is not A1.5 maximality. -/
structure G8BookIIICh23FloorNormalizedA15SymmetryWithoutMaximality where
  cancellationSource :
    G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource
  symmetry :
    G8BookIIICh23FloorNormalizedA15KirchhoffSymmetricOperator
      cancellationSource
  noMaximality :
    ¬ G8BookIIICh23FloorNormalizedA15MaximalKirchhoffExtension
      cancellationSource

/-- A symmetry-only gap refutes an attempted maximality proof. -/
theorem
    G8BookIIICh23FloorNormalizedA15SymmetryWithoutMaximality.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15SymmetryWithoutMaximality)
    (h :
      G8BookIIICh23FloorNormalizedA15MaximalKirchhoffExtension
        gap.cancellationSource) :
    False :=
  gap.noMaximality h

/-- Missing adjoint-domain exhaustion refutes a selected A1.5 source. -/
structure G8BookIIICh23FloorNormalizedA15MissingAdjointDomainExhaustion
    (source :
      G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource) where
  missing :
    ¬ Nonempty
      (G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput
        source)

theorem
    G8BookIIICh23FloorNormalizedA15MissingAdjointDomainExhaustion.refutesSource
    {source :
      G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource}
    (gap :
      G8BookIIICh23FloorNormalizedA15MissingAdjointDomainExhaustion
        source)
    (a15 :
      G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionSource)
    (hsource : a15.cancellationSource = source) :
    False := by
  subst hsource
  exact gap.missing ⟨a15.adjointDomainExhaustion⟩

/-- Compact resolvent remains A1.6; it is not obtained from A1.5 alone. -/
structure G8BookIIICh23FloorNormalizedA15PrematureCompactResolventClaim
    (source :
      G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionSource) where
  claimedCompactResolvent : Prop
  noCompactResolventFromA15Alone : ¬ claimedCompactResolvent

theorem
    G8BookIIICh23FloorNormalizedA15PrematureCompactResolventClaim.refutes
    {source :
      G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionSource}
    (claim :
      G8BookIIICh23FloorNormalizedA15PrematureCompactResolventClaim
        source) :
    ¬ claim.claimedCompactResolvent :=
  claim.noCompactResolventFromA15Alone

/-- Point-spectrum reality remains A2.9; it is not obtained from A1.5 alone. -/
structure G8BookIIICh23FloorNormalizedA15PrematurePointSpectrumRealityClaim
    (source :
      G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionSource) where
  claimedPointSpectrumReality : Prop
  noPointSpectrumRealityFromA15Alone : ¬ claimedPointSpectrumReality

theorem
    G8BookIIICh23FloorNormalizedA15PrematurePointSpectrumRealityClaim.refutes
    {source :
      G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionSource}
    (claim :
      G8BookIIICh23FloorNormalizedA15PrematurePointSpectrumRealityClaim
        source) :
    ¬ claim.claimedPointSpectrumReality :=
  claim.noPointSpectrumRealityFromA15Alone

end Tau.BookIII.Bridge
