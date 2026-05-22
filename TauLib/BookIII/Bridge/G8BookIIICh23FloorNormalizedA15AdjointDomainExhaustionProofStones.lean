import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtension

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Adjoint-Domain Exhaustion Proof Stones

This module drills into the remaining A1.5 mathematical payload surfaced in
`G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtension`.

The forward inclusion

```text
Kirchhoff domain <= adjoint domain
```

is exactly the already-closed A1.4 symmetry result.  The hard reverse
inclusion is now split into its proof-map components:

```text
adjoint boundary traces exist
  -> boundary-form annihilator classification
  -> crossing trace agreement
  -> Kirchhoff derivative balance
  -> adjoint domain <= Kirchhoff domain
```

Together with maximal isotropic Kirchhoff boundary conditions, these stones
assemble the exact `G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput`
needed by the A1.5 maximality adapter.

No compact-resolvent, discrete-spectrum, point-spectrum, A3 actual-`xi`, or
RH-facing claim is made here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- THEOREM-BACKED FORWARD INCLUSION
-- ============================================================

/-- Closed selected A1.4 symmetry is the forward adjoint-domain inclusion:
    the Kirchhoff operator domain is contained in the adjoint domain. -/
def
    G8BookIIICh23FloorNormalizedA15KirchhoffDomainContainedInAdjointDomain :
    Prop :=
  G8BookIIICh23FloorNormalizedA15KirchhoffSymmetricOperator
    g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed

/-- The forward inclusion is closed by A1.4 boundary-form cancellation. -/
theorem
    g8BookIIICh23FloorNormalizedA15KirchhoffDomainContainedInAdjointDomain_closed :
    G8BookIIICh23FloorNormalizedA15KirchhoffDomainContainedInAdjointDomain :=
  g8BookIIICh23FloorNormalizedA15KirchhoffSymmetricOperator_closed

-- ============================================================
-- REVERSE-INCLUSION PROOF STONES
-- ============================================================

/-- Adjoint trace existence: every adjoint-domain vector has the boundary
    traces needed to test the Green boundary form. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource where
  traceExists : Prop
  traceExistsWitness : traceExists
  traceCompatibleWithSelectedA12SobolevTheory : Prop
  traceCompatibleWitness :
    traceCompatibleWithSelectedA12SobolevTheory
  status : SpineStatus := .conditional_interface

/-- Boundary-form annihilator classification: if a vector lies in the adjoint
    domain, its boundary traces annihilate the Kirchhoff test boundary form. -/
structure
    G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationSource where
  traceSource :
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource
  annihilatorClassifiedByGreenForm : Prop
  annihilatorClassifiedWitness :
    annihilatorClassifiedByGreenForm
  testsAllKirchhoffDomainElements : Prop
  testsAllKirchhoffDomainElementsWitness :
    testsAllKirchhoffDomainElements
  status : SpineStatus := .conditional_interface

/-- Crossing agreement forced from the annihilator classification. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointCrossingTraceAgreementSource where
  annihilatorSource :
    G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationSource
  crossingTraceAgreement : Prop
  crossingTraceAgreementWitness : crossingTraceAgreement
  valueTraceUsesA12CrossingClosure : Prop
  valueTraceUsesA12CrossingClosureWitness :
    valueTraceUsesA12CrossingClosure
  status : SpineStatus := .conditional_interface

/-- Kirchhoff derivative balance forced from the annihilator classification. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointKirchhoffBalanceSource where
  annihilatorSource :
    G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationSource
  kirchhoffDerivativeBalance : Prop
  kirchhoffDerivativeBalanceWitness :
    kirchhoffDerivativeBalance
  derivativeTraceUsesA12KirchhoffClosure : Prop
  derivativeTraceUsesA12KirchhoffClosureWitness :
    derivativeTraceUsesA12KirchhoffClosure
  status : SpineStatus := .conditional_interface

/-- Maximality of the Kirchhoff boundary condition among isotropic/symmetric
    boundary conditions. -/
structure
    G8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundarySource where
  maximalIsotropicKirchhoffBoundaryCondition : Prop
  maximalIsotropicKirchhoffBoundaryConditionWitness :
    maximalIsotropicKirchhoffBoundaryCondition
  noLargerSymmetricBoundaryCondition : Prop
  noLargerSymmetricBoundaryConditionWitness :
    noLargerSymmetricBoundaryCondition
  status : SpineStatus := .conditional_interface

/-- Reverse inclusion: adjoint-domain traces satisfying crossing agreement and
    Kirchhoff balance are exactly Kirchhoff-domain traces. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource where
  crossingSource :
    G8BookIIICh23FloorNormalizedA15AdjointCrossingTraceAgreementSource
  kirchhoffSource :
    G8BookIIICh23FloorNormalizedA15AdjointKirchhoffBalanceSource
  adjointDomainContainedInKirchhoffDomain : Prop
  adjointDomainContainedInKirchhoffDomainWitness :
    adjointDomainContainedInKirchhoffDomain
  graphH2RegularityRecoveredFromAdjointEquation : Prop
  graphH2RegularityRecoveredWitness :
    graphH2RegularityRecoveredFromAdjointEquation
  status : SpineStatus := .conditional_interface

/-- Exact domain equality for A1.5: the forward inclusion is theorem-backed
    from A1.4, while the reverse inclusion is supplied by the proof stones. -/
def G8BookIIICh23FloorNormalizedA15AdjointDomainEqualsKirchhoffDomain
    (reverse :
      G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15KirchhoffDomainContainedInAdjointDomain ∧
    reverse.adjointDomainContainedInKirchhoffDomain

/-- A reverse-inclusion source combines with the closed forward inclusion to
    prove exact domain equality. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource.domainEquality
    (reverse :
      G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainEqualsKirchhoffDomain
      reverse :=
  ⟨g8BookIIICh23FloorNormalizedA15KirchhoffDomainContainedInAdjointDomain_closed,
    reverse.adjointDomainContainedInKirchhoffDomainWitness⟩

-- ============================================================
-- FULL EXHAUSTION PROOF-STONE SOURCE
-- ============================================================

/-- Full proof-stone source for the A1.5 adjoint-domain exhaustion theorem.

This is the next exact target to discharge from compact graph operator
analysis.  It carries only the A1.5 mathematical payload and no downstream
spectral or RH-facing information. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource where
  traceExistence :
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource
  annihilatorClassification :
    G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationSource
  crossingAgreement :
    G8BookIIICh23FloorNormalizedA15AdjointCrossingTraceAgreementSource
  kirchhoffBalance :
    G8BookIIICh23FloorNormalizedA15AdjointKirchhoffBalanceSource
  maximalBoundary :
    G8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundarySource
  reverseInclusion :
    G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource
  traceSourceAligned :
    annihilatorClassification.traceSource = traceExistence
  crossingUsesAnnihilator :
    crossingAgreement.annihilatorSource = annihilatorClassification
  kirchhoffUsesAnnihilator :
    kirchhoffBalance.annihilatorSource = annihilatorClassification
  reverseUsesCrossing :
    reverseInclusion.crossingSource = crossingAgreement
  reverseUsesKirchhoff :
    reverseInclusion.kirchhoffSource = kirchhoffBalance
  status : SpineStatus := .conditional_interface

/-- Target for the next A1.5 proof-stone theorem. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource

/-- A proof-stone source assembles the exact A1.5 adjoint-domain exhaustion
    input consumed by the already-built maximality adapter. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toAdjointDomainExhaustionInput
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionInput
      g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed where
  closedCancellationSource :=
    g8BookIIICh23FloorNormalizedA15ClosedSelectedA14Cancellation_closed
  symmetricOperator :=
    g8BookIIICh23FloorNormalizedA15KirchhoffSymmetricOperator_closed
  adjointBoundaryTraceExists :=
    source.traceExistence.traceExists
  adjointBoundaryTraceExistsWitness :=
    source.traceExistence.traceExistsWitness
  adjointTraceClassifiedByBoundaryForm :=
    source.annihilatorClassification.annihilatorClassifiedByGreenForm
  adjointTraceClassifiedByBoundaryFormWitness :=
    source.annihilatorClassification.annihilatorClassifiedWitness
  adjointTraceSatisfiesCrossingAgreement :=
    source.crossingAgreement.crossingTraceAgreement
  adjointTraceSatisfiesCrossingAgreementWitness :=
    source.crossingAgreement.crossingTraceAgreementWitness
  adjointTraceSatisfiesKirchhoffBalance :=
    source.kirchhoffBalance.kirchhoffDerivativeBalance
  adjointTraceSatisfiesKirchhoffBalanceWitness :=
    source.kirchhoffBalance.kirchhoffDerivativeBalanceWitness
  maximalIsotropicKirchhoffBoundaryCondition :=
    source.maximalBoundary.maximalIsotropicKirchhoffBoundaryCondition
  maximalIsotropicKirchhoffBoundaryConditionWitness :=
    source.maximalBoundary.maximalIsotropicKirchhoffBoundaryConditionWitness
  kirchhoffDomainContainedInAdjointDomain :=
    G8BookIIICh23FloorNormalizedA15KirchhoffDomainContainedInAdjointDomain
  kirchhoffDomainContainedInAdjointDomainWitness :=
    g8BookIIICh23FloorNormalizedA15KirchhoffDomainContainedInAdjointDomain_closed
  adjointDomainContainedInKirchhoffDomain :=
    source.reverseInclusion.adjointDomainContainedInKirchhoffDomain
  adjointDomainContainedInKirchhoffDomainWitness :=
    source.reverseInclusion.adjointDomainContainedInKirchhoffDomainWitness
  adjointDomainEqualsKirchhoffDomain :=
    G8BookIIICh23FloorNormalizedA15AdjointDomainEqualsKirchhoffDomain
      source.reverseInclusion
  adjointDomainEqualsKirchhoffDomainWitness :=
    source.reverseInclusion.domainEquality
  status := .conditional_interface

/-- A proof-stone source discharges the exact A1.5 adjoint-domain exhaustion
    target. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toAdjointDomainExhaustionTarget
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionTarget :=
  ⟨source.toAdjointDomainExhaustionInput⟩

/-- A proof-stone source discharges the selected-carrier A1.5 maximal
    Kirchhoff self-adjoint extension target. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toMaximalKirchhoffSelfAdjointExtensionTarget
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofAdjointDomainExhaustion
    source.toAdjointDomainExhaustionInput

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Forward inclusion from symmetry alone does not supply the reverse
    inclusion. -/
structure
    G8BookIIICh23FloorNormalizedA15ForwardInclusionWithoutReverse where
  forward :
    G8BookIIICh23FloorNormalizedA15KirchhoffDomainContainedInAdjointDomain
  noReverse :
    ¬ Nonempty
      G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource

theorem
    G8BookIIICh23FloorNormalizedA15ForwardInclusionWithoutReverse.refutesReverse
    (gap :
      G8BookIIICh23FloorNormalizedA15ForwardInclusionWithoutReverse)
    (reverse :
      G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource) :
    False :=
  gap.noReverse ⟨reverse⟩

/-- Missing boundary-form annihilator classification refutes the full proof
    stone source. -/
structure
    G8BookIIICh23FloorNormalizedA15MissingAnnihilatorClassification where
  missing :
    ¬ Nonempty
      G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationSource

theorem
    G8BookIIICh23FloorNormalizedA15MissingAnnihilatorClassification.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15MissingAnnihilatorClassification)
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource) :
    False :=
  gap.missing ⟨source.annihilatorClassification⟩

/-- Missing maximal isotropic Kirchhoff boundary evidence refutes the full
    proof-stone source. -/
structure
    G8BookIIICh23FloorNormalizedA15MissingMaximalBoundary where
  missing :
    ¬ Nonempty
      G8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundarySource

theorem
    G8BookIIICh23FloorNormalizedA15MissingMaximalBoundary.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15MissingMaximalBoundary)
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource) :
    False :=
  gap.missing ⟨source.maximalBoundary⟩

/-- Missing graph-H2 regularity recovery blocks the reverse inclusion. -/
structure
    G8BookIIICh23FloorNormalizedA15MissingGraphH2RegularityRecovery
    (reverse :
      G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource) where
  missing :
    ¬ reverse.graphH2RegularityRecoveredFromAdjointEquation

theorem
    G8BookIIICh23FloorNormalizedA15MissingGraphH2RegularityRecovery.refutes
    {reverse :
      G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource}
    (gap :
      G8BookIIICh23FloorNormalizedA15MissingGraphH2RegularityRecovery
        reverse) :
    False :=
  gap.missing reverse.graphH2RegularityRecoveredWitness

end Tau.BookIII.Bridge
