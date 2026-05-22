import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStones

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Adjoint Trace/Annihilator Classification

This module begins the reverse-inclusion proof work for A1.5.

The previous proof-stone module named the two first hard stones:

```text
adjoint boundary traces exist
boundary-form annihilator classification
```

Here we split those stones one level further.  The selected A1.2 trace theory
and selected A1.4 Green bookkeeping are already theorem-backed.  What remains
mathematical is the adjoint-equation regularity and the adjoint pairing law:

```text
adjoint equation recovers graph-H2 traces
  + selected A1.2 Sobolev trace readiness
  -> adjoint boundary trace existence

adjoint pairing identity against all Kirchhoff tests
  + selected A1.4 Green bookkeeping
  + adjoint traces
  -> boundary-form annihilator classification
```

No crossing agreement, Kirchhoff balance, maximal boundary condition,
compact-resolvent, point-spectrum, A3 actual-`xi`, or RH-facing claim is made
here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CLOSED SELECTED TRACE/GREEN INPUTS
-- ============================================================

/-- The selected A1.2 Sobolev trace package available for adjoint-domain
    trace recovery. -/
def
    G8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint :
    Prop :=
  G8BookIIICh23FloorNormalizedA12SobolevTraceReadiness
    g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed

/-- The selected A1.2 trace package is theorem-backed. -/
theorem
    g8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint_closed :
    G8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint :=
  g8BookIIICh23FloorNormalizedA12SobolevTraceReadiness_closed

/-- The selected A1.4 Green bookkeeping available for adjoint pairing
    classification. -/
def
    G8BookIIICh23FloorNormalizedA15SelectedGreenBookkeepingForAdjoint :
    Prop :=
  G8BookIIICh23FloorNormalizedA14EdgewiseGreenBookkeeping
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed

/-- The selected A1.4 Green bookkeeping is theorem-backed. -/
theorem
    g8BookIIICh23FloorNormalizedA15SelectedGreenBookkeepingForAdjoint_closed :
    G8BookIIICh23FloorNormalizedA15SelectedGreenBookkeepingForAdjoint :=
  g8BookIIICh23FloorNormalizedA14EdgewiseGreenBookkeeping_closed

-- ============================================================
-- ADJOINT TRACE EXISTENCE
-- ============================================================

/-- Proof-carrying input for recovering boundary traces of an adjoint-domain
    candidate.

The load-bearing analytic step is `traceRecoveryFromAdjointEquation`: it is
the graph-operator statement that the adjoint equation recovers enough
edgewise regularity to apply the selected A1.2 Sobolev trace package. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointTraceRegularityInput where
  selectedTraceReadiness :
    G8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint
  adjointEquationInSelectedL2 : Prop
  adjointEquationInSelectedL2Witness :
    adjointEquationInSelectedL2
  graphH2RegularityFromAdjointEquation : Prop
  graphH2RegularityFromAdjointEquationWitness :
    graphH2RegularityFromAdjointEquation
  traceRecoveryFromAdjointEquation : Prop
  traceRecoveryFromAdjointEquationWitness :
    traceRecoveryFromAdjointEquation
  valueAndDerivativeBoundaryTracesExist : Prop
  valueAndDerivativeBoundaryTracesExistWitness :
    valueAndDerivativeBoundaryTracesExist
  status : SpineStatus := .conditional_interface

/-- The exact trace-existence predicate proved from adjoint-equation
    regularity plus selected A1.2 trace readiness. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceFromRegularity
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointTraceRegularityInput) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint ∧
    input.adjointEquationInSelectedL2 ∧
    input.graphH2RegularityFromAdjointEquation ∧
    input.traceRecoveryFromAdjointEquation ∧
    input.valueAndDerivativeBoundaryTracesExist

/-- Adjoint trace regularity input supplies the first proof stone:
    adjoint boundary traces exist. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointTraceRegularityInput.traceExistence
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointTraceRegularityInput) :
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceFromRegularity
      input :=
  ⟨input.selectedTraceReadiness,
    input.adjointEquationInSelectedL2Witness,
    input.graphH2RegularityFromAdjointEquationWitness,
    input.traceRecoveryFromAdjointEquationWitness,
    input.valueAndDerivativeBoundaryTracesExistWitness⟩

/-- Convert the trace-regularity input into the existing A1.5 adjoint trace
    existence source. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointTraceRegularityInput.toTraceExistenceSource
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointTraceRegularityInput) :
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource where
  traceExists :=
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceFromRegularity
      input
  traceExistsWitness := input.traceExistence
  traceCompatibleWithSelectedA12SobolevTheory :=
    G8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint
  traceCompatibleWitness :=
    g8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint_closed
  status := .conditional_interface

/-- Target for the first A1.5 reverse-inclusion stone. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointTraceExistenceRegularityTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA15AdjointTraceRegularityInput

/-- A regularity input discharges the existing trace-existence source target. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointTraceExistenceSource_ofRegularity
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointTraceRegularityInput) :
    Nonempty
      G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource :=
  ⟨input.toTraceExistenceSource⟩

-- ============================================================
-- BOUNDARY-FORM ANNIHILATOR CLASSIFICATION
-- ============================================================

/-- Proof-carrying input for classifying adjoint traces as annihilators of the
    Kirchhoff boundary form.

This is still upstream of crossing agreement and Kirchhoff balance: it only
proves that the adjoint trace lies in the boundary annihilator of all
Kirchhoff test traces. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput where
  traceSource :
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource
  selectedGreenBookkeeping :
    G8BookIIICh23FloorNormalizedA15SelectedGreenBookkeepingForAdjoint
  adjointPairingIdentityAgainstKirchhoffTests : Prop
  adjointPairingIdentityWitness :
    adjointPairingIdentityAgainstKirchhoffTests
  edgewiseGreenIdentityAgainstKirchhoffTests : Prop
  edgewiseGreenIdentityWitness :
    edgewiseGreenIdentityAgainstKirchhoffTests
  boundaryFormEqualsAdjointDefectPairing : Prop
  boundaryFormEqualsAdjointDefectPairingWitness :
    boundaryFormEqualsAdjointDefectPairing
  annihilatesKirchhoffBoundaryForm : Prop
  annihilatesKirchhoffBoundaryFormWitness :
    annihilatesKirchhoffBoundaryForm
  testsAllKirchhoffDomainElements : Prop
  testsAllKirchhoffDomainElementsWitness :
    testsAllKirchhoffDomainElements
  status : SpineStatus := .conditional_interface

/-- The exact annihilator-classification predicate produced from the adjoint
    pairing law and selected A1.4 Green bookkeeping. -/
def
    G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassified
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput) :
    Prop :=
  input.traceSource.traceExists ∧
    G8BookIIICh23FloorNormalizedA15SelectedGreenBookkeepingForAdjoint ∧
    input.adjointPairingIdentityAgainstKirchhoffTests ∧
    input.edgewiseGreenIdentityAgainstKirchhoffTests ∧
    input.boundaryFormEqualsAdjointDefectPairing ∧
    input.annihilatesKirchhoffBoundaryForm

/-- The Green/adjoint pairing input proves boundary-form annihilator
    classification. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput.annihilatorClassified
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput) :
    G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassified
      input :=
  ⟨input.traceSource.traceExistsWitness,
    input.selectedGreenBookkeeping,
    input.adjointPairingIdentityWitness,
    input.edgewiseGreenIdentityWitness,
    input.boundaryFormEqualsAdjointDefectPairingWitness,
    input.annihilatesKirchhoffBoundaryFormWitness⟩

/-- Convert the Green/adjoint pairing input into the existing A1.5
    boundary-form annihilator classification source. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput.toAnnihilatorClassificationSource
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput) :
    G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationSource where
  traceSource := input.traceSource
  annihilatorClassifiedByGreenForm :=
    G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassified
      input
  annihilatorClassifiedWitness := input.annihilatorClassified
  testsAllKirchhoffDomainElements :=
    input.testsAllKirchhoffDomainElements
  testsAllKirchhoffDomainElementsWitness :=
    input.testsAllKirchhoffDomainElementsWitness
  status := .conditional_interface

/-- Target for the second A1.5 reverse-inclusion stone. -/
def
    G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput

/-- A Green/adjoint pairing input discharges the existing annihilator
    classification source target. -/
theorem
    g8BookIIICh23FloorNormalizedA15AnnihilatorClassificationSource_ofGreenInput
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput) :
    Nonempty
      G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationSource :=
  ⟨input.toAnnihilatorClassificationSource⟩

-- ============================================================
-- COMBINED FIRST-TWO-STONES PACKAGE
-- ============================================================

/-- Combined proof package for the first two reverse-inclusion stones:
    trace existence and boundary-form annihilator classification. -/
structure
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource where
  traceInput :
    G8BookIIICh23FloorNormalizedA15AdjointTraceRegularityInput
  traceSource :
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource
  annihilatorInput :
    G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput
  annihilatorSource :
    G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationSource
  traceSourceFromInput :
    traceSource = traceInput.toTraceExistenceSource
  annihilatorSourceFromInput :
    annihilatorSource =
      annihilatorInput.toAnnihilatorClassificationSource
  annihilatorUsesTraceSource :
    annihilatorInput.traceSource = traceSource
  status : SpineStatus := .conditional_interface

/-- A trace input and a compatible Green/annihilator input assemble the first
    two A1.5 proof stones. -/
def
    g8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource_ofInputs
    (traceInput :
      G8BookIIICh23FloorNormalizedA15AdjointTraceRegularityInput)
    (greenInput :
      G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput)
    (hTrace :
      greenInput.traceSource =
        traceInput.toTraceExistenceSource) :
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource where
  traceInput := traceInput
  traceSource := traceInput.toTraceExistenceSource
  annihilatorInput := greenInput
  annihilatorSource := greenInput.toAnnihilatorClassificationSource
  traceSourceFromInput := rfl
  annihilatorSourceFromInput := rfl
  annihilatorUsesTraceSource := hTrace
  status := .conditional_interface

/-- The combined first-two-stones package exposes the trace-existence source. -/
def
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource.toTraceExistenceSource
    (source :
      G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource :=
  source.traceSource

/-- The combined first-two-stones package exposes the annihilator
    classification source. -/
def
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource.toAnnihilatorClassificationSource
    (source :
      G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource) :
    G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationSource :=
  source.annihilatorSource

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Selected A1.2 trace readiness alone does not supply adjoint trace
    existence; the adjoint-equation regularity/recovery input is still needed.
-/
structure
    G8BookIIICh23FloorNormalizedA15TraceReadinessWithoutAdjointRecovery where
  selectedTraceReadiness :
    G8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint
  noAdjointRegularityInput :
    ¬ Nonempty
      G8BookIIICh23FloorNormalizedA15AdjointTraceRegularityInput

theorem
    G8BookIIICh23FloorNormalizedA15TraceReadinessWithoutAdjointRecovery.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15TraceReadinessWithoutAdjointRecovery)
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointTraceRegularityInput) :
    False :=
  gap.noAdjointRegularityInput ⟨input⟩

/-- Trace existence alone does not supply boundary-form annihilator
    classification. -/
structure
    G8BookIIICh23FloorNormalizedA15TraceExistenceWithoutAnnihilatorLaw where
  traceSource :
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource
  noGreenAnnihilatorInput :
    ¬ Nonempty
      G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput

theorem
    G8BookIIICh23FloorNormalizedA15TraceExistenceWithoutAnnihilatorLaw.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15TraceExistenceWithoutAnnihilatorLaw)
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput) :
    False :=
  gap.noGreenAnnihilatorInput ⟨input⟩

/-- Missing the adjoint pairing identity blocks the annihilator input. -/
structure
    G8BookIIICh23FloorNormalizedA15MissingAdjointPairingIdentity where
  missing :
    ¬ Nonempty
      G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput

theorem
    G8BookIIICh23FloorNormalizedA15MissingAdjointPairingIdentity.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15MissingAdjointPairingIdentity)
    (input :
      G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput) :
    False :=
  gap.missing ⟨input⟩

end Tau.BookIII.Bridge
