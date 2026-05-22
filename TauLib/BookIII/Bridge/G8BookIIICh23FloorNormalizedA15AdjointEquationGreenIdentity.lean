import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15AdjointTraceAnnihilatorClassification

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Adjoint Equation / Green Identity

This module is the next A1.5 reverse-inclusion layer.  It isolates the two
analytic facts needed to populate the first two proof stones:

```text
graph-H2 trace recovery from the adjoint equation
adjoint Green identity against all Kirchhoff test functions
```

The selected A1.2 trace readiness and selected A1.4 Green bookkeeping are
already theorem-backed.  This file therefore proves the no-sorry adapters:

```text
trace recovery law -> adjoint trace regularity input
Green identity law -> adjoint Green annihilator input
both laws -> trace/annihilator classification source
```

The laws themselves remain proof-carrying mathematical inputs unless and until
the compact graph adjoint-regularity theorem is formalized.  No crossing
agreement, Kirchhoff balance, maximal isotropic boundary, compact resolvent,
point spectrum, A3 actual-`xi`, or RH-facing statement is proved here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- GRAPH-H2 TRACE RECOVERY FROM THE ADJOINT EQUATION
-- ============================================================

/-- The exact analytic law needed to recover boundary traces for adjoint
    candidates.

This is not merely the already-closed A1.2 trace theorem.  It is the missing
regularity theorem saying that a selected adjoint-domain representative with
`H_L^* u` in the selected `L2` output has edgewise graph-H2 regularity and
therefore has the value and derivative traces needed by Green's identity. -/
structure
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation where
  selectedTraceReadiness :
    G8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint
  selectedEdgewiseH2KirchhoffDomainReady :
    G8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady
      g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
  adjointEquationInSelectedL2 : Prop
  adjointEquationInSelectedL2Witness :
    adjointEquationInSelectedL2
  adjointDistributionalSecondDerivativeInSelectedL2 : Prop
  adjointDistributionalSecondDerivativeWitness :
    adjointDistributionalSecondDerivativeInSelectedL2
  graphH2RegularityFromAdjointEquation : Prop
  graphH2RegularityFromAdjointEquationWitness :
    graphH2RegularityFromAdjointEquation
  valueTraceRecoveredFromSobolevTrace : Prop
  valueTraceRecoveredWitness :
    valueTraceRecoveredFromSobolevTrace
  derivativeTraceRecoveredFromSobolevTrace : Prop
  derivativeTraceRecoveredWitness :
    derivativeTraceRecoveredFromSobolevTrace
  traceRecoveryFromAdjointEquation : Prop
  traceRecoveryFromAdjointEquationWitness :
    traceRecoveryFromAdjointEquation
  valueAndDerivativeBoundaryTracesExist : Prop
  valueAndDerivativeBoundaryTracesExistWitness :
    valueAndDerivativeBoundaryTracesExist
  status : SpineStatus := .conditional_interface

/-- Target for closing the graph-H2 trace-recovery law. -/
def
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquationTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation

/-- A graph-H2 trace-recovery law supplies the trace-regularity input consumed
    by the existing trace-existence adapter. -/
def
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation.toTraceRegularityInput
    (law :
      G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation) :
    G8BookIIICh23FloorNormalizedA15AdjointTraceRegularityInput where
  selectedTraceReadiness := law.selectedTraceReadiness
  adjointEquationInSelectedL2 :=
    law.adjointEquationInSelectedL2
  adjointEquationInSelectedL2Witness :=
    law.adjointEquationInSelectedL2Witness
  graphH2RegularityFromAdjointEquation :=
    law.graphH2RegularityFromAdjointEquation
  graphH2RegularityFromAdjointEquationWitness :=
    law.graphH2RegularityFromAdjointEquationWitness
  traceRecoveryFromAdjointEquation :=
    law.traceRecoveryFromAdjointEquation
  traceRecoveryFromAdjointEquationWitness :=
    law.traceRecoveryFromAdjointEquationWitness
  valueAndDerivativeBoundaryTracesExist :=
    law.valueAndDerivativeBoundaryTracesExist
  valueAndDerivativeBoundaryTracesExistWitness :=
    law.valueAndDerivativeBoundaryTracesExistWitness
  status := .conditional_interface

/-- The graph-H2 trace-recovery law discharges the trace-existence source
    surface. -/
def
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation.toTraceExistenceSource
    (law :
      G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation) :
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource :=
  law.toTraceRegularityInput.toTraceExistenceSource

-- ============================================================
-- ADJOINT GREEN IDENTITY AGAINST KIRCHHOFF TESTS
-- ============================================================

/-- The exact analytic Green identity needed to classify adjoint traces as
    boundary-form annihilators.

This is stronger than selected A1.4 symmetry.  A1.4 says Kirchhoff-domain test
functions cancel with Kirchhoff-domain inputs.  This law says an adjoint
candidate paired against every Kirchhoff test function has the Green defect
represented exactly by the boundary form, and the adjoint definition forces
that defect to vanish. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests
    where
  selectedGreenBookkeeping :
    G8BookIIICh23FloorNormalizedA15SelectedGreenBookkeepingForAdjoint
  traceSource :
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource
  testsAllKirchhoffDomainElements : Prop
  testsAllKirchhoffDomainElementsWitness :
    testsAllKirchhoffDomainElements
  adjointPairingIdentityAgainstKirchhoffTests : Prop
  adjointPairingIdentityWitness :
    adjointPairingIdentityAgainstKirchhoffTests
  edgewiseGreenIdentityAgainstKirchhoffTests : Prop
  edgewiseGreenIdentityWitness :
    edgewiseGreenIdentityAgainstKirchhoffTests
  boundaryFormEqualsAdjointDefectPairing : Prop
  boundaryFormEqualsAdjointDefectPairingWitness :
    boundaryFormEqualsAdjointDefectPairing
  adjointDefectPairingVanishes : Prop
  adjointDefectPairingVanishesWitness :
    adjointDefectPairingVanishes
  annihilatesKirchhoffBoundaryForm : Prop
  annihilatesKirchhoffBoundaryFormWitness :
    annihilatesKirchhoffBoundaryForm
  status : SpineStatus := .conditional_interface

/-- Target for closing the adjoint Green identity law. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTestsTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests

/-- An adjoint Green identity law supplies the Green-annihilator input
    consumed by the existing annihilator classification adapter. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests.toGreenAnnihilatorInput
    (law :
      G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests) :
    G8BookIIICh23FloorNormalizedA15AdjointGreenAnnihilatorInput where
  traceSource := law.traceSource
  selectedGreenBookkeeping := law.selectedGreenBookkeeping
  adjointPairingIdentityAgainstKirchhoffTests :=
    law.adjointPairingIdentityAgainstKirchhoffTests
  adjointPairingIdentityWitness :=
    law.adjointPairingIdentityWitness
  edgewiseGreenIdentityAgainstKirchhoffTests :=
    law.edgewiseGreenIdentityAgainstKirchhoffTests
  edgewiseGreenIdentityWitness :=
    law.edgewiseGreenIdentityWitness
  boundaryFormEqualsAdjointDefectPairing :=
    law.boundaryFormEqualsAdjointDefectPairing
  boundaryFormEqualsAdjointDefectPairingWitness :=
    law.boundaryFormEqualsAdjointDefectPairingWitness
  annihilatesKirchhoffBoundaryForm :=
    law.annihilatesKirchhoffBoundaryForm
  annihilatesKirchhoffBoundaryFormWitness :=
    law.annihilatesKirchhoffBoundaryFormWitness
  testsAllKirchhoffDomainElements :=
    law.testsAllKirchhoffDomainElements
  testsAllKirchhoffDomainElementsWitness :=
    law.testsAllKirchhoffDomainElementsWitness
  status := .conditional_interface

/-- The adjoint Green identity law discharges the annihilator-classification
    source surface. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests.toAnnihilatorClassificationSource
    (law :
      G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests) :
    G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationSource :=
  law.toGreenAnnihilatorInput.toAnnihilatorClassificationSource

-- ============================================================
-- COMBINED PAYLOAD SOURCE
-- ============================================================

/-- Combined source for the two A1.5 analytic payloads at the start of the
    reverse inclusion. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource where
  traceRecovery :
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation
  greenIdentity :
    G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests
  greenUsesRecoveredTrace :
    greenIdentity.traceSource =
      traceRecovery.toTraceExistenceSource
  status : SpineStatus := .conditional_interface

/-- Target for the combined graph-H2 recovery plus Green identity source. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentityTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource

/-- The combined source produces the previously defined first-two-stones
    package. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource.toTraceAnnihilatorClassificationSource
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource) :
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource :=
  g8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource_ofInputs
    source.traceRecovery.toTraceRegularityInput
    source.greenIdentity.toGreenAnnihilatorInput
    (by
      simpa [
        G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests.toGreenAnnihilatorInput,
        G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation.toTraceExistenceSource
      ] using source.greenUsesRecoveredTrace)

/-- The combined source exposes the trace-existence source. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource.toTraceExistenceSource
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource) :
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource :=
  source.toTraceAnnihilatorClassificationSource.toTraceExistenceSource

/-- The combined source exposes the boundary-form annihilator classification
    source. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource.toAnnihilatorClassificationSource
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource) :
    G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationSource :=
  source.toTraceAnnihilatorClassificationSource.toAnnihilatorClassificationSource

/-- A combined source discharges the existing trace/annihilator classification
    source target. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource.toFirstTwoStonesTarget
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource) :
    Nonempty
      G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource :=
  ⟨source.toTraceAnnihilatorClassificationSource⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A selected graph-H2/Kirchhoff domain theorem does not by itself recover
    adjoint traces; the adjoint equation regularity law is still needed. -/
structure
    G8BookIIICh23FloorNormalizedA15SelectedH2WithoutAdjointRecovery where
  selectedEdgewiseH2KirchhoffDomainReady :
    G8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady
      g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
  noTraceRecovery :
    ¬ G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquationTarget

theorem
    G8BookIIICh23FloorNormalizedA15SelectedH2WithoutAdjointRecovery.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15SelectedH2WithoutAdjointRecovery)
    (law :
      G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation) :
    False :=
  gap.noTraceRecovery ⟨law⟩

/-- A1.4 Green bookkeeping does not by itself classify adjoint-domain
    boundary annihilators; the adjoint pairing identity is still needed. -/
structure
    G8BookIIICh23FloorNormalizedA15GreenBookkeepingWithoutAdjointPairing where
  selectedGreenBookkeeping :
    G8BookIIICh23FloorNormalizedA15SelectedGreenBookkeepingForAdjoint
  noAdjointPairingGreenIdentity :
    ¬ G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTestsTarget

theorem
    G8BookIIICh23FloorNormalizedA15GreenBookkeepingWithoutAdjointPairing.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15GreenBookkeepingWithoutAdjointPairing)
    (law :
      G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests) :
    False :=
  gap.noAdjointPairingGreenIdentity ⟨law⟩

/-- Trace recovery without the Green identity still does not produce the
    annihilator classification needed by reverse inclusion. -/
structure
    G8BookIIICh23FloorNormalizedA15TraceRecoveryWithoutGreenIdentity where
  traceRecovery :
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation
  noCombinedSource :
    ¬ G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentityTarget

theorem
    G8BookIIICh23FloorNormalizedA15TraceRecoveryWithoutGreenIdentity.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15TraceRecoveryWithoutGreenIdentity)
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource) :
    False :=
  gap.noCombinedSource ⟨source⟩

end Tau.BookIII.Bridge
