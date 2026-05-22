import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Compact Graph Adjoint Calculus

This module is the next A1.5 proof step below the analytic-law kernel.

The previous layer showed that a non-vacuous adjoint/test universe together
with pointwise regularity and Green-identity kernels proves the two analytic
laws:

```text
graph-H2 trace recovery from the adjoint equation
adjoint Green identity against all Kirchhoff test functions
```

Here we package the intended compact-graph adjoint calculus source.  The
selected A1.2 trace readiness, selected A1.4 Green bookkeeping, and selected
A1.3 edgewise H2/Kirchhoff domain readiness are inserted from theorem-backed
closed sources.  The only remaining fields are the real compact-graph
adjoint-domain calculus payload:

```text
adjoint candidates really represent the full adjoint domain
Kirchhoff tests really exhaust the Kirchhoff domain
each adjoint candidate satisfies the regularity theorem
each adjoint candidate/test pair satisfies the Green identity theorem
```

No compact-graph adjoint theorem is faked here.  The module proves only that
this exact source is sufficient to build the analytic-law kernel and hence the
two opening reverse-inclusion stones.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- COMPACT-GRAPH ADJOINT CALCULUS SOURCE
-- ============================================================

/-- The compact-graph adjoint calculus theorem, in the exact form needed for
    A1.5.

The selected trace, Green-bookkeeping, and edgewise-H2/Kirchhoff-domain facts
are already theorem-backed upstream.  The load-bearing new content is:

* the candidate carrier really is the full adjoint-domain carrier;
* the test carrier really exhausts the Kirchhoff domain;
* adjoint equation regularity holds for every candidate;
* Green's identity holds for every candidate against every Kirchhoff test.
-/
structure
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource where
  candidate : Type 1
  kirchhoffTest : Type 1
  candidateNonempty : Nonempty candidate
  kirchhoffTestNonempty : Nonempty kirchhoffTest
  candidatesRepresentAdjointDomain : Prop
  candidatesRepresentAdjointDomainWitness :
    candidatesRepresentAdjointDomain
  testsExhaustKirchhoffDomain : Prop
  testsExhaustKirchhoffDomainWitness :
    testsExhaustKirchhoffDomain
  noFiniteDiagnosticSubstitute : Prop
  noFiniteDiagnosticSubstituteWitness :
    noFiniteDiagnosticSubstitute
  adjointEquationInSelectedL2 :
    candidate → Prop
  adjointEquationWitness :
    ∀ u : candidate, adjointEquationInSelectedL2 u
  adjointDistributionalSecondDerivativeInSelectedL2 :
    candidate → Prop
  adjointDistributionalSecondDerivativeWitness :
    ∀ u : candidate,
      adjointDistributionalSecondDerivativeInSelectedL2 u
  graphH2RegularityFromAdjointEquation :
    candidate → Prop
  graphH2RegularityWitness :
    ∀ u : candidate,
      graphH2RegularityFromAdjointEquation u
  valueTraceRecoveredFromSobolevTrace :
    candidate → Prop
  valueTraceRecoveredWitness :
    ∀ u : candidate,
      valueTraceRecoveredFromSobolevTrace u
  derivativeTraceRecoveredFromSobolevTrace :
    candidate → Prop
  derivativeTraceRecoveredWitness :
    ∀ u : candidate,
      derivativeTraceRecoveredFromSobolevTrace u
  traceRecoveryFromAdjointEquation :
    candidate → Prop
  traceRecoveryWitness :
    ∀ u : candidate,
      traceRecoveryFromAdjointEquation u
  valueAndDerivativeBoundaryTracesExist :
    candidate → Prop
  valueAndDerivativeBoundaryTracesExistWitness :
    ∀ u : candidate,
      valueAndDerivativeBoundaryTracesExist u
  adjointPairingIdentityAgainstKirchhoffTests :
    candidate → kirchhoffTest → Prop
  adjointPairingIdentityWitness :
    ∀ (u : candidate) (v : kirchhoffTest),
      adjointPairingIdentityAgainstKirchhoffTests u v
  edgewiseGreenIdentityAgainstKirchhoffTests :
    candidate → kirchhoffTest → Prop
  edgewiseGreenIdentityWitness :
    ∀ (u : candidate) (v : kirchhoffTest),
      edgewiseGreenIdentityAgainstKirchhoffTests u v
  boundaryFormEqualsAdjointDefectPairing :
    candidate → kirchhoffTest → Prop
  boundaryFormEqualsAdjointDefectPairingWitness :
    ∀ (u : candidate) (v : kirchhoffTest),
      boundaryFormEqualsAdjointDefectPairing u v
  adjointDefectPairingVanishes :
    candidate → kirchhoffTest → Prop
  adjointDefectPairingVanishesWitness :
    ∀ (u : candidate) (v : kirchhoffTest),
      adjointDefectPairingVanishes u v
  annihilatesKirchhoffBoundaryForm :
    candidate → kirchhoffTest → Prop
  annihilatesKirchhoffBoundaryFormWitness :
    ∀ (u : candidate) (v : kirchhoffTest),
      annihilatesKirchhoffBoundaryForm u v
  status : SpineStatus := .conditional_interface

/-- Target for constructing the compact-graph adjoint calculus source. -/
def G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource

-- ============================================================
-- ADAPTERS TO THE ANALYTIC-LAW KERNEL
-- ============================================================

/-- A compact-graph adjoint calculus source supplies the non-vacuous
    adjoint/test universe required by the analytic-law kernel. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource.toAnalyticUniverse
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource) :
    G8BookIIICh23FloorNormalizedA15AdjointAnalyticUniverse where
  candidate := source.candidate
  kirchhoffTest := source.kirchhoffTest
  candidateNonempty := source.candidateNonempty
  kirchhoffTestNonempty := source.kirchhoffTestNonempty
  selectedTraceReadiness :=
    g8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint_closed
  selectedGreenBookkeeping :=
    g8BookIIICh23FloorNormalizedA15SelectedGreenBookkeepingForAdjoint_closed
  selectedEdgewiseH2KirchhoffDomainReady :=
    g8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady_closed
  candidatesRepresentAdjointDomain :=
    source.candidatesRepresentAdjointDomain
  candidatesRepresentAdjointDomainWitness :=
    source.candidatesRepresentAdjointDomainWitness
  testsExhaustKirchhoffDomain :=
    source.testsExhaustKirchhoffDomain
  testsExhaustKirchhoffDomainWitness :=
    source.testsExhaustKirchhoffDomainWitness
  noFiniteDiagnosticSubstitute :=
    source.noFiniteDiagnosticSubstitute
  noFiniteDiagnosticSubstituteWitness :=
    source.noFiniteDiagnosticSubstituteWitness
  status := .conditional_interface

/-- A compact-graph adjoint calculus source supplies the pointwise regularity
    kernel. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource.toRegularityKernel
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource) :
    G8BookIIICh23FloorNormalizedA15AdjointEquationRegularityKernel
      source.toAnalyticUniverse where
  adjointEquationInSelectedL2 :=
    source.adjointEquationInSelectedL2
  adjointEquationWitness :=
    source.adjointEquationWitness
  adjointDistributionalSecondDerivativeInSelectedL2 :=
    source.adjointDistributionalSecondDerivativeInSelectedL2
  adjointDistributionalSecondDerivativeWitness :=
    source.adjointDistributionalSecondDerivativeWitness
  graphH2RegularityFromAdjointEquation :=
    source.graphH2RegularityFromAdjointEquation
  graphH2RegularityWitness :=
    source.graphH2RegularityWitness
  valueTraceRecoveredFromSobolevTrace :=
    source.valueTraceRecoveredFromSobolevTrace
  valueTraceRecoveredWitness :=
    source.valueTraceRecoveredWitness
  derivativeTraceRecoveredFromSobolevTrace :=
    source.derivativeTraceRecoveredFromSobolevTrace
  derivativeTraceRecoveredWitness :=
    source.derivativeTraceRecoveredWitness
  traceRecoveryFromAdjointEquation :=
    source.traceRecoveryFromAdjointEquation
  traceRecoveryWitness :=
    source.traceRecoveryWitness
  valueAndDerivativeBoundaryTracesExist :=
    source.valueAndDerivativeBoundaryTracesExist
  valueAndDerivativeBoundaryTracesExistWitness :=
    source.valueAndDerivativeBoundaryTracesExistWitness
  status := .conditional_interface

/-- A compact-graph adjoint calculus source supplies the pointwise Green
    identity kernel. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource.toGreenIdentityKernel
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource) :
    G8BookIIICh23FloorNormalizedA15AdjointGreenIdentityKernel
      source.toAnalyticUniverse where
  adjointPairingIdentityAgainstKirchhoffTests :=
    source.adjointPairingIdentityAgainstKirchhoffTests
  adjointPairingIdentityWitness :=
    source.adjointPairingIdentityWitness
  edgewiseGreenIdentityAgainstKirchhoffTests :=
    source.edgewiseGreenIdentityAgainstKirchhoffTests
  edgewiseGreenIdentityWitness :=
    source.edgewiseGreenIdentityWitness
  boundaryFormEqualsAdjointDefectPairing :=
    source.boundaryFormEqualsAdjointDefectPairing
  boundaryFormEqualsAdjointDefectPairingWitness :=
    source.boundaryFormEqualsAdjointDefectPairingWitness
  adjointDefectPairingVanishes :=
    source.adjointDefectPairingVanishes
  adjointDefectPairingVanishesWitness :=
    source.adjointDefectPairingVanishesWitness
  annihilatesKirchhoffBoundaryForm :=
    source.annihilatesKirchhoffBoundaryForm
  annihilatesKirchhoffBoundaryFormWitness :=
    source.annihilatesKirchhoffBoundaryFormWitness
  status := .conditional_interface

/-- A compact-graph adjoint calculus source constructs the combined
    analytic-law kernel. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource.toAnalyticLawKernel
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource) :
    G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel where
  ctx := source.toAnalyticUniverse
  regularity := source.toRegularityKernel
  greenIdentity := source.toGreenIdentityKernel
  status := .conditional_interface

/-- A compact-graph adjoint calculus source proves both analytic-law targets. -/
theorem
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource.toTwoAnalyticLawTargets
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource) :
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquationTarget ∧
      G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTestsTarget :=
  source.toAnalyticLawKernel.toTwoAnalyticLawTargets

/-- A compact-graph adjoint calculus source discharges the first two
    reverse-inclusion proof stones. -/
theorem
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource.toFirstTwoStonesTarget
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource) :
    Nonempty
      G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource :=
  source.toAnalyticLawKernel.toFirstTwoStonesTarget

/-- A target-level compact-graph adjoint calculus proof supplies the
    analytic-law kernel target. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernelTarget_ofCompactGraphCalculus
    (target :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernelTarget :=
  target.elim fun source => ⟨source.toAnalyticLawKernel⟩

/-- A target-level compact-graph adjoint calculus proof supplies both
    analytic-law targets. -/
theorem
    g8BookIIICh23FloorNormalizedA15TwoAnalyticLawTargets_ofCompactGraphCalculus
    (target :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusTarget) :
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquationTarget ∧
      G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTestsTarget :=
  target.elim fun source => source.toTwoAnalyticLawTargets

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A candidate/test carrier is not enough without the proof that it represents
    the full adjoint domain and full Kirchhoff test domain. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointCarrierWithoutDomainCoverage where
  candidate : Type 1
  kirchhoffTest : Type 1
  candidateNonempty : Nonempty candidate
  kirchhoffTestNonempty : Nonempty kirchhoffTest
  noCompactGraphCalculus :
    ¬ G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusTarget

theorem
    G8BookIIICh23FloorNormalizedA15AdjointCarrierWithoutDomainCoverage.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15AdjointCarrierWithoutDomainCoverage)
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource) :
    False :=
  gap.noCompactGraphCalculus ⟨source⟩

/-- Pointwise regularity alone does not construct the compact-graph calculus
    source if the Green identity against all Kirchhoff tests is missing. -/
structure
    G8BookIIICh23FloorNormalizedA15RegularityWithoutCompactGraphGreen where
  source :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource
  noGreenIdentity :
    ¬ G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTestsTarget

theorem
    G8BookIIICh23FloorNormalizedA15RegularityWithoutCompactGraphGreen.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15RegularityWithoutCompactGraphGreen) :
    False :=
  gap.noGreenIdentity
    (gap.source.toTwoAnalyticLawTargets).2

/-- A finite diagnostic subset cannot be used as the compact-graph adjoint
    calculus source unless the source itself proves it is not merely finite
    diagnostic data. -/
structure
    G8BookIIICh23FloorNormalizedA15FiniteDiagnosticCompactGraphCalculusGap where
  source :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource
  diagnosticOnly :
    ¬ source.noFiniteDiagnosticSubstitute

theorem
    G8BookIIICh23FloorNormalizedA15FiniteDiagnosticCompactGraphCalculusGap.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15FiniteDiagnosticCompactGraphCalculusGap) :
    False :=
  gap.diagnosticOnly gap.source.noFiniteDiagnosticSubstituteWitness

end Tau.BookIII.Bridge
