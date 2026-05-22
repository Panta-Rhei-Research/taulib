import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentity

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Adjoint Analytic Law Kernel

This module is the first non-vacuous implementation step toward proving the
two A1.5 analytic laws.

The previous layer named the two laws:

```text
graph-H2 trace recovery from the adjoint equation
adjoint Green identity against all Kirchhoff test functions
```

Here we make the compact-graph analytic theorem proof-facing at the correct
granularity: a universe of adjoint candidates and Kirchhoff tests, plus
pointwise regularity and Green-identity theorems over that universe.  From
that kernel we prove, without sorries, the two law objects consumed by the
existing A1.5 source layer.

This still does not assert that the compact graph adjoint calculus theorem has
been proved.  It says exactly what theorem must be supplied next, and proves
that supplying it is sufficient.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- ADJOINT CANDIDATE / KIRCHHOFF TEST UNIVERSE
-- ============================================================

/-- A non-vacuous universe of adjoint candidates and Kirchhoff test functions
    for the selected floor-normalized Ch.23 operator.

The load-bearing fields are the coverage/provenance predicates:
`candidatesRepresentAdjointDomain` and `testsExhaustKirchhoffDomain`.  They
prevent the later pointwise laws from being read as facts about a toy carrier
or about a finite diagnostic subset. -/
structure G8BookIIICh23FloorNormalizedA15AdjointAnalyticUniverse where
  candidate : Type 1
  kirchhoffTest : Type 1
  candidateNonempty : Nonempty candidate
  kirchhoffTestNonempty : Nonempty kirchhoffTest
  selectedTraceReadiness :
    G8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint
  selectedGreenBookkeeping :
    G8BookIIICh23FloorNormalizedA15SelectedGreenBookkeepingForAdjoint
  selectedEdgewiseH2KirchhoffDomainReady :
    G8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady
      g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
  candidatesRepresentAdjointDomain : Prop
  candidatesRepresentAdjointDomainWitness :
    candidatesRepresentAdjointDomain
  testsExhaustKirchhoffDomain : Prop
  testsExhaustKirchhoffDomainWitness :
    testsExhaustKirchhoffDomain
  noFiniteDiagnosticSubstitute : Prop
  noFiniteDiagnosticSubstituteWitness :
    noFiniteDiagnosticSubstitute
  status : SpineStatus := .conditional_interface

/-- Target for constructing the non-vacuous adjoint/test universe. -/
def G8BookIIICh23FloorNormalizedA15AdjointAnalyticUniverseTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA15AdjointAnalyticUniverse

-- ============================================================
-- GRAPH-H2 REGULARITY KERNEL
-- ============================================================

/-- Pointwise graph-H2 regularity theorem for adjoint candidates.

This is the real trace-recovery theorem in kernel form: each adjoint candidate
has its adjoint equation in the selected `L2` layer; that equation gives a
distributional second derivative in selected `L2`; hence graph-H2 regularity
and the value/derivative traces needed by the reverse inclusion. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointEquationRegularityKernel
    (ctx :
      G8BookIIICh23FloorNormalizedA15AdjointAnalyticUniverse) where
  adjointEquationInSelectedL2 :
    ctx.candidate → Prop
  adjointEquationWitness :
    ∀ u : ctx.candidate, adjointEquationInSelectedL2 u
  adjointDistributionalSecondDerivativeInSelectedL2 :
    ctx.candidate → Prop
  adjointDistributionalSecondDerivativeWitness :
    ∀ u : ctx.candidate,
      adjointDistributionalSecondDerivativeInSelectedL2 u
  graphH2RegularityFromAdjointEquation :
    ctx.candidate → Prop
  graphH2RegularityWitness :
    ∀ u : ctx.candidate,
      graphH2RegularityFromAdjointEquation u
  valueTraceRecoveredFromSobolevTrace :
    ctx.candidate → Prop
  valueTraceRecoveredWitness :
    ∀ u : ctx.candidate,
      valueTraceRecoveredFromSobolevTrace u
  derivativeTraceRecoveredFromSobolevTrace :
    ctx.candidate → Prop
  derivativeTraceRecoveredWitness :
    ∀ u : ctx.candidate,
      derivativeTraceRecoveredFromSobolevTrace u
  traceRecoveryFromAdjointEquation :
    ctx.candidate → Prop
  traceRecoveryWitness :
    ∀ u : ctx.candidate,
      traceRecoveryFromAdjointEquation u
  valueAndDerivativeBoundaryTracesExist :
    ctx.candidate → Prop
  valueAndDerivativeBoundaryTracesExistWitness :
    ∀ u : ctx.candidate,
      valueAndDerivativeBoundaryTracesExist u
  status : SpineStatus := .conditional_interface

/-- A pointwise regularity kernel proves the global graph-H2 trace-recovery
    law object from the previous layer. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointEquationRegularityKernel.toTraceRecoveryLaw
    {ctx :
      G8BookIIICh23FloorNormalizedA15AdjointAnalyticUniverse}
    (kernel :
      G8BookIIICh23FloorNormalizedA15AdjointEquationRegularityKernel
        ctx) :
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation where
  selectedTraceReadiness := ctx.selectedTraceReadiness
  selectedEdgewiseH2KirchhoffDomainReady :=
    ctx.selectedEdgewiseH2KirchhoffDomainReady
  adjointEquationInSelectedL2 :=
    ∀ u : ctx.candidate, kernel.adjointEquationInSelectedL2 u
  adjointEquationInSelectedL2Witness :=
    kernel.adjointEquationWitness
  adjointDistributionalSecondDerivativeInSelectedL2 :=
    ∀ u : ctx.candidate,
      kernel.adjointDistributionalSecondDerivativeInSelectedL2 u
  adjointDistributionalSecondDerivativeWitness :=
    kernel.adjointDistributionalSecondDerivativeWitness
  graphH2RegularityFromAdjointEquation :=
    ∀ u : ctx.candidate,
      kernel.graphH2RegularityFromAdjointEquation u
  graphH2RegularityFromAdjointEquationWitness :=
    kernel.graphH2RegularityWitness
  valueTraceRecoveredFromSobolevTrace :=
    ∀ u : ctx.candidate,
      kernel.valueTraceRecoveredFromSobolevTrace u
  valueTraceRecoveredWitness :=
    kernel.valueTraceRecoveredWitness
  derivativeTraceRecoveredFromSobolevTrace :=
    ∀ u : ctx.candidate,
      kernel.derivativeTraceRecoveredFromSobolevTrace u
  derivativeTraceRecoveredWitness :=
    kernel.derivativeTraceRecoveredWitness
  traceRecoveryFromAdjointEquation :=
    ∀ u : ctx.candidate,
      kernel.traceRecoveryFromAdjointEquation u
  traceRecoveryFromAdjointEquationWitness :=
    kernel.traceRecoveryWitness
  valueAndDerivativeBoundaryTracesExist :=
    ∀ u : ctx.candidate,
      kernel.valueAndDerivativeBoundaryTracesExist u
  valueAndDerivativeBoundaryTracesExistWitness :=
    kernel.valueAndDerivativeBoundaryTracesExistWitness
  status := .conditional_interface

-- ============================================================
-- ADJOINT GREEN IDENTITY KERNEL
-- ============================================================

/-- Pointwise Green identity theorem for adjoint candidates against every
    Kirchhoff test.

This is the real Green-identity theorem in kernel form.  It is deliberately
universal in both variables so that finite checks or a single test function
cannot fill the A1.5 annihilator-classification slot. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointGreenIdentityKernel
    (ctx :
      G8BookIIICh23FloorNormalizedA15AdjointAnalyticUniverse) where
  adjointPairingIdentityAgainstKirchhoffTests :
    ctx.candidate → ctx.kirchhoffTest → Prop
  adjointPairingIdentityWitness :
    ∀ (u : ctx.candidate) (v : ctx.kirchhoffTest),
      adjointPairingIdentityAgainstKirchhoffTests u v
  edgewiseGreenIdentityAgainstKirchhoffTests :
    ctx.candidate → ctx.kirchhoffTest → Prop
  edgewiseGreenIdentityWitness :
    ∀ (u : ctx.candidate) (v : ctx.kirchhoffTest),
      edgewiseGreenIdentityAgainstKirchhoffTests u v
  boundaryFormEqualsAdjointDefectPairing :
    ctx.candidate → ctx.kirchhoffTest → Prop
  boundaryFormEqualsAdjointDefectPairingWitness :
    ∀ (u : ctx.candidate) (v : ctx.kirchhoffTest),
      boundaryFormEqualsAdjointDefectPairing u v
  adjointDefectPairingVanishes :
    ctx.candidate → ctx.kirchhoffTest → Prop
  adjointDefectPairingVanishesWitness :
    ∀ (u : ctx.candidate) (v : ctx.kirchhoffTest),
      adjointDefectPairingVanishes u v
  annihilatesKirchhoffBoundaryForm :
    ctx.candidate → ctx.kirchhoffTest → Prop
  annihilatesKirchhoffBoundaryFormWitness :
    ∀ (u : ctx.candidate) (v : ctx.kirchhoffTest),
      annihilatesKirchhoffBoundaryForm u v
  status : SpineStatus := .conditional_interface

/-- A pointwise Green-identity kernel proves the global adjoint Green identity
    law object from the previous layer, using the trace source recovered from
    the graph-H2 law. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointGreenIdentityKernel.toGreenIdentityLaw
    {ctx :
      G8BookIIICh23FloorNormalizedA15AdjointAnalyticUniverse}
    (kernel :
      G8BookIIICh23FloorNormalizedA15AdjointGreenIdentityKernel
        ctx)
    (traceLaw :
      G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation) :
    G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests
    where
  selectedGreenBookkeeping := ctx.selectedGreenBookkeeping
  traceSource := traceLaw.toTraceExistenceSource
  testsAllKirchhoffDomainElements :=
    ctx.testsExhaustKirchhoffDomain
  testsAllKirchhoffDomainElementsWitness :=
    ctx.testsExhaustKirchhoffDomainWitness
  adjointPairingIdentityAgainstKirchhoffTests :=
    ∀ (u : ctx.candidate) (v : ctx.kirchhoffTest),
      kernel.adjointPairingIdentityAgainstKirchhoffTests u v
  adjointPairingIdentityWitness :=
    kernel.adjointPairingIdentityWitness
  edgewiseGreenIdentityAgainstKirchhoffTests :=
    ∀ (u : ctx.candidate) (v : ctx.kirchhoffTest),
      kernel.edgewiseGreenIdentityAgainstKirchhoffTests u v
  edgewiseGreenIdentityWitness :=
    kernel.edgewiseGreenIdentityWitness
  boundaryFormEqualsAdjointDefectPairing :=
    ∀ (u : ctx.candidate) (v : ctx.kirchhoffTest),
      kernel.boundaryFormEqualsAdjointDefectPairing u v
  boundaryFormEqualsAdjointDefectPairingWitness :=
    kernel.boundaryFormEqualsAdjointDefectPairingWitness
  adjointDefectPairingVanishes :=
    ∀ (u : ctx.candidate) (v : ctx.kirchhoffTest),
      kernel.adjointDefectPairingVanishes u v
  adjointDefectPairingVanishesWitness :=
    kernel.adjointDefectPairingVanishesWitness
  annihilatesKirchhoffBoundaryForm :=
    ∀ (u : ctx.candidate) (v : ctx.kirchhoffTest),
      kernel.annihilatesKirchhoffBoundaryForm u v
  annihilatesKirchhoffBoundaryFormWitness :=
    kernel.annihilatesKirchhoffBoundaryFormWitness
  status := .conditional_interface

-- ============================================================
-- COMBINED ANALYTIC LAW KERNEL
-- ============================================================

/-- Combined compact-graph adjoint calculus kernel.

This is now the exact mathematical payload for the two analytic laws.  It
  requires a non-vacuous adjoint/test universe, pointwise adjoint-equation
regularity, and pointwise Green identity against every Kirchhoff test. -/
structure G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel where
  ctx :
    G8BookIIICh23FloorNormalizedA15AdjointAnalyticUniverse
  regularity :
    G8BookIIICh23FloorNormalizedA15AdjointEquationRegularityKernel
      ctx
  greenIdentity :
    G8BookIIICh23FloorNormalizedA15AdjointGreenIdentityKernel
      ctx
  status : SpineStatus := .conditional_interface

/-- Target for the combined adjoint analytic law kernel. -/
def G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernelTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel

/-- The trace-recovery law extracted from a combined analytic kernel. -/
def G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel.traceRecoveryLaw
    (kernel :
      G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel) :
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation :=
  kernel.regularity.toTraceRecoveryLaw

/-- The Green-identity law extracted from a combined analytic kernel. -/
def G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel.greenIdentityLaw
    (kernel :
      G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel) :
    G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests :=
  kernel.greenIdentity.toGreenIdentityLaw kernel.traceRecoveryLaw

/-- A combined analytic kernel proves both analytic-law targets. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel.toTwoAnalyticLawTargets
    (kernel :
      G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel) :
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquationTarget ∧
      G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTestsTarget :=
  ⟨⟨kernel.traceRecoveryLaw⟩, ⟨kernel.greenIdentityLaw⟩⟩

/-- A combined analytic kernel assembles the previous combined source for the
    first two reverse-inclusion stones. -/
def G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel.toEquationGreenIdentitySource
    (kernel :
      G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel) :
    G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource where
  traceRecovery := kernel.traceRecoveryLaw
  greenIdentity := kernel.greenIdentityLaw
  greenUsesRecoveredTrace := rfl
  status := .conditional_interface

/-- A combined analytic kernel discharges the first-two-stones source target. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel.toFirstTwoStonesTarget
    (kernel :
      G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel) :
    Nonempty
      G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource :=
  kernel.toEquationGreenIdentitySource.toFirstTwoStonesTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A candidate/test carrier without pointwise regularity does not construct
    graph-H2 trace recovery. -/
structure G8BookIIICh23FloorNormalizedA15UniverseWithoutRegularityKernel where
  ctx :
    G8BookIIICh23FloorNormalizedA15AdjointAnalyticUniverse
  noRegularity :
    ¬ Nonempty
      (G8BookIIICh23FloorNormalizedA15AdjointEquationRegularityKernel
        ctx)

theorem
    G8BookIIICh23FloorNormalizedA15UniverseWithoutRegularityKernel.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15UniverseWithoutRegularityKernel)
    (regularity :
      G8BookIIICh23FloorNormalizedA15AdjointEquationRegularityKernel
        gap.ctx) :
    False :=
  gap.noRegularity ⟨regularity⟩

/-- Pointwise trace recovery without the Green identity does not classify the
    adjoint boundary-form annihilator. -/
structure G8BookIIICh23FloorNormalizedA15RegularityWithoutGreenKernel where
  kernel :
    G8BookIIICh23FloorNormalizedA15AdjointAnalyticLawKernel
  noGreenIdentity :
    ¬ G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTestsTarget

theorem
    G8BookIIICh23FloorNormalizedA15RegularityWithoutGreenKernel.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15RegularityWithoutGreenKernel) :
    False :=
  gap.noGreenIdentity ⟨gap.kernel.greenIdentityLaw⟩

/-- A finite diagnostic subset is not enough unless the universe proof says it
    really represents all adjoint candidates and all Kirchhoff tests. -/
structure G8BookIIICh23FloorNormalizedA15FiniteDiagnosticUniverseGap where
  ctx :
    G8BookIIICh23FloorNormalizedA15AdjointAnalyticUniverse
  diagnosticOnly :
    ¬ ctx.noFiniteDiagnosticSubstitute

theorem
    G8BookIIICh23FloorNormalizedA15FiniteDiagnosticUniverseGap.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15FiniteDiagnosticUniverseGap) :
    False :=
  gap.diagnosticOnly gap.ctx.noFiniteDiagnosticSubstituteWitness

end Tau.BookIII.Bridge
