import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15FiniteTraceBoundaryForcingConstruction

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Compact Graph Finite Trace Readout

This module moves the remaining A1.5 reverse-inclusion payload one step closer
to the compact graph operator theorem.

The previous boundary-forcing construction proved:

```text
raw finite trace representation of adjoint candidates
  -> finite boundary algebra forces Kirchhoff traces
  -> reverse inclusion
  -> A1.5 maximal Kirchhoff self-adjointness target
```

Here we prove the adapter from the compact-graph adjoint calculus source plus
an exact finite boundary-trace readout:

```text
compact graph adjoint calculus
  + finite trace readout of each adjoint candidate
  + Green/annihilator law for that readout
  -> raw finite trace representation
```

The remaining mathematical theorem is therefore no longer the whole A1.5
chain.  It is the finite endpoint-trace readout theorem for the compact graph
adjoint domain, with exact annihilator membership against all Kirchhoff tests.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- TRACE/ANNIHILATOR ROUTE FROM COMPACT GRAPH CALCULUS
-- ============================================================

/-- A compact-graph adjoint calculus source supplies the trace/annihilator
    payload route used by the finite-trace layer. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource.toTraceAnnihilatorPayloadRouteSource
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource) :
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource :=
  let firstTwo :=
    source.toAnalyticLawKernel.toEquationGreenIdentitySource
      |>.toTraceAnnihilatorClassificationSource
  { traceExistence := firstTwo.traceSource
    annihilatorClassification := firstTwo.annihilatorSource
    traceSourceAligned := by
      rw [firstTwo.annihilatorSourceFromInput]
      exact firstTwo.annihilatorUsesTraceSource
    noFiniteDiagnosticTestSubset :=
      source.testsExhaustKirchhoffDomain ∧
        source.noFiniteDiagnosticSubstitute
    noFiniteDiagnosticTestSubsetWitness :=
      ⟨source.testsExhaustKirchhoffDomainWitness,
        source.noFiniteDiagnosticSubstituteWitness⟩
    status := .conditional_interface }

-- ============================================================
-- FINITE TRACE READOUT SOURCE
-- ============================================================

/-- Exact finite boundary-trace readout theorem for compact-graph adjoint
    candidates.

The `boundaryTrace` field is the actual endpoint-trace extraction target.
The load-bearing theorem is `finiteTraceAnnihilatesKirchhoff`: it says the
readout is in the Kirchhoff annihilator for every adjoint candidate, using the
compact-graph Green identity against the full Kirchhoff test universe.
-/
structure
    G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutSource
    where
  calculus :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource
  boundaryTrace :
    calculus.candidate ->
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace
  finiteTraceAnnihilatesKirchhoff :
    ∀ candidate : calculus.candidate,
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
        (boundaryTrace candidate)
  boundaryTraceExtractsRecoveredTrace : Prop
  boundaryTraceExtractsRecoveredTraceWitness :
    boundaryTraceExtractsRecoveredTrace
  boundaryTraceGreenPairingRealizesAnnihilator : Prop
  boundaryTraceGreenPairingRealizesAnnihilatorWitness :
    boundaryTraceGreenPairingRealizesAnnihilator
  finiteTraceReadoutIsGlobal : Prop
  finiteTraceReadoutIsGlobalWitness :
    finiteTraceReadoutIsGlobal
  finiteTraceReadoutUsesAllKirchhoffTests : Prop
  finiteTraceReadoutUsesAllKirchhoffTestsWitness :
    finiteTraceReadoutUsesAllKirchhoffTests
  status : SpineStatus := .conditional_interface

/-- Target for the exact compact-graph finite trace readout theorem. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutSource

/-- A compact-graph finite trace readout supplies the raw finite trace
    representation consumed by the boundary-forcing construction. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutSource.toRawFiniteTraceAdjointRepresentationSource
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutSource) :
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource
    where
  traceAnnihilator :=
    source.calculus.toTraceAnnihilatorPayloadRouteSource
  adjointCandidateCarrier :=
    source.calculus.candidate
  adjointCandidateNonempty :=
    source.calculus.candidateNonempty
  boundaryTrace :=
    source.boundaryTrace
  traceAnnihilatesKirchhoff :=
    source.finiteTraceAnnihilatesKirchhoff
  representsAllAdjointBoundaryTraces :=
    source.calculus.candidatesRepresentAdjointDomain ∧
      source.finiteTraceReadoutIsGlobal
  representsAllAdjointBoundaryTracesWitness :=
    ⟨source.calculus.candidatesRepresentAdjointDomainWitness,
      source.finiteTraceReadoutIsGlobalWitness⟩
  tracesComeFromAdjointTraceExistence :=
    source.boundaryTraceExtractsRecoveredTrace ∧
      (∀ candidate : source.calculus.candidate,
        source.calculus.valueAndDerivativeBoundaryTracesExist candidate)
  tracesComeFromAdjointTraceExistenceWitness :=
    ⟨source.boundaryTraceExtractsRecoveredTraceWitness,
      source.calculus.valueAndDerivativeBoundaryTracesExistWitness⟩
  traceRepresentationUsesGreenAnnihilatorClassification :=
    source.boundaryTraceGreenPairingRealizesAnnihilator ∧
      source.finiteTraceReadoutUsesAllKirchhoffTests
  traceRepresentationUsesGreenAnnihilatorClassificationWitness :=
    ⟨source.boundaryTraceGreenPairingRealizesAnnihilatorWitness,
      source.finiteTraceReadoutUsesAllKirchhoffTestsWitness⟩
  graphH2RegularityRecoveredFromAdjointEquation :=
    ∀ candidate : source.calculus.candidate,
      source.calculus.graphH2RegularityFromAdjointEquation candidate
  graphH2RegularityRecoveredWitness :=
    source.calculus.graphH2RegularityWitness
  finiteTraceRepresentationIsGlobal :=
    source.calculus.candidatesRepresentAdjointDomain ∧
      source.finiteTraceReadoutIsGlobal ∧
        source.calculus.noFiniteDiagnosticSubstitute
  finiteTraceRepresentationIsGlobalWitness :=
    ⟨source.calculus.candidatesRepresentAdjointDomainWitness,
      source.finiteTraceReadoutIsGlobalWitness,
      source.calculus.noFiniteDiagnosticSubstituteWitness⟩
  status := .conditional_interface

-- ============================================================
-- TARGET-LEVEL ADAPTERS
-- ============================================================

/-- Compact-graph finite trace readout discharges the raw finite trace
    representation target. -/
theorem
    G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutSource.toRawFiniteTraceAdjointRepresentationTarget
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutSource) :
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget :=
  ⟨source.toRawFiniteTraceAdjointRepresentationSource⟩

/-- Target-level adapter from compact-graph finite trace readout to raw finite
    trace representation. -/
theorem
    g8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget_ofCompactGraphFiniteTraceReadout
    (target :
      G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutTarget) :
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget :=
  target.elim fun source =>
    source.toRawFiniteTraceAdjointRepresentationTarget

/-- Compact-graph finite trace readout is sufficient for the finite-trace
    lift/reverse-inclusion target. -/
theorem
    g8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget_ofCompactGraphFiniteTraceReadout
    (target :
      G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutTarget) :
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget :=
  g8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget_ofRawFiniteTraceRepresentation
    (g8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget_ofCompactGraphFiniteTraceReadout
      target)

/-- Compact-graph finite trace readout is sufficient for the A1.5 proof-stone
    target. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget_ofCompactGraphFiniteTraceReadout
    (target :
      G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget_ofRawFiniteTraceRepresentation
    (g8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget_ofCompactGraphFiniteTraceReadout
      target)

/-- Compact-graph finite trace readout is sufficient for the selected-carrier
    A1.5 maximal Kirchhoff self-adjoint extension target. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofCompactGraphFiniteTraceReadout
    (target :
      G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofRawFiniteTraceRepresentation
    (g8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget_ofCompactGraphFiniteTraceReadout
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Compact-graph regularity/Green calculus without endpoint finite trace
    readout still does not construct the raw finite trace representation. -/
structure
    G8BookIIICh23FloorNormalizedA15CompactGraphCalculusWithoutFiniteTraceReadout
    where
  calculus :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource
  missingFiniteTraceReadout :
    ¬ G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutTarget

theorem
    G8BookIIICh23FloorNormalizedA15CompactGraphCalculusWithoutFiniteTraceReadout.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15CompactGraphCalculusWithoutFiniteTraceReadout)
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutSource) :
    False :=
  gap.missingFiniteTraceReadout ⟨source⟩

/-- A finite trace readout without the annihilator law cannot feed boundary
    forcing. -/
structure
    G8BookIIICh23FloorNormalizedA15FiniteTraceReadoutWithoutAnnihilatorLaw
    where
  source :
    G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutSource
  missingAnnihilatorLaw :
    ¬ (∀ candidate : source.calculus.candidate,
        G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
          (source.boundaryTrace candidate))

theorem
    G8BookIIICh23FloorNormalizedA15FiniteTraceReadoutWithoutAnnihilatorLaw.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15FiniteTraceReadoutWithoutAnnihilatorLaw) :
    False :=
  gap.missingAnnihilatorLaw
    gap.source.finiteTraceAnnihilatesKirchhoff

/-- A finite trace readout that is only diagnostic cannot supply the global
    adjoint-domain finite trace representation. -/
structure
    G8BookIIICh23FloorNormalizedA15FiniteTraceReadoutDiagnosticOnly
    where
  source :
    G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutSource
  diagnosticOnly :
    ¬ source.finiteTraceReadoutIsGlobal

theorem
    G8BookIIICh23FloorNormalizedA15FiniteTraceReadoutDiagnosticOnly.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15FiniteTraceReadoutDiagnosticOnly) :
    False :=
  gap.diagnosticOnly gap.source.finiteTraceReadoutIsGlobalWitness

end Tau.BookIII.Bridge
