import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15AllTestGreenIdentityConstruction
import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15SelectedEndpointTraceReadout

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Reverse Inclusion / Maximality Assembly

This module closes the post-Green A1.5 assembly step:

```text
graph-H2 recovery + all-test Green identity
  -> trace/annihilator classification
  -> selected endpoint finite trace in the Kirchhoff annihilator
  -> raw finite-trace reverse inclusion
  -> proof stones and maximal Kirchhoff self-adjointness
```

The load-bearing analytic stones remain the lower-route theorems already
closed upstream: distributional equation, graph-H2 recovery, and all-test
Green identity.  This file adds no spectral, A3 actual-`xi`, accepted
coverage, O3, determinant, divisor, completion, or RH-facing dependency.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- TRACE / ANNIHILATOR PAYLOAD FROM THE CLOSED GREEN SOURCE
-- ============================================================

/-- The closed graph-H2/all-test-Green source, re-read as the exact
    trace-annihilator classification source consumed by the finite-trace
    reverse-inclusion layer. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource_closed :
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource :=
  g8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource_closed
    |>.toTraceAnnihilatorClassificationSource

/-- The closed trace source and annihilator source are exactly aligned. -/
theorem
    g8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource_closed_aligned :
    (G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource.toAnnihilatorClassificationSource
        g8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource_closed).traceSource =
      G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource.toTraceExistenceSource
        g8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource_closed := by
  let source :=
    g8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource_closed
  change source.annihilatorSource.traceSource = source.traceSource
  rw [source.annihilatorSourceFromInput]
  exact
    source.annihilatorUsesTraceSource

/-- The closed trace/annihilator payload route used by the boundary-forcing
    layer. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource_closed :
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource
    where
  traceExistence :=
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource.toTraceExistenceSource
      g8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource_closed
  annihilatorClassification :=
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource.toAnnihilatorClassificationSource
      g8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource_closed
  traceSourceAligned :=
    g8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource_closed_aligned
  noFiniteDiagnosticTestSubset :=
    G8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain
  noFiniteDiagnosticTestSubsetWitness :=
    g8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain_closed
  status := .conditional_interface

/-- Target-level closure of the trace/annihilator payload route. -/
theorem
    g8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteTarget_closed :
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteTarget :=
  ⟨g8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource_closed⟩

-- ============================================================
-- ENDPOINT FINITE TRACE FOR ACTUAL ADJOINT CANDIDATES
-- ============================================================

/-- The finite endpoint trace attached to an actual lower-route adjoint
    candidate by its selected A1.3 representative. -/
def
    G8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate) :
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace :=
  G8BookIIICh23FloorNormalizedA15SelectedEndpointFiniteTrace
    u.selectedRepresentative

/-- The actual endpoint trace is Kirchhoff because the selected representative
    carries the closed A1.3 endpoint laws. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace_kirchhoff
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate) :
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.Kirchhoff
      (G8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace u) :=
  G8BookIIICh23FloorNormalizedA15SelectedEndpointFiniteTrace_kirchhoff
    u.selectedRepresentative

/-- The actual endpoint trace lies in the finite Kirchhoff annihilator. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace_annihilatesKirchhoff
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate) :
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
      (G8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace u) :=
  G8BookIIICh23FloorNormalizedA15SelectedEndpointFiniteTrace_annihilatesKirchhoff
    u.selectedRepresentative

-- ============================================================
-- RAW FINITE TRACE REPRESENTATION
-- ============================================================

/-- Closed raw finite-trace representation for the actual lower-route
    adjoint candidates.

The boundary trace is the selected endpoint trace.  Its annihilator law is
the closed finite boundary algebra applied to the selected Kirchhoff endpoint
conditions; its Green provenance is the all-test Green identity closed
upstream. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource_closed :
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource
    where
  traceAnnihilator :=
    g8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource_closed
  adjointCandidateCarrier :=
    G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate
  adjointCandidateNonempty :=
    g8BookIIICh23FloorNormalizedA15ActualAdjointCandidate_nonempty
  boundaryTrace :=
    G8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace
  traceAnnihilatesKirchhoff :=
    g8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace_annihilatesKirchhoff
  representsAllAdjointBoundaryTraces :=
    (∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      g8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source_closed
        |>.graphH2
        |>.graphH2TraceRecoveryAt u) ∧
      (∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
        g8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source_closed
          |>.greenIdentityMatchesAdjointPairingLawAt u)
  representsAllAdjointBoundaryTracesWitness :=
    ⟨g8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source_closed
        |>.graphH2
        |>.graphH2TraceRecoveryAtWitness,
      g8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source_closed
        |>.greenIdentityMatchesAdjointPairingLawWitness⟩
  tracesComeFromAdjointTraceExistence :=
    G8BookIIICh23FloorNormalizedA15ActualBoundaryTracesExist
  tracesComeFromAdjointTraceExistenceWitness :=
    g8BookIIICh23FloorNormalizedA15ActualBoundaryTracesExist_closed
  traceRepresentationUsesGreenAnnihilatorClassification :=
    G8BookIIICh23FloorNormalizedA15ActualAnnihilatesKirchhoffBoundaryForm ∧
      G8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain
  traceRepresentationUsesGreenAnnihilatorClassificationWitness :=
    ⟨g8BookIIICh23FloorNormalizedA15ActualAnnihilatesKirchhoffBoundaryForm_closed,
      g8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain_closed⟩
  graphH2RegularityRecoveredFromAdjointEquation :=
    ∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      g8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source_closed
        |>.graphH2
        |>.graphH2TraceRecoveryAt u
  graphH2RegularityRecoveredWitness :=
    g8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source_closed
      |>.graphH2
      |>.graphH2TraceRecoveryAtWitness
  finiteTraceRepresentationIsGlobal :=
    (∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      g8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource_subtype
        |>.hilbertAdjointGraphPredicate u) ∧
      G8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain
  finiteTraceRepresentationIsGlobalWitness :=
    ⟨g8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource_subtype
        |>.predicateMembershipWitness,
      g8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain_closed⟩
  status := .conditional_interface

/-- Target-level closure of the raw finite-trace representation. -/
theorem
    g8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget_closed :
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget :=
  ⟨g8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource_closed⟩

-- ============================================================
-- BOUNDARY HOOKUP AND LOWER ROUTE
-- ============================================================

/-- Closed boundary-annihilator hookup, with the actual endpoint finite trace
    as the boundary data and the closed finite boundary algebra as the forcing
    theorem. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed :
    G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource
    where
  green :=
    g8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source_closed
  boundaryTraceAnnihilatorAt :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
        (G8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace u)
  boundaryTraceAnnihilatorAtWitness :=
    g8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace_annihilatesKirchhoff
  boundaryTraceForcesKirchhoffAt :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.Kirchhoff
        (G8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace u)
  boundaryTraceForcesKirchhoffAtWitness :=
    g8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace_kirchhoff
  usesClosedFiniteBoundaryAlgebra :=
    ∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.Kirchhoff
        (G8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace u)
  usesClosedFiniteBoundaryAlgebraWitness :=
    g8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace_kirchhoff
  noApproximateBoundaryData :=
    G8BookIIICh23FloorNormalizedA15ActualAnnihilatesKirchhoffBoundaryForm ∧
      G8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain
  noApproximateBoundaryDataWitness :=
    ⟨g8BookIIICh23FloorNormalizedA15ActualAnnihilatesKirchhoffBoundaryForm_closed,
      g8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain_closed⟩
  status := .conditional_interface

/-- Target-level closure of the finite boundary-annihilator hookup. -/
theorem
    g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupTarget_closed :
    G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupTarget :=
  ⟨g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed⟩

/-- Closed lower Hilbert-adjoint graph-predicate route after the all-test
    Green identity and finite boundary-annihilator hookup. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource_closed :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource
    where
  annihilator :=
    g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed
  reverseInclusionIntoSelectedKirchhoffDomainAt :=
    fun u =>
      (g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed
          |>.green
          |>.graphH2
          |>.graphH2TraceRecoveryAt u) ∧
        (g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed
          |>.boundaryTraceForcesKirchhoffAt u)
  reverseInclusionIntoSelectedKirchhoffDomainAtWitness :=
    fun u =>
      ⟨g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed
          |>.green
          |>.graphH2
          |>.graphH2TraceRecoveryAtWitness u,
        g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed
          |>.boundaryTraceForcesKirchhoffAtWitness u⟩
  reverseInclusionUsesDistributionalH2GreenAndBoundaryForcing :=
    (∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed
        |>.green
        |>.graphH2
        |>.graphH2TraceRecoveryAt u) ∧
      (∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
        g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed
          |>.green
          |>.greenIdentityMatchesAdjointPairingLawAt u) ∧
        (∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
          g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed
            |>.boundaryTraceForcesKirchhoffAt u)
  reverseInclusionUsesDistributionalH2GreenAndBoundaryForcingWitness :=
    ⟨g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed
        |>.green
        |>.graphH2
        |>.graphH2TraceRecoveryAtWitness,
      g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed
        |>.green
        |>.greenIdentityMatchesAdjointPairingLawWitness,
      g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed
        |>.boundaryTraceForcesKirchhoffAtWitness⟩
  graphDefinitionIsGlobal :=
    (∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      g8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource_subtype
        |>.hilbertAdjointGraphPredicate u) ∧
      G8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain
  graphDefinitionIsGlobalWitness :=
    ⟨g8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource_subtype
        |>.predicateMembershipWitness,
      g8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain_closed⟩
  noFiniteDiagnosticSubstitute :=
    G8BookIIICh23FloorNormalizedA15ActualAnnihilatesKirchhoffBoundaryForm ∧
      G8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain ∧
        (g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed
          |>.noApproximateBoundaryData)
  noFiniteDiagnosticSubstituteWitness :=
    ⟨g8BookIIICh23FloorNormalizedA15ActualAnnihilatesKirchhoffBoundaryForm_closed,
      g8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain_closed,
      g8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource_closed
        |>.noApproximateBoundaryDataWitness⟩
  status := .conditional_interface

/-- Target-level closure of the lower Hilbert-adjoint graph-predicate route. -/
theorem
    g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget_closed :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget :=
  ⟨g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource_closed⟩

-- ============================================================
-- REVERSE INCLUSION, PROOF STONES, AND MAXIMALITY
-- ============================================================

/-- The closed raw finite-trace representation supplies the finite-trace
    reverse-inclusion target. -/
theorem
    g8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget_closed :
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget :=
  g8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget_ofRawFiniteTraceRepresentation
    g8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget_closed

/-- Closed A1.5 adjoint-domain exhaustion proof stones. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget_closed :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget :=
  g8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource_closed
    |>.toAdjointDomainExhaustionProofStoneTarget

/-- Closed A1.5 adjoint calculus engine target via the raw finite-trace
    reverse-inclusion path. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_closed :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :=
  g8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource_closed
    |>.toAdjointCalculusEngineTarget

/-- Closed compact-graph adjoint-domain realization target. -/
theorem
    g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_closed :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget :=
  g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_ofRawFiniteTraceRepresentation
    g8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget_closed

/-- Closed selected-carrier A1.5 maximal Kirchhoff self-adjoint extension
    target. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_closed :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofRawFiniteTraceRepresentation
    g8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget_closed

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- The trace-annihilator source alone is not enough unless the endpoint
    finite trace is also shown to annihilate all Kirchhoff tests. -/
structure
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorWithoutEndpointReadout
    where
  traceAnnihilator :
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource
  missingEndpointAnnihilator :
    ¬ (∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
        G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
          (G8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace u))

theorem
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorWithoutEndpointReadout.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15TraceAnnihilatorWithoutEndpointReadout) :
    False :=
  gap.missingEndpointAnnihilator
    g8BookIIICh23FloorNormalizedA15ActualAdjointEndpointFiniteTrace_annihilatesKirchhoff

/-- Boundary hookup without reverse-inclusion assembly does not reach the
    lower graph-predicate route. -/
structure
    G8BookIIICh23FloorNormalizedA15BoundaryHookupWithoutReverseAssembly
    where
  hookup :
    G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource
  missingRoute :
    ¬ G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget

theorem
    G8BookIIICh23FloorNormalizedA15BoundaryHookupWithoutReverseAssembly.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15BoundaryHookupWithoutReverseAssembly) :
    False :=
  gap.missingRoute
    g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget_closed

end Tau.BookIII.Bridge
