import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15RawFiniteTraceEngineConstruction

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Actual Adjoint Endpoint Trace Construction

This module constructs the endpoint-trace route from the actual Hilbert-adjoint
graph predicate route.

The previous raw finite-trace engine construction proved:

```text
raw finite trace representation
  -> reverse-inclusion proof stones
  -> Type-1 presentation
  -> concrete adjoint calculus engine
```

Here we construct the missing input from the lower route:

```text
actual Hilbert-adjoint graph predicate route
  -> selected representative for each adjoint candidate
  -> selected endpoint finite trace
  -> raw finite trace representation
  -> reverse-inclusion proof stones and engine
```

No A2 spectrum, A3 actual-`xi`, accepted coverage, O3, determinant transfer,
divisor transfer, completion uniqueness, or RH-facing handoff is imported or
used.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- ENDPOINT TRACE READOUT FROM THE LOWER GRAPH-PREDICATE ROUTE
-- ============================================================

/-- The graph-predicate route first gives the compact-domain realization, then
    the genuine carrier, and hence the concrete adjoint-calculus engine whose
    candidates are actual Hilbert-adjoint graph candidates. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.toEndpointTraceAdjointCalculusEngineSource
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource :=
  source.toCompactGraphAdjointDomainRealizationSource
    |>.toGenuineAdjointDomainCarrierSource
    |>.toAdjointCalculusEngineSource

/-- The endpoint finite-trace readout induced by the selected representative
    of each actual adjoint candidate. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.toEndpointCompactGraphFiniteTraceReadoutSource
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutSource :=
  source.toEndpointTraceAdjointCalculusEngineSource
    |>.toCompactGraphFiniteTraceReadoutSource

/-- The lower graph-predicate route constructs the raw finite-trace
    representation by reading endpoint traces from selected representatives. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.toEndpointRawFiniteTraceAdjointRepresentationSource
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource :=
  source.toEndpointCompactGraphFiniteTraceReadoutSource
    |>.toRawFiniteTraceAdjointRepresentationSource

/-- The endpoint trace readout is in the Kirchhoff annihilator for every
    actual adjoint candidate in the route. -/
theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.endpointTraceAnnihilatesKirchhoff
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    ∀ candidate :
        source.toEndpointRawFiniteTraceAdjointRepresentationSource
          |>.adjointCandidateCarrier,
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
        ((source.toEndpointRawFiniteTraceAdjointRepresentationSource)
          |>.boundaryTrace candidate) :=
  source.toEndpointRawFiniteTraceAdjointRepresentationSource
    |>.traceAnnihilatesKirchhoff

/-- The endpoint trace construction is global over the actual adjoint-domain
    carrier, not a finite diagnostic family. -/
theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.endpointRawFiniteTraceIsGlobal
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    source.toEndpointRawFiniteTraceAdjointRepresentationSource
      |>.finiteTraceRepresentationIsGlobal :=
  source.toEndpointRawFiniteTraceAdjointRepresentationSource
    |>.finiteTraceRepresentationIsGlobalWitness

-- ============================================================
-- TARGET-LEVEL CONSTRUCTORS
-- ============================================================

/-- A lower graph-predicate route now supplies the raw finite-trace
    representation target. -/
theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.toEndpointRawFiniteTraceAdjointRepresentationTarget
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget :=
  ⟨source.toEndpointRawFiniteTraceAdjointRepresentationSource⟩

/-- Target-level constructor from the graph-predicate route to raw finite
    traces. -/
theorem
    g8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget_ofPredicateRouteEndpointTrace
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget) :
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget :=
  target.elim fun source =>
    source.toEndpointRawFiniteTraceAdjointRepresentationTarget

/-- Source-level reverse-inclusion proof stones built from endpoint raw finite
    traces. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.toEndpointAdjointDomainExhaustionProofStoneSource
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource :=
  source.toEndpointRawFiniteTraceAdjointRepresentationSource
    |>.toAdjointDomainExhaustionProofStoneSource

/-- A graph-predicate route supplies the reverse-inclusion proof-stone target
    through the endpoint raw finite-trace representation. -/
theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.toEndpointAdjointDomainExhaustionProofStoneTarget
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget :=
  ⟨source.toEndpointAdjointDomainExhaustionProofStoneSource⟩

/-- Target-level constructor for reverse-inclusion proof stones from endpoint
    raw finite traces. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget_ofPredicateRouteEndpointTrace
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget :=
  target.elim fun source =>
    source.toEndpointAdjointDomainExhaustionProofStoneTarget

/-- Source-level Type-1 presentation built from the endpoint raw finite-trace
    reverse-inclusion proof stones. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.toEndpointAdjointDomainType1PresentationSource
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource :=
  source.toEndpointRawFiniteTraceAdjointRepresentationSource
    |>.toAdjointDomainType1PresentationSource

/-- Source-level concrete engine reconstructed from endpoint raw finite
    traces and the closed selected Type-1 presentation. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.toEndpointRawTraceAdjointCalculusEngineSource
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource :=
  source.toEndpointRawFiniteTraceAdjointRepresentationSource
    |>.toAdjointCalculusEngineSource

/-- A graph-predicate route supplies the concrete A1.5 engine target through
    endpoint raw finite traces. -/
theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.toEndpointRawTraceAdjointCalculusEngineTarget
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :=
  ⟨source.toEndpointRawTraceAdjointCalculusEngineSource⟩

/-- Target-level constructor for the concrete engine from endpoint raw finite
    traces. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofPredicateRouteEndpointTrace
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :=
  target.elim fun source =>
    source.toEndpointRawTraceAdjointCalculusEngineTarget

/-- The endpoint trace route also reconstructs the lower Hilbert-adjoint
    graph-predicate route through the raw finite-trace engine construction. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.toEndpointReconstructedHilbertAdjointGraphPredicateRouteSource
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource :=
  source.toEndpointRawFiniteTraceAdjointRepresentationSource
    |>.toHilbertAdjointGraphPredicateRouteSource

/-- A graph-predicate route gives the selected-carrier A1.5 maximal
    Kirchhoff self-adjointness target through endpoint raw finite traces. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofPredicateRouteEndpointTrace
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofRawFiniteTraceRepresentation
    (g8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget_ofPredicateRouteEndpointTrace
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Missing endpoint raw finite-trace representation refutes a lower
    graph-predicate route. -/
structure
    G8BookIIICh23FloorNormalizedA15PredicateRouteWithoutEndpointRawFiniteTrace
    where
  source :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource
  missingEndpointRawTrace :
    ¬ G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget

theorem
    G8BookIIICh23FloorNormalizedA15PredicateRouteWithoutEndpointRawFiniteTrace.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15PredicateRouteWithoutEndpointRawFiniteTrace) :
    False :=
  gap.missingEndpointRawTrace
    gap.source.toEndpointRawFiniteTraceAdjointRepresentationTarget

/-- Missing endpoint-trace annihilator membership refutes the construction. -/
structure
    G8BookIIICh23FloorNormalizedA15PredicateRouteEndpointTraceWithoutAnnihilator
    where
  source :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource
  missingAnnihilator :
    ¬ (∀ candidate :
          source.toEndpointRawFiniteTraceAdjointRepresentationSource
            |>.adjointCandidateCarrier,
        G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
          ((source.toEndpointRawFiniteTraceAdjointRepresentationSource)
            |>.boundaryTrace candidate))

theorem
    G8BookIIICh23FloorNormalizedA15PredicateRouteEndpointTraceWithoutAnnihilator.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15PredicateRouteEndpointTraceWithoutAnnihilator) :
    False :=
  gap.missingAnnihilator
    gap.source.endpointTraceAnnihilatesKirchhoff

/-- A non-global endpoint finite trace family cannot replace the actual
    adjoint-domain endpoint trace construction. -/
structure
    G8BookIIICh23FloorNormalizedA15PredicateRouteEndpointTraceDiagnosticOnly
    where
  source :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource
  diagnosticOnly :
    ¬ (source.toEndpointRawFiniteTraceAdjointRepresentationSource
      |>.finiteTraceRepresentationIsGlobal)

theorem
    G8BookIIICh23FloorNormalizedA15PredicateRouteEndpointTraceDiagnosticOnly.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15PredicateRouteEndpointTraceDiagnosticOnly) :
    False :=
  gap.diagnosticOnly
    gap.source.endpointRawFiniteTraceIsGlobal

end Tau.BookIII.Bridge
