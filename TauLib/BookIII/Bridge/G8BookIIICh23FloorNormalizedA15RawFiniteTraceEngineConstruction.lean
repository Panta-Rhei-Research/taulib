import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15FiniteTraceBoundaryForcingConstruction
import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteConstruction
import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationConstructor
import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationConstruction

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Raw Finite-Trace Engine Construction

This module is the source-level construction below the A1.5 lower route.

The selected Kirchhoff Type-1 presentation is already closed.  The finite
boundary-linear algebra is already closed.  The remaining load-bearing input
at this layer is therefore the raw finite trace representation of actual
adjoint candidates.  From that single source we construct, without a target
detour:

```text
raw finite trace representation
  -> reverse-inclusion proof stones
  -> adjoint-domain Type-1 presentation source
  -> concrete adjoint-calculus engine source
  -> lower Hilbert-adjoint graph predicate route source
```

No spectral, A3 actual-`xi`, accepted-coverage, O3, determinant, divisor,
completion, or RH-facing source is imported or used.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- RAW FINITE TRACE TO REVERSE-INCLUSION PROOF STONES
-- ============================================================

/-- The raw finite trace representation constructs the full A1.5
    reverse-inclusion proof-stone source.

This is source-level, not merely target-level: crossing agreement, Kirchhoff
balance, maximal boundary, and reverse inclusion are read through the finite
trace lift and the closed finite boundary-linear algebra. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toAdjointDomainExhaustionProofStoneSource
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource :=
  source.toFiniteTraceLiftReverseInclusionSource
    |>.toAdjointLiftReverseInclusionSource
    |>.toMaximalBoundaryReverseInclusionSource
    |>.toPayloadRouteSource
    |>.toProofStoneSource

/-- Source-level proof stones packaged as the existing proof-stone target. -/
theorem
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toAdjointDomainExhaustionProofStoneTarget
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget :=
  ⟨source.toAdjointDomainExhaustionProofStoneSource⟩

-- ============================================================
-- CLOSED TYPE-1 PRESENTATION PLUS RAW TRACE PROOF STONES
-- ============================================================

/-- The closed selected Kirchhoff Type-1 presentation used by the concrete
    engine construction. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15ClosedSelectedKirchhoffType1Presentation :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation :=
  g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource_closed
    |>.toPresentation

/-- The raw finite trace representation, together with the closed selected
    Type-1 presentation, constructs the adjoint-domain Type-1 presentation
    assembly source. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toAdjointDomainType1PresentationAssemblySource
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationAssemblySource where
  presentation :=
    g8BookIIICh23FloorNormalizedA15ClosedSelectedKirchhoffType1Presentation
  proofStones :=
    source.toAdjointDomainExhaustionProofStoneSource
  status := .conditional_interface

/-- The raw finite trace representation constructs the adjoint-domain Type-1
    presentation source consumed by the concrete A1.5 engine. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toAdjointDomainType1PresentationSource
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource :=
  source.toAdjointDomainType1PresentationAssemblySource
    |>.toType1PresentationSource

/-- Source-level Type-1 presentation packaged as the existing target. -/
theorem
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toAdjointDomainType1PresentationTarget
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget :=
  ⟨source.toAdjointDomainType1PresentationSource⟩

-- ============================================================
-- RAW TRACE TO CONCRETE ENGINE AND LOWER ROUTE
-- ============================================================

/-- The raw finite trace representation constructs the concrete
    adjoint-calculus engine source. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toAdjointCalculusEngineSource
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource :=
  source.toAdjointDomainType1PresentationSource
    |>.toAdjointCalculusEngineSource

/-- The raw finite trace representation discharges the concrete engine
    target. -/
theorem
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toAdjointCalculusEngineTarget
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :=
  ⟨source.toAdjointCalculusEngineSource⟩

/-- The raw finite trace representation constructs the lower Hilbert-adjoint
    graph predicate route source through the concrete engine. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toHilbertAdjointGraphPredicateRouteSource
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource :=
  source.toAdjointCalculusEngineSource
    |>.toHilbertAdjointGraphPredicateRouteSource

/-- Source-level lower-route target from raw finite trace representation. -/
theorem
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toHilbertAdjointGraphPredicateRouteTarget
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget :=
  ⟨source.toHilbertAdjointGraphPredicateRouteSource⟩

-- ============================================================
-- TARGET-LEVEL SELECTORS
-- ============================================================

/-- Target-level selector from raw finite trace representation to the concrete
    engine. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofRawFiniteTraceRepresentation
    (target :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :=
  target.elim fun source => source.toAdjointCalculusEngineTarget

/-- Target-level selector from raw finite trace representation to the lower
    Hilbert-adjoint graph predicate route. -/
theorem
    g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget_ofRawFiniteTraceRepresentation
    (target :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget :=
  target.elim fun source => source.toHilbertAdjointGraphPredicateRouteTarget

/-- Target-level selector from raw finite trace representation to the full
    compact-graph adjoint-domain realization constructor. -/
theorem
    g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_ofRawFiniteTraceRepresentation
    (target :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget :=
  g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_ofPredicateRouteConstructor
    (g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget_ofRawFiniteTraceRepresentation
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Without the raw finite trace representation, the direct engine constructor
    has no source-level input. -/
structure
    G8BookIIICh23FloorNormalizedA15NoRawFiniteTraceNoEngineSource
    where
  missingRawFiniteTrace :
    ¬ G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget

theorem
    G8BookIIICh23FloorNormalizedA15NoRawFiniteTraceNoEngineSource.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15NoRawFiniteTraceNoEngineSource)
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    False :=
  gap.missingRawFiniteTrace ⟨source⟩

/-- The closed selected Type-1 presentation is still used explicitly; the raw
    trace route does not replace the selected-domain universe-lowering step. -/
theorem
    g8BookIIICh23FloorNormalizedA15RawFiniteTraceEngineConstruction_usesClosedSelectedPresentation
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    source.toAdjointDomainType1PresentationAssemblySource.presentation =
      g8BookIIICh23FloorNormalizedA15ClosedSelectedKirchhoffType1Presentation :=
  rfl

/-- The engine source produced by the raw trace route carries the reverse
    inclusion proof stones through its candidate coverage field. -/
theorem
    g8BookIIICh23FloorNormalizedA15RawFiniteTraceEngineConstruction_candidateCoverage
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    source.toAdjointCalculusEngineSource.candidates.representsFullAdjointDomain :=
  source.toAdjointCalculusEngineSource.candidates
    |>.representsFullAdjointDomainWitness

end Tau.BookIII.Bridge
