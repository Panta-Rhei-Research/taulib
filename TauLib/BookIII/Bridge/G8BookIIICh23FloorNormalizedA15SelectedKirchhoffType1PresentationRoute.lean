import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationAssembly

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Selected Kirchhoff Type-1 Presentation Route

This module is the first of the two remaining A1.5 payload routes.

The selected A1.3 Kirchhoff operator domain is normalized to a `Type 1`
carrier: its internal function/output carriers are `Type`-level selected graph
data.  The concrete A1.5 adjoint calculus engine still insists on an explicit
`Type 1` candidate/test presentation.  The real theorem is therefore a
small-presentation theorem:

```text
small Type-1 carrier
  -> exact realization into the selected Kirchhoff domain
  -> every selected Kirchhoff element is realized
  -> selected Kirchhoff Type-1 presentation
```

This file gives the exact proof-carrying route and proof-backed adapters into the
existing A1.5 assembly.  It does not assert that the small carrier has already
been constructed, and it does not use finite diagnostics as a substitute for
exhaustivity.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- SMALL PRESENTATION ROUTE
-- ============================================================

/-- The proof-carrying source for the small presentation of the selected A1.3
    Kirchhoff operator domain.

The load-bearing field is `realizesEverySelectedKirchhoffElement`.  It is the
exact universe-lowering theorem still required for the Type-1 presentation
route. -/
structure
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource where
  point : Type 1
  pointNonempty : Nonempty point
  realize :
    point →
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain
  realizesEverySelectedKirchhoffElement :
    ∀ u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain,
      ∃ p : point, realize p = u
  realizationUsesClosedSelectedA13Domain : Prop
  realizationUsesClosedSelectedA13DomainWitness :
    realizationUsesClosedSelectedA13Domain
  universeLoweringIsGenuine : Prop
  universeLoweringIsGenuineWitness :
    universeLoweringIsGenuine
  noFiniteDiagnosticSubstitute : Prop
  noFiniteDiagnosticSubstituteWitness :
    noFiniteDiagnosticSubstitute
  constructedFromCompactGraphDomain : Prop
  constructedFromCompactGraphDomainWitness :
    constructedFromCompactGraphDomain
  status : SpineStatus := .conditional_interface

/-- Target for the small-presentation route. -/
def
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource

/-- The selected-domain exhaustivity carried by a route source. -/
def
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffRouteExhaustive
    (source :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource) :
    Prop :=
  ∀ u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain,
    ∃ p : source.point, source.realize p = u

/-- A route source is exhaustive by construction. -/
theorem
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource.exhaustive
    (source :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource) :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffRouteExhaustive
      source :=
  source.realizesEverySelectedKirchhoffElement

/-- A route source gives the selected Kirchhoff Type-1 presentation consumed
    by the A1.5 engine. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource.toPresentation
    (source :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource) :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation where
  point := source.point
  pointNonempty := source.pointNonempty
  realize := source.realize
  realizesEverySelectedKirchhoffElement :=
    source.realizesEverySelectedKirchhoffElement
  noFiniteDiagnosticSubstitute :=
    source.noFiniteDiagnosticSubstitute
  noFiniteDiagnosticSubstituteWitness :=
    source.noFiniteDiagnosticSubstituteWitness
  constructedFromCompactGraphDomain :=
    source.constructedFromCompactGraphDomain
  constructedFromCompactGraphDomainWitness :=
    source.constructedFromCompactGraphDomainWitness
  status := .conditional_interface

/-- A small-presentation route source proves the existing presentation target. -/
theorem
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource.toPresentationTarget
    (source :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource) :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationTarget :=
  ⟨source.toPresentation⟩

/-- Target-level adapter from the route target to the existing presentation
    target. -/
theorem
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationTarget_ofRoute
    (target :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget) :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationTarget :=
  target.elim fun source => source.toPresentationTarget

-- ============================================================
-- ROUTE INTO THE A1.5 ASSEMBLY
-- ============================================================

/-- The small-presentation route plus the proof-stone target assemble the
    adjoint-domain Type-1 presentation target. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofSelectedRouteAndProofStones
    (presentationRoute :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget)
    (proofStoneTarget :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofPresentationAndProofStones
    (g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationTarget_ofRoute
      presentationRoute)
    proofStoneTarget

/-- The small-presentation route plus the proof-stone target feed the concrete
    A1.5 adjoint-calculus engine. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofSelectedRouteAndProofStones
    (presentationRoute :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget)
    (proofStoneTarget :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofType1Presentation
    (g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofSelectedRouteAndProofStones
      presentationRoute
      proofStoneTarget)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Without exact exhaustivity, a small carrier cannot serve as the selected
    Kirchhoff Type-1 presentation. -/
structure
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffRouteWithoutExhaustivity
    where
  source :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource
  missingExhaustivity :
    ¬ G8BookIIICh23FloorNormalizedA15SelectedKirchhoffRouteExhaustive
      source

theorem
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffRouteWithoutExhaustivity.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffRouteWithoutExhaustivity) :
    False :=
  gap.missingExhaustivity gap.source.exhaustive

/-- A finite diagnostic substitute is refuted by the route's non-diagnostic
    provenance field. -/
structure
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffRouteFiniteDiagnosticOnly
    where
  source :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource
  diagnosticOnly :
    ¬ source.noFiniteDiagnosticSubstitute

theorem
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffRouteFiniteDiagnosticOnly.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffRouteFiniteDiagnosticOnly) :
    False :=
  gap.diagnosticOnly gap.source.noFiniteDiagnosticSubstituteWitness

/-- The Type-1 route must be a genuine universe-lowering construction, not a
    silent reuse of an unnormalized higher-universe carrier. -/
structure
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffRouteNotUniverseLowering
    where
  source :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource
  missingUniverseLowering :
    ¬ source.universeLoweringIsGenuine

theorem
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffRouteNotUniverseLowering.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffRouteNotUniverseLowering) :
    False :=
  gap.missingUniverseLowering gap.source.universeLoweringIsGenuineWitness

end Tau.BookIII.Bridge
