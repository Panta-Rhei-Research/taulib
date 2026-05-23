import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRoute

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Selected Kirchhoff Type-1 Presentation Construction

This module discharges the first of the two remaining A1.5 payload routes.

The key source change is upstream in A1.3: the selected Kirchhoff operator
domain now stores `Type`-level function/output carriers, so the selected domain
itself is a genuine `Type 1` carrier.  The small presentation is therefore the
identity presentation on the selected A1.3 Kirchhoff domain:

```text
point := selected Kirchhoff operator domain
realize := id
every selected Kirchhoff element is realized by itself
```

This is a theorem-backed universe-lowering step for the selected
floor-normalized route.  It does not prove the reverse adjoint-domain
inclusion; that remains the second A1.5 payload route.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CLOSED SMALL PRESENTATION
-- ============================================================

/-- The identity presentation exhausts the selected A1.3 Kirchhoff operator
    domain once that domain has been normalized to `Type 1`. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource_closed :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource where
  point := G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain
  pointNonempty :=
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain_nonempty
  realize := id
  realizesEverySelectedKirchhoffElement := by
    intro u
    exact ⟨u, rfl⟩
  realizationUsesClosedSelectedA13Domain :=
    G8BookIIICh23FloorNormalizedA13ClosedSelectedHilbertDomain
      g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
  realizationUsesClosedSelectedA13DomainWitness :=
    g8BookIIICh23FloorNormalizedA13ClosedSelectedHilbertDomain_closed
  universeLoweringIsGenuine :=
    Nonempty G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain
  universeLoweringIsGenuineWitness :=
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain_nonempty
  noFiniteDiagnosticSubstitute :=
    ∀ u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain,
      ∃ p : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain,
        id p = u
  noFiniteDiagnosticSubstituteWitness := by
    intro u
    exact ⟨u, rfl⟩
  constructedFromCompactGraphDomain :=
    G8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady
      g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
  constructedFromCompactGraphDomainWitness :=
    g8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady_closed
  status := .conditional_interface

/-- The selected Kirchhoff Type-1 presentation route is closed on the
    floor-normalized selected carrier. -/
theorem
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget_closed :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget :=
  ⟨g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource_closed⟩

/-- Closed target for the selected Kirchhoff Type-1 presentation consumed by
    the A1.5 engine. -/
theorem
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationTarget_closed :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationTarget :=
  g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationTarget_ofRoute
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget_closed

/-- Pointwise exhaustivity of the closed identity presentation. -/
theorem
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRoute_exhaustive_closed :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffRouteExhaustive
      g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource_closed :=
  g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource_closed
    |>.exhaustive

-- ============================================================
-- CLOSED PRESENTATION INTO A1.5 ASSEMBLY
-- ============================================================

/-- With the small selected Kirchhoff presentation now closed, the only
    remaining A1.5 input for the Type-1 adjoint-domain presentation is the
    reverse-inclusion proof-stone target. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofClosedSelectedPresentationAndProofStones
    (proofStoneTarget :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofSelectedRouteAndProofStones
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget_closed
    proofStoneTarget

/-- The same closed selected presentation feeds the concrete adjoint-calculus
    engine as soon as the reverse-inclusion proof stones are supplied. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofClosedSelectedPresentationAndProofStones
    (proofStoneTarget :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofSelectedRouteAndProofStones
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget_closed
    proofStoneTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- The closed construction is not a finite diagnostic subset: every selected
    Kirchhoff element is realized by the identity presentation. -/
theorem
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation_closed_notFiniteDiagnosticOnly :
    ¬
      (¬
        (g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource_closed
          |>.noFiniteDiagnosticSubstitute)) := by
  intro h
  exact h
    (g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource_closed
      |>.noFiniteDiagnosticSubstituteWitness)

/-- The closed construction is genuinely small because the selected Kirchhoff
    operator domain has been normalized to `Type 1` before forming the
    identity presentation. -/
theorem
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation_closed_universeLowering :
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource_closed
      |>.universeLoweringIsGenuine :=
  g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource_closed
    |>.universeLoweringIsGenuineWitness

end Tau.BookIII.Bridge
