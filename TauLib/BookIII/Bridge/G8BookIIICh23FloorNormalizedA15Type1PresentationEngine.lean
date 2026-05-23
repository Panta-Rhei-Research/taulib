import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15AdjointCalculusEngine

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Type-1 Presentation Engine

This module is the next concrete step under the A1.5 compact-graph adjoint
calculus engine.

The selected Kirchhoff operator domain built in A1.3 is now normalized to a
`Type 1` carrier: its function/output carriers are `Type`-level graph data,
not arbitrary higher-universe carriers.  The A1.5 engine still asks for
explicit `Type 1` presentations of adjoint candidates and Kirchhoff tests, so
the universe-lowering theorem is visible rather than hidden in the domain
definition.

This file isolates that exact small-presentation theorem:

```text
Type-1 presentation of the selected Kirchhoff domain
  + reverse adjoint-domain inclusion
  -> adjoint-candidate presentation
  + Kirchhoff-test presentation
  -> concrete adjoint-calculus engine source
```

The Kirchhoff-test side is now theorem-backed from an exhaustive Type-1
presentation.  The adjoint-candidate side additionally needs the real
reverse-inclusion theorem saying the adjoint domain is represented by the
selected Kirchhoff domain.  No A1.5 maximality, compact resolvent, A2 point
spectrum, A3 actual-`xi`, or RH-facing statement is proved here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- TYPE-1 PRESENTATION OF THE SELECTED KIRCHHOFF DOMAIN
-- ============================================================

/-- A small presentation of the selected A1.3 Kirchhoff operator domain.

The load-bearing field is the exact surjectivity statement
`realizesEverySelectedKirchhoffElement`.  It is the universe-lowering theorem
needed before the A1.5 engine can be inhabited by genuine graph-domain data,
rather than by a finite diagnostic test set. -/
structure
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation where
  point : Type 1
  pointNonempty : Nonempty point
  realize :
    point →
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain
  realizesEverySelectedKirchhoffElement :
    ∀ u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain,
      ∃ p : point, realize p = u
  noFiniteDiagnosticSubstitute : Prop
  noFiniteDiagnosticSubstituteWitness :
    noFiniteDiagnosticSubstitute
  constructedFromCompactGraphDomain : Prop
  constructedFromCompactGraphDomainWitness :
    constructedFromCompactGraphDomain
  status : SpineStatus := .conditional_interface

/-- Target for the small-presentation theorem for the selected Kirchhoff
    domain. -/
def
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation

/-- Exact exhaustivity predicate induced by a Type-1 presentation. -/
def
    G8BookIIICh23FloorNormalizedA15Type1PresentationExhaustsSelectedKirchhoffDomain
    (presentation :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation) :
    Prop :=
  ∀ u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain,
    ∃ p : presentation.point, presentation.realize p = u

/-- A Type-1 presentation exhausts the selected Kirchhoff domain by its
    defining surjectivity field. -/
theorem
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation.exhaustsSelectedKirchhoffDomain
    (presentation :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation) :
    G8BookIIICh23FloorNormalizedA15Type1PresentationExhaustsSelectedKirchhoffDomain
      presentation :=
  presentation.realizesEverySelectedKirchhoffElement

/-- The presentation uses the selected graph-domain structure pointwise: every
    realized test/candidate has the closed selected trace-recovery data. -/
def
    G8BookIIICh23FloorNormalizedA15Type1PresentationUsesSelectedGraphDomain
    (presentation :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation) :
    Prop :=
  ∀ p : presentation.point,
    G8BookIIICh23FloorNormalizedA15SelectedTraceRecovery
      (presentation.realize p)

/-- Pointwise selected-domain readiness follows from the closed A1.2-A1.3
    selected representative facts. -/
theorem
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation.usesSelectedGraphDomain
    (presentation :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation) :
    G8BookIIICh23FloorNormalizedA15Type1PresentationUsesSelectedGraphDomain
      presentation :=
  fun p =>
    g8BookIIICh23FloorNormalizedA15SelectedTraceRecovery_closed
      (presentation.realize p)

-- ============================================================
-- CLOSED KIRCHHOFF-TEST PRESENTATION FROM SMALL EXHAUSTIVITY
-- ============================================================

/-- A Type-1 presentation of the selected Kirchhoff domain gives the
    Kirchhoff-test presentation required by the adjoint-calculus engine. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation.toKirchhoffTestPresentation
    (presentation :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation) :
    G8BookIIICh23FloorNormalizedA15KirchhoffTestPresentation where
  point := presentation.point
  pointNonempty := presentation.pointNonempty
  realize := presentation.realize
  exhaustsSelectedKirchhoffDomain :=
    G8BookIIICh23FloorNormalizedA15Type1PresentationExhaustsSelectedKirchhoffDomain
      presentation
  exhaustsSelectedKirchhoffDomainWitness :=
    presentation.exhaustsSelectedKirchhoffDomain
  realizationUsesSelectedGraphDomain :=
    G8BookIIICh23FloorNormalizedA15Type1PresentationUsesSelectedGraphDomain
      presentation
  realizationUsesSelectedGraphDomainWitness :=
    presentation.usesSelectedGraphDomain
  noFiniteDiagnosticSubstitute :=
    presentation.noFiniteDiagnosticSubstitute
  noFiniteDiagnosticSubstituteWitness :=
    presentation.noFiniteDiagnosticSubstituteWitness
  status := .conditional_interface

/-- A small presentation theorem is sufficient for the Kirchhoff-test side of
    the A1.5 engine. -/
theorem
    g8BookIIICh23FloorNormalizedA15KirchhoffTestPresentationTarget_ofType1Presentation
    (target :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationTarget) :
    Nonempty G8BookIIICh23FloorNormalizedA15KirchhoffTestPresentation :=
  target.elim fun presentation =>
    ⟨presentation.toKirchhoffTestPresentation⟩

-- ============================================================
-- ADJOINT-CANDIDATE PRESENTATION FROM REVERSE INCLUSION
-- ============================================================

/-- A Type-1 presentation plus reverse adjoint-domain inclusion is the exact
    source needed to present adjoint candidates by selected Kirchhoff-domain
    representatives. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource where
  presentation :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation
  reverseInclusion :
    G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource
  reverseInclusionUsesPresentation : Prop
  reverseInclusionUsesPresentationWitness :
    reverseInclusionUsesPresentation
  status : SpineStatus := .conditional_interface

/-- Target for the adjoint-domain Type-1 presentation source. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource

/-- Exact candidate-coverage predicate: the selected domain exhausts the
    adjoint domain by reverse inclusion, and the Type-1 presentation exhausts
    the selected domain. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointCandidateCoverageFromType1Presentation
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15AdjointDomainEqualsKirchhoffDomain
      source.reverseInclusion ∧
    G8BookIIICh23FloorNormalizedA15Type1PresentationExhaustsSelectedKirchhoffDomain
      source.presentation ∧
      source.reverseInclusion.graphH2RegularityRecoveredFromAdjointEquation

/-- The adjoint candidate coverage follows from reverse inclusion and the
    Type-1 presentation exhaustivity theorem. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource.candidateCoverage
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCandidateCoverageFromType1Presentation
      source :=
  ⟨source.reverseInclusion.domainEquality,
    source.presentation.exhaustsSelectedKirchhoffDomain,
    source.reverseInclusion.graphH2RegularityRecoveredWitness⟩

/-- A Type-1 adjoint-domain presentation source gives the adjoint-candidate
    presentation required by the concrete A1.5 engine. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource.toAdjointCandidatePresentation
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCandidatePresentation where
  point := source.presentation.point
  pointNonempty := source.presentation.pointNonempty
  realize := source.presentation.realize
  representsFullAdjointDomain :=
    G8BookIIICh23FloorNormalizedA15AdjointCandidateCoverageFromType1Presentation
      source
  representsFullAdjointDomainWitness :=
    source.candidateCoverage
  realizationUsesSelectedGraphDomain :=
    G8BookIIICh23FloorNormalizedA15Type1PresentationUsesSelectedGraphDomain
      source.presentation
  realizationUsesSelectedGraphDomainWitness :=
    source.presentation.usesSelectedGraphDomain
  noFiniteDiagnosticSubstitute :=
    source.presentation.noFiniteDiagnosticSubstitute ∧
      source.reverseInclusionUsesPresentation
  noFiniteDiagnosticSubstituteWitness :=
    ⟨source.presentation.noFiniteDiagnosticSubstituteWitness,
      source.reverseInclusionUsesPresentationWitness⟩
  status := .conditional_interface

-- ============================================================
-- TYPE-1 PRESENTATION SOURCE TO ADJOINT-CALCULUS ENGINE
-- ============================================================

/-- The candidate and test presentations are built from the same Type-1
    presentation and therefore use exactly the same realization map. -/
def
    G8BookIIICh23FloorNormalizedA15CandidateAndTestUseSameType1Realization
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource) :
    Prop :=
  source.toAdjointCandidatePresentation.realize =
    source.presentation.toKirchhoffTestPresentation.realize

/-- The same Type-1 realization map is used on the candidate and test sides. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource.sameType1Realization
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource) :
    G8BookIIICh23FloorNormalizedA15CandidateAndTestUseSameType1Realization
      source :=
  rfl

/-- Build the concrete adjoint-calculus engine source from a Type-1
    presentation plus reverse inclusion. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource.toAdjointCalculusEngineSource
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource where
  candidates := source.toAdjointCandidatePresentation
  tests := source.presentation.toKirchhoffTestPresentation
  presentationsUseSameSelectedA13Domain :=
    G8BookIIICh23FloorNormalizedA15CandidateAndTestUseSameType1Realization
      source
  presentationsUseSameSelectedA13DomainWitness :=
    source.sameType1Realization
  status := .conditional_interface

/-- A Type-1 adjoint-domain presentation source discharges the concrete
    adjoint-calculus engine target. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource.toAdjointCalculusEngineTarget
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :=
  ⟨source.toAdjointCalculusEngineSource⟩

/-- Target-level adapter from the Type-1 adjoint-domain presentation theorem
    to the concrete A1.5 adjoint-calculus engine. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofType1Presentation
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :=
  target.elim fun source => source.toAdjointCalculusEngineTarget

/-- The Type-1 presentation theorem is sufficient for the two analytic law
    targets already exposed by the concrete engine. -/
theorem
    g8BookIIICh23FloorNormalizedA15TwoAnalyticLawTargets_ofType1Presentation
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget) :
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquationTarget ∧
      G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTestsTarget :=
  g8BookIIICh23FloorNormalizedA15TwoAnalyticLawTargets_ofEngine
    (g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofType1Presentation
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A small presentation without selected-domain exhaustivity cannot build the
    Kirchhoff-test presentation. -/
structure
    G8BookIIICh23FloorNormalizedA15Type1PresentationWithoutExhaustivity
    where
  presentation :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation
  missingExhaustivity :
    ¬ G8BookIIICh23FloorNormalizedA15Type1PresentationExhaustsSelectedKirchhoffDomain
      presentation

theorem
    G8BookIIICh23FloorNormalizedA15Type1PresentationWithoutExhaustivity.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15Type1PresentationWithoutExhaustivity) :
    False :=
  gap.missingExhaustivity gap.presentation.exhaustsSelectedKirchhoffDomain

/-- Reverse inclusion remains necessary: small Kirchhoff tests alone do not
    prove that adjoint candidates are represented by the selected domain. -/
structure
    G8BookIIICh23FloorNormalizedA15Type1PresentationWithoutReverseInclusion
    where
  source :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource
  missingReverse :
    ¬ G8BookIIICh23FloorNormalizedA15AdjointDomainEqualsKirchhoffDomain
      source.reverseInclusion

theorem
    G8BookIIICh23FloorNormalizedA15Type1PresentationWithoutReverseInclusion.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15Type1PresentationWithoutReverseInclusion) :
    False :=
  gap.missingReverse gap.source.reverseInclusion.domainEquality

/-- A finite diagnostic candidate universe is refuted once the source carries
    the non-diagnostic presentation provenance. -/
structure
    G8BookIIICh23FloorNormalizedA15Type1PresentationDiagnosticOnlyGap
    where
  source :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource
  diagnosticOnly :
    ¬ source.presentation.noFiniteDiagnosticSubstitute

theorem
    G8BookIIICh23FloorNormalizedA15Type1PresentationDiagnosticOnlyGap.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15Type1PresentationDiagnosticOnlyGap) :
    False :=
  gap.diagnosticOnly
    gap.source.presentation.noFiniteDiagnosticSubstituteWitness

end Tau.BookIII.Bridge
