import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRoute

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Hilbert-Adjoint Graph Predicate Route Construction

This module builds the lower graph-predicate route from the concrete A1.5
adjoint-calculus engine.

The construction is deliberately direct:

* the adjoint carrier is the engine candidate carrier;
* the selected representative is the engine realization map;
* the `L2` output is the selected graph Laplacian of that representative;
* all-test pairing is read against the closed Kirchhoff test presentation;
* the finite endpoint trace readout supplies the boundary annihilator and
  Kirchhoff forcing fields.

This is still not an unconditional compact-graph adjoint theorem: the engine
source itself carries the genuine adjoint-domain coverage and reverse-inclusion
payload.  The point here is that, once that engine is present, the full
Hilbert-adjoint graph-predicate route is now constructed explicitly rather
than routed through the compact-graph realization equivalence.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- POINTWISE L2 OUTPUT / ALL-TEST PAIRING EVIDENCE
-- ============================================================

/-- The concrete engine supplies the `L2` output and all-test pairing evidence
    for a pointwise Hilbert-adjoint graph candidate. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.toHilbertAdjointGraphL2OutputEvidence
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource)
    (u : engine.candidates.point) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphL2OutputEvidence
      engine.candidates.point u
    where
  adjointOutput :=
    g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian
      (engine.candidates.realize u)
  outputInSelectedL2 :=
    G8BookIIICh23FloorNormalizedA13L2Output.squareIntegrable
      (g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian
        (engine.candidates.realize u))
  outputInSelectedL2Witness :=
    (g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian
      (engine.candidates.realize u)).squareIntegrableWitness
  outputSquareIntegrableAligned :=
    rfl
  outputRepresentsAdjointFunctional :=
    engine.candidates.representsFullAdjointDomain ∧
      engine.candidates.realizationUsesSelectedGraphDomain ∧
        engine.presentationsUseSameSelectedA13Domain
  outputRepresentsAdjointFunctionalWitness :=
    ⟨engine.candidates.representsFullAdjointDomainWitness,
      engine.candidates.realizationUsesSelectedGraphDomainWitness,
      engine.presentationsUseSameSelectedA13DomainWitness⟩
  adjointPairingIdentityAgainstClosedTests :=
    fun test =>
      G8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity
        (engine.candidates.realize u)
        (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
          |>.realize test)
  adjointPairingIdentityWitness :=
    fun test =>
      g8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity_closed
        (engine.candidates.realize u)
        (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
          |>.realize test)
  pairingLawIdentifiesHilbertAdjointGraph :=
    engine.candidates.representsFullAdjointDomain
  pairingLawIdentifiesHilbertAdjointGraphWitness :=
    engine.candidates.representsFullAdjointDomainWitness
  status := .conditional_interface

/-- The concrete engine defines the actual graph predicate by the existential
    `L2` output/all-test pairing law. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.toActualHilbertAdjointGraphPredicateSource
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource) :
    G8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource
    where
  candidate :=
    engine.candidates.point
  candidateNonempty :=
    engine.candidates.pointNonempty
  hilbertAdjointGraphPredicate :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphExistsL2Output u
  predicateIffExistsL2Output :=
    fun _ => Iff.rfl
  predicateMembershipWitness :=
    fun u =>
      ⟨engine.toHilbertAdjointGraphL2OutputEvidence u⟩
  graphPredicateIsActualHilbertAdjointDomain :=
    engine.candidates.representsFullAdjointDomain ∧
      engine.tests.exhaustsSelectedKirchhoffDomain
  graphPredicateIsActualHilbertAdjointDomainWitness :=
    ⟨engine.candidates.representsFullAdjointDomainWitness,
      engine.tests.exhaustsSelectedKirchhoffDomainWitness⟩
  noFiniteTestSubsetDefinition :=
    engine.candidates.noFiniteDiagnosticSubstitute ∧
      engine.tests.noFiniteDiagnosticSubstitute
  noFiniteTestSubsetDefinitionWitness :=
    ⟨engine.candidates.noFiniteDiagnosticSubstituteWitness,
      engine.tests.noFiniteDiagnosticSubstituteWitness⟩
  status := .conditional_interface

-- ============================================================
-- SELECTED REPRESENTATIVE / ANALYTIC STONES
-- ============================================================

/-- The engine realization map is the selected representative extraction for
    the graph-predicate route. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.toSelectedRepresentativeExtractionSource
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource) :
    G8BookIIICh23FloorNormalizedA15SelectedRepresentativeExtractionSource
    where
  graphPredicate :=
    engine.toActualHilbertAdjointGraphPredicateSource
  selectedRepresentative :=
    engine.candidates.realize
  selectedRepresentativeExtractedAt :=
    fun u =>
      engine.candidates.representsFullAdjointDomain ∧
        G8BookIIICh23FloorNormalizedA15SelectedTraceRecovery
          (engine.candidates.realize u)
  selectedRepresentativeExtractedWitness :=
    fun u =>
      ⟨engine.candidates.representsFullAdjointDomainWitness,
        g8BookIIICh23FloorNormalizedA15SelectedTraceRecovery_closed
          (engine.candidates.realize u)⟩
  selectedRepresentativeCompatibleWithA13At :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15SelectedTraceRecovery
        (engine.candidates.realize u)
  selectedRepresentativeCompatibleWithA13Witness :=
    fun u =>
      g8BookIIICh23FloorNormalizedA15SelectedTraceRecovery_closed
        (engine.candidates.realize u)
  selectedRepresentativeAlignmentIsExact :=
    engine.presentationsUseSameSelectedA13Domain ∧
      engine.candidates.representsFullAdjointDomain
  selectedRepresentativeAlignmentIsExactWitness :=
    ⟨engine.presentationsUseSameSelectedA13DomainWitness,
      engine.candidates.representsFullAdjointDomainWitness⟩
  noSelectedDomainShortcut :=
    engine.candidates.noFiniteDiagnosticSubstitute ∧
      engine.candidates.representsFullAdjointDomain
  noSelectedDomainShortcutWitness :=
    ⟨engine.candidates.noFiniteDiagnosticSubstituteWitness,
      engine.candidates.representsFullAdjointDomainWitness⟩
  status := .conditional_interface

/-- Distributional second-derivative recovery for the selected representative
    of each engine candidate. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.toDistributionalEquationFromAdjointPairingSource
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource) :
    G8BookIIICh23FloorNormalizedA15DistributionalEquationFromAdjointPairingSource
    where
  extraction :=
    engine.toSelectedRepresentativeExtractionSource
  distributionalAdjointEquationAt :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15SelectedDistributionalSecondDerivativeInL2
        (engine.candidates.realize u)
  distributionalAdjointEquationAtWitness :=
    fun u =>
      g8BookIIICh23FloorNormalizedA15SelectedDistributionalSecondDerivativeInL2_closed
        (engine.candidates.realize u)
  obtainedFromInteriorSupportedKirchhoffTests :=
    engine.candidates.representsFullAdjointDomain ∧
      engine.tests.exhaustsSelectedKirchhoffDomain
  obtainedFromInteriorSupportedKirchhoffTestsWitness :=
    ⟨engine.candidates.representsFullAdjointDomainWitness,
      engine.tests.exhaustsSelectedKirchhoffDomainWitness⟩
  status := .conditional_interface

/-- Graph-`H2` and endpoint trace recovery for the selected representative of
    each engine candidate. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.toGraphH2RecoveryFromHilbertAdjointGraphSource
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource) :
    G8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphSource
    where
  distributional :=
    engine.toDistributionalEquationFromAdjointPairingSource
  graphH2TraceRecoveryAt :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15SelectedTraceRecovery
        (engine.candidates.realize u)
  graphH2TraceRecoveryAtWitness :=
    fun u =>
      g8BookIIICh23FloorNormalizedA15SelectedTraceRecovery_closed
        (engine.candidates.realize u)
  recoveredFromL2OutputAndDistributionalSecondDerivative :=
    ∀ u : engine.candidates.point,
      G8BookIIICh23FloorNormalizedA15SelectedAdjointEquationInL2
          (engine.candidates.realize u) ∧
        G8BookIIICh23FloorNormalizedA15SelectedDistributionalSecondDerivativeInL2
          (engine.candidates.realize u)
  recoveredFromL2OutputAndDistributionalSecondDerivativeWitness :=
    fun u =>
      ⟨g8BookIIICh23FloorNormalizedA15SelectedAdjointEquationInL2_closed
          (engine.candidates.realize u),
        g8BookIIICh23FloorNormalizedA15SelectedDistributionalSecondDerivativeInL2_closed
          (engine.candidates.realize u)⟩
  status := .conditional_interface

/-- Green identity against every closed Kirchhoff test, read through the
    closed test presentation. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.toAllTestGreenIdentityFromGraphH2Source
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource) :
    G8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source
    where
  graphH2 :=
    engine.toGraphH2RecoveryFromHilbertAdjointGraphSource
  allTestGreenIdentityAt :=
    fun u test =>
      G8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity
        (engine.candidates.realize u)
        (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
          |>.realize test)
  allTestGreenIdentityAtWitness :=
    fun u test =>
      g8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity_closed
        (engine.candidates.realize u)
        (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
          |>.realize test)
  greenIdentityMatchesAdjointPairingLawAt :=
    fun u =>
      ∀ test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest,
        G8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity
          (engine.candidates.realize u)
          (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
            |>.realize test)
  greenIdentityMatchesAdjointPairingLawWitness :=
    fun u test =>
      g8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity_closed
        (engine.candidates.realize u)
        (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
          |>.realize test)
  obtainedByEdgewiseIntegrationByParts :=
    ∀ (u : engine.candidates.point)
      (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest),
        G8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenIdentity
          (engine.candidates.realize u)
          (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
            |>.realize test)
  obtainedByEdgewiseIntegrationByPartsWitness :=
    fun u test =>
      g8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenIdentity_closed
        (engine.candidates.realize u)
        (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
          |>.realize test)
  status := .conditional_interface

-- ============================================================
-- FINITE ENDPOINT TRACE / BOUNDARY ANNIHILATOR HOOKUP
-- ============================================================

/-- The finite endpoint trace readout supplies the boundary annihilator and
    Kirchhoff forcing stones for every engine candidate. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.toBoundaryAnnihilatorHookupSource
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource) :
    G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource
    where
  green :=
    engine.toAllTestGreenIdentityFromGraphH2Source
  boundaryTraceAnnihilatorAt :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
        (engine.boundaryTrace u)
  boundaryTraceAnnihilatorAtWitness :=
    fun u =>
      engine.boundaryTrace_annihilatesKirchhoff u
  boundaryTraceForcesKirchhoffAt :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.Kirchhoff
        (engine.boundaryTrace u)
  boundaryTraceForcesKirchhoffAtWitness :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.kirchhoff_of_annihilatesKirchhoff
        (engine.boundaryTrace_annihilatesKirchhoff u)
  usesClosedFiniteBoundaryAlgebra :=
    ∀ u : engine.candidates.point,
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.Kirchhoff
        (engine.boundaryTrace u)
  usesClosedFiniteBoundaryAlgebraWitness :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.kirchhoff_of_annihilatesKirchhoff
        (engine.boundaryTrace_annihilatesKirchhoff u)
  noApproximateBoundaryData :=
    engine.candidates.noFiniteDiagnosticSubstitute ∧
      engine.tests.noFiniteDiagnosticSubstitute
  noApproximateBoundaryDataWitness :=
    ⟨engine.candidates.noFiniteDiagnosticSubstituteWitness,
      engine.tests.noFiniteDiagnosticSubstituteWitness⟩
  status := .conditional_interface

-- ============================================================
-- FULL GRAPH-PREDICATE ROUTE CONSTRUCTION
-- ============================================================

/-- The concrete A1.5 engine constructs the full Hilbert-adjoint
    graph-predicate route source. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.toHilbertAdjointGraphPredicateRouteSource
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource
    where
  annihilator :=
    engine.toBoundaryAnnihilatorHookupSource
  reverseInclusionIntoSelectedKirchhoffDomainAt :=
    fun u =>
      engine.candidates.representsFullAdjointDomain ∧
        G8BookIIICh23FloorNormalizedA15SelectedTraceRecovery
          (engine.candidates.realize u) ∧
          G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.Kirchhoff
            (engine.boundaryTrace u)
  reverseInclusionIntoSelectedKirchhoffDomainAtWitness :=
    fun u =>
      ⟨engine.candidates.representsFullAdjointDomainWitness,
        g8BookIIICh23FloorNormalizedA15SelectedTraceRecovery_closed
          (engine.candidates.realize u),
        G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.kirchhoff_of_annihilatesKirchhoff
          (engine.boundaryTrace_annihilatesKirchhoff u)⟩
  reverseInclusionUsesDistributionalH2GreenAndBoundaryForcing :=
    engine.candidates.representsFullAdjointDomain ∧
      (∀ u : engine.candidates.point,
        G8BookIIICh23FloorNormalizedA15SelectedTraceRecovery
          (engine.candidates.realize u)) ∧
        (∀ u : engine.candidates.point,
          G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.Kirchhoff
            (engine.boundaryTrace u))
  reverseInclusionUsesDistributionalH2GreenAndBoundaryForcingWitness :=
    ⟨engine.candidates.representsFullAdjointDomainWitness,
      fun u =>
        g8BookIIICh23FloorNormalizedA15SelectedTraceRecovery_closed
          (engine.candidates.realize u),
      fun u =>
        G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.kirchhoff_of_annihilatesKirchhoff
          (engine.boundaryTrace_annihilatesKirchhoff u)⟩
  graphDefinitionIsGlobal :=
    engine.candidates.representsFullAdjointDomain ∧
      engine.tests.exhaustsSelectedKirchhoffDomain
  graphDefinitionIsGlobalWitness :=
    ⟨engine.candidates.representsFullAdjointDomainWitness,
      engine.tests.exhaustsSelectedKirchhoffDomainWitness⟩
  noFiniteDiagnosticSubstitute :=
    engine.candidates.noFiniteDiagnosticSubstitute ∧
      engine.tests.noFiniteDiagnosticSubstitute ∧
        engine.presentationsUseSameSelectedA13Domain
  noFiniteDiagnosticSubstituteWitness :=
    ⟨engine.candidates.noFiniteDiagnosticSubstituteWitness,
      engine.tests.noFiniteDiagnosticSubstituteWitness,
      engine.presentationsUseSameSelectedA13DomainWitness⟩
  status := .conditional_interface

/-- A concrete A1.5 engine proves the graph-predicate route target. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.toHilbertAdjointGraphPredicateRouteTarget
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget :=
  ⟨engine.toHilbertAdjointGraphPredicateRouteSource⟩

/-- Target-level constructor from the concrete A1.5 engine to the full
    Hilbert-adjoint graph-predicate route. -/
theorem
    g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget_ofAdjointCalculusEngine
    (target : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget :=
  target.elim fun engine =>
    engine.toHilbertAdjointGraphPredicateRouteTarget

/-- The Type-1 adjoint-domain presentation route now feeds the full
    graph-predicate route through the concrete engine. -/
theorem
    g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget_ofType1Presentation
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget :=
  g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget_ofAdjointCalculusEngine
    (g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofType1Presentation
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Without full adjoint-domain coverage on the engine candidate
    presentation, the graph-predicate route construction cannot be justified. -/
structure
    G8BookIIICh23FloorNormalizedA15EngineWithoutAdjointDomainCoverageForPredicateRoute
    where
  engine :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource
  missingCoverage :
    ¬ engine.candidates.representsFullAdjointDomain

theorem
    G8BookIIICh23FloorNormalizedA15EngineWithoutAdjointDomainCoverageForPredicateRoute.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15EngineWithoutAdjointDomainCoverageForPredicateRoute) :
    False :=
  gap.missingCoverage
    gap.engine.candidates.representsFullAdjointDomainWitness

/-- Without the full closed Kirchhoff-test presentation, finite endpoint
    traces alone do not justify the all-test graph-predicate route. -/
structure
    G8BookIIICh23FloorNormalizedA15EngineWithoutKirchhoffTestExhaustionForPredicateRoute
    where
  engine :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource
  missingTestExhaustion :
    ¬ engine.tests.exhaustsSelectedKirchhoffDomain

theorem
    G8BookIIICh23FloorNormalizedA15EngineWithoutKirchhoffTestExhaustionForPredicateRoute.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15EngineWithoutKirchhoffTestExhaustionForPredicateRoute) :
    False :=
  gap.missingTestExhaustion
    gap.engine.tests.exhaustsSelectedKirchhoffDomainWitness

/-- Losing the finite endpoint trace annihilator law blocks the boundary
    forcing stone of the route. -/
structure
    G8BookIIICh23FloorNormalizedA15EngineWithoutEndpointAnnihilatorForPredicateRoute
    where
  engine :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource
  missingAnnihilator :
    ¬ (∀ u : engine.candidates.point,
        G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
          (engine.boundaryTrace u))

theorem
    G8BookIIICh23FloorNormalizedA15EngineWithoutEndpointAnnihilatorForPredicateRoute.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15EngineWithoutEndpointAnnihilatorForPredicateRoute) :
    False :=
  gap.missingAnnihilator
    gap.engine.boundaryTrace_annihilatesKirchhoff

end Tau.BookIII.Bridge
