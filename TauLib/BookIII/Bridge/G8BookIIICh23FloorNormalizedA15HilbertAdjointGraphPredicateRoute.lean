import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinition

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Hilbert-Adjoint Graph Predicate Route

This module sharpens the remaining A1.5 target one step further down.

The previous layer exposed a pointwise Hilbert-adjoint graph object.  Here we
name the graph predicate itself:

```text
u in Dom(H*) iff there is an L2 output w
  such that the adjoint pairing identity holds against all selected
  Kirchhoff tests.
```

The route then records the exact analytic stones needed after this predicate:

* selected representative extraction;
* distributional equation from adjoint pairing;
* graph-H2 recovery;
* all-test Green identity;
* finite boundary-annihilator hookup;
* reverse inclusion into the selected Kirchhoff domain.

This is still a proof-carrying source layer, not a proof of A1.5 maximality by
itself.  It imports no spectral, A3, final RH, O3, determinant, divisor,
accepted-coverage, or completion modules.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- ACTUAL HILBERT-ADJOINT GRAPH PREDICATE
-- ============================================================

/-- The L2-output/all-test pairing evidence that defines pointwise membership
    in the Hilbert-adjoint graph.

The parameter `u` is deliberately present: the evidence belongs to that
candidate, even though the current upstream carrier remains abstract. -/
structure
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphL2OutputEvidence
    (candidate : Type 1) (u : candidate) where
  adjointOutput :
    G8BookIIICh23FloorNormalizedA15SelectedL2Output
  outputInSelectedL2 : Prop
  outputInSelectedL2Witness :
    outputInSelectedL2
  outputSquareIntegrableAligned :
    outputInSelectedL2 =
      G8BookIIICh23FloorNormalizedA13L2Output.squareIntegrable
        adjointOutput
  outputRepresentsAdjointFunctional : Prop
  outputRepresentsAdjointFunctionalWitness :
    outputRepresentsAdjointFunctional
  adjointPairingIdentityAgainstClosedTests :
    G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest → Prop
  adjointPairingIdentityWitness :
    ∀ test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest,
      adjointPairingIdentityAgainstClosedTests test
  pairingLawIdentifiesHilbertAdjointGraph : Prop
  pairingLawIdentifiesHilbertAdjointGraphWitness :
    pairingLawIdentifiesHilbertAdjointGraph
  status : SpineStatus := .conditional_interface

/-- The existential `L2`-output characterization of the Hilbert-adjoint graph
    predicate for a candidate. -/
def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphExistsL2Output
    {candidate : Type 1} (u : candidate) :
    Prop :=
  Nonempty
    (G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphL2OutputEvidence
      candidate u)

/-- A graph predicate is honest when it is equivalent pointwise to the
    existence of an `L2` output satisfying the all-test adjoint pairing law. -/
structure
    G8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource
    where
  candidate : Type 1
  candidateNonempty : Nonempty candidate
  hilbertAdjointGraphPredicate :
    candidate → Prop
  predicateIffExistsL2Output :
    ∀ u : candidate,
      hilbertAdjointGraphPredicate u ↔
        G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphExistsL2Output u
  predicateMembershipWitness :
    ∀ u : candidate, hilbertAdjointGraphPredicate u
  graphPredicateIsActualHilbertAdjointDomain : Prop
  graphPredicateIsActualHilbertAdjointDomainWitness :
    graphPredicateIsActualHilbertAdjointDomain
  noFiniteTestSubsetDefinition : Prop
  noFiniteTestSubsetDefinitionWitness :
    noFiniteTestSubsetDefinition
  status : SpineStatus := .conditional_interface

/-- Target for the actual Hilbert-adjoint graph predicate definition. -/
def
    G8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource

/-- Extract the `L2`-output evidence from pointwise graph membership. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource.evidence
    (source :
      G8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource)
    (u : source.candidate) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphL2OutputEvidence
      source.candidate u :=
  Classical.choice
    ((source.predicateIffExistsL2Output u).mp
      (source.predicateMembershipWitness u))

/-- Every candidate has the existential `L2` graph evidence. -/
theorem
    G8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource.existsL2OutputAll
    (source :
      G8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource) :
    ∀ u : source.candidate,
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphExistsL2Output u :=
  fun u =>
    (source.predicateIffExistsL2Output u).mp
      (source.predicateMembershipWitness u)

-- ============================================================
-- SELECTED REPRESENTATIVE EXTRACTION
-- ============================================================

/-- Selected representative extraction from the actual Hilbert-adjoint graph
    predicate.

This is the second stone in the route: graph membership is not enough unless a
selected edgewise A1.3 representative is extracted with exact alignment. -/
structure
    G8BookIIICh23FloorNormalizedA15SelectedRepresentativeExtractionSource
    where
  graphPredicate :
    G8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource
  selectedRepresentative :
    graphPredicate.candidate →
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain
  selectedRepresentativeExtractedAt :
    graphPredicate.candidate → Prop
  selectedRepresentativeExtractedWitness :
    ∀ u : graphPredicate.candidate, selectedRepresentativeExtractedAt u
  selectedRepresentativeCompatibleWithA13At :
    graphPredicate.candidate → Prop
  selectedRepresentativeCompatibleWithA13Witness :
    ∀ u : graphPredicate.candidate,
      selectedRepresentativeCompatibleWithA13At u
  selectedRepresentativeAlignmentIsExact : Prop
  selectedRepresentativeAlignmentIsExactWitness :
    selectedRepresentativeAlignmentIsExact
  noSelectedDomainShortcut : Prop
  noSelectedDomainShortcutWitness :
    noSelectedDomainShortcut
  status : SpineStatus := .conditional_interface

/-- Target for selected representative extraction. -/
def
    G8BookIIICh23FloorNormalizedA15SelectedRepresentativeExtractionTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15SelectedRepresentativeExtractionSource

-- ============================================================
-- ANALYTIC STONES AFTER GRAPH MEMBERSHIP
-- ============================================================

/-- The distributional equation obtained from the adjoint pairing identity
    against tests supported inside each lobe. -/
structure
    G8BookIIICh23FloorNormalizedA15DistributionalEquationFromAdjointPairingSource
    where
  extraction :
    G8BookIIICh23FloorNormalizedA15SelectedRepresentativeExtractionSource
  distributionalAdjointEquationAt :
    extraction.graphPredicate.candidate → Prop
  distributionalAdjointEquationAtWitness :
    ∀ u : extraction.graphPredicate.candidate,
      distributionalAdjointEquationAt u
  obtainedFromInteriorSupportedKirchhoffTests : Prop
  obtainedFromInteriorSupportedKirchhoffTestsWitness :
    obtainedFromInteriorSupportedKirchhoffTests
  status : SpineStatus := .conditional_interface

/-- Target for the distributional-equation stone. -/
def
    G8BookIIICh23FloorNormalizedA15DistributionalEquationFromAdjointPairingTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15DistributionalEquationFromAdjointPairingSource

/-- Graph-H2 recovery from `w ∈ L2` and the distributional second-derivative
    equation. -/
structure
    G8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphSource
    where
  distributional :
    G8BookIIICh23FloorNormalizedA15DistributionalEquationFromAdjointPairingSource
  graphH2TraceRecoveryAt :
    distributional.extraction.graphPredicate.candidate → Prop
  graphH2TraceRecoveryAtWitness :
    ∀ u : distributional.extraction.graphPredicate.candidate,
      graphH2TraceRecoveryAt u
  recoveredFromL2OutputAndDistributionalSecondDerivative : Prop
  recoveredFromL2OutputAndDistributionalSecondDerivativeWitness :
    recoveredFromL2OutputAndDistributionalSecondDerivative
  status : SpineStatus := .conditional_interface

/-- Target for graph-H2 recovery. -/
def
    G8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphSource

/-- All-test Green identity after graph-H2 regularity is recovered. -/
structure
    G8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source
    where
  graphH2 :
    G8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphSource
  allTestGreenIdentityAt :
    graphH2.distributional.extraction.graphPredicate.candidate →
      G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest →
        Prop
  allTestGreenIdentityAtWitness :
    ∀ (u : graphH2.distributional.extraction.graphPredicate.candidate)
      (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest),
        allTestGreenIdentityAt u test
  greenIdentityMatchesAdjointPairingLawAt :
    graphH2.distributional.extraction.graphPredicate.candidate → Prop
  greenIdentityMatchesAdjointPairingLawWitness :
    ∀ u : graphH2.distributional.extraction.graphPredicate.candidate,
      greenIdentityMatchesAdjointPairingLawAt u
  obtainedByEdgewiseIntegrationByParts : Prop
  obtainedByEdgewiseIntegrationByPartsWitness :
    obtainedByEdgewiseIntegrationByParts
  status : SpineStatus := .conditional_interface

/-- Target for the all-test Green identity stone. -/
def
    G8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Target :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source

/-- Hookup to the closed finite boundary-annihilator classification. -/
structure
    G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource
    where
  green :
    G8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source
  boundaryTraceAnnihilatorAt :
    green.graphH2.distributional.extraction.graphPredicate.candidate → Prop
  boundaryTraceAnnihilatorAtWitness :
    ∀ u : green.graphH2.distributional.extraction.graphPredicate.candidate,
      boundaryTraceAnnihilatorAt u
  boundaryTraceForcesKirchhoffAt :
    green.graphH2.distributional.extraction.graphPredicate.candidate → Prop
  boundaryTraceForcesKirchhoffAtWitness :
    ∀ u : green.graphH2.distributional.extraction.graphPredicate.candidate,
      boundaryTraceForcesKirchhoffAt u
  usesClosedFiniteBoundaryAlgebra : Prop
  usesClosedFiniteBoundaryAlgebraWitness :
    usesClosedFiniteBoundaryAlgebra
  noApproximateBoundaryData : Prop
  noApproximateBoundaryDataWitness :
    noApproximateBoundaryData
  status : SpineStatus := .conditional_interface

/-- Target for the finite boundary-annihilator hookup. -/
def
    G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource

-- ============================================================
-- FULL ROUTE ASSEMBLY
-- ============================================================

/-- The full seven-stone route from the actual Hilbert-adjoint graph predicate
    to the graph-definition source. -/
structure
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource
    where
  annihilator :
    G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource
  reverseInclusionIntoSelectedKirchhoffDomainAt :
    annihilator.green.graphH2.distributional.extraction.graphPredicate.candidate →
      Prop
  reverseInclusionIntoSelectedKirchhoffDomainAtWitness :
    ∀ u : annihilator.green.graphH2.distributional.extraction.graphPredicate.candidate,
      reverseInclusionIntoSelectedKirchhoffDomainAt u
  reverseInclusionUsesDistributionalH2GreenAndBoundaryForcing : Prop
  reverseInclusionUsesDistributionalH2GreenAndBoundaryForcingWitness :
    reverseInclusionUsesDistributionalH2GreenAndBoundaryForcing
  graphDefinitionIsGlobal : Prop
  graphDefinitionIsGlobalWitness :
    graphDefinitionIsGlobal
  noFiniteDiagnosticSubstitute : Prop
  noFiniteDiagnosticSubstituteWitness :
    noFiniteDiagnosticSubstitute
  status : SpineStatus := .conditional_interface

/-- Target for the full graph-predicate route. -/
def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource

/-- The underlying actual graph-predicate source of a route. -/
def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.graphPredicate
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource :=
  source.annihilator.green.graphH2.distributional.extraction.graphPredicate

/-- The selected representative extraction source of a route. -/
def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.extraction
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15SelectedRepresentativeExtractionSource :=
  source.annihilator.green.graphH2.distributional.extraction

/-- The `L2` output evidence attached to a route candidate. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.evidence
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource)
    (u : source.graphPredicate.candidate) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphL2OutputEvidence
      source.graphPredicate.candidate u :=
  source.graphPredicate.evidence u

/-- Convert the graph-predicate route into a pointwise graph object. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.graphObject
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource)
    (u : source.graphPredicate.candidate) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObject :=
  let evidence := source.evidence u
  { selectedRepresentative :=
      source.extraction.selectedRepresentative u
    adjointOutput :=
      evidence.adjointOutput
    outputInSelectedL2 :=
      evidence.outputInSelectedL2
    outputInSelectedL2Witness :=
      evidence.outputInSelectedL2Witness
    outputSquareIntegrableAligned :=
      evidence.outputSquareIntegrableAligned
    outputRepresentsAdjointFunctional :=
      evidence.outputRepresentsAdjointFunctional
    outputRepresentsAdjointFunctionalWitness :=
      evidence.outputRepresentsAdjointFunctionalWitness
    adjointPairingIdentityAgainstClosedTests :=
      evidence.adjointPairingIdentityAgainstClosedTests
    adjointPairingIdentityWitness :=
      evidence.adjointPairingIdentityWitness
    pairingLawIdentifiesHilbertAdjointGraph :=
      evidence.pairingLawIdentifiesHilbertAdjointGraph
    pairingLawIdentifiesHilbertAdjointGraphWitness :=
      evidence.pairingLawIdentifiesHilbertAdjointGraphWitness
    selectedRepresentativeIsFunctionSide :=
      source.extraction.selectedRepresentativeCompatibleWithA13At u
    selectedRepresentativeIsFunctionSideWitness :=
      source.extraction.selectedRepresentativeCompatibleWithA13Witness u
    status := .conditional_interface }

/-- A full graph-predicate route supplies the graph-definition source. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.toGraphDefinitionSource
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource
    where
  candidate :=
    source.graphPredicate.candidate
  candidateNonempty :=
    source.graphPredicate.candidateNonempty
  graphObject :=
    source.graphObject
  graphObjectIsActualHilbertAdjointGraph :=
    source.graphPredicate.graphPredicateIsActualHilbertAdjointDomain ∧
      source.graphDefinitionIsGlobal
  graphObjectIsActualHilbertAdjointGraphWitness :=
    ⟨source.graphPredicate.graphPredicateIsActualHilbertAdjointDomainWitness,
      source.graphDefinitionIsGlobalWitness⟩
  selectedRepresentativeAlignmentAt :=
    source.extraction.selectedRepresentativeExtractedAt
  selectedRepresentativeAlignmentWitness :=
    source.extraction.selectedRepresentativeExtractedWitness
  selectedRepresentativeAlignmentIsExact :=
    source.extraction.selectedRepresentativeAlignmentIsExact
  selectedRepresentativeAlignmentIsExactWitness :=
    source.extraction.selectedRepresentativeAlignmentIsExactWitness
  distributionalAdjointEquationAt :=
    source.annihilator.green.graphH2.distributional.distributionalAdjointEquationAt
  distributionalAdjointEquationAtWitness :=
    source.annihilator.green.graphH2.distributional.distributionalAdjointEquationAtWitness
  graphH2TraceRecoveryAt :=
    source.annihilator.green.graphH2.graphH2TraceRecoveryAt
  graphH2TraceRecoveryAtWitness :=
    source.annihilator.green.graphH2.graphH2TraceRecoveryAtWitness
  boundaryTraceAnnihilatorAt :=
    source.annihilator.boundaryTraceAnnihilatorAt
  boundaryTraceAnnihilatorAtWitness :=
    source.annihilator.boundaryTraceAnnihilatorAtWitness
  boundaryTraceForcesKirchhoffAt :=
    source.annihilator.boundaryTraceForcesKirchhoffAt
  boundaryTraceForcesKirchhoffAtWitness :=
    source.annihilator.boundaryTraceForcesKirchhoffAtWitness
  reverseInclusionIntoSelectedKirchhoffDomainAt :=
    source.reverseInclusionIntoSelectedKirchhoffDomainAt
  reverseInclusionIntoSelectedKirchhoffDomainAtWitness :=
    source.reverseInclusionIntoSelectedKirchhoffDomainAtWitness
  noSelectedDomainShortcut :=
    source.extraction.noSelectedDomainShortcut
  noSelectedDomainShortcutWitness :=
    source.extraction.noSelectedDomainShortcutWitness
  noFiniteDiagnosticSubstitute :=
    source.noFiniteDiagnosticSubstitute ∧
      source.graphPredicate.noFiniteTestSubsetDefinition ∧
        source.annihilator.noApproximateBoundaryData
  noFiniteDiagnosticSubstituteWitness :=
    ⟨source.noFiniteDiagnosticSubstituteWitness,
      source.graphPredicate.noFiniteTestSubsetDefinitionWitness,
      source.annihilator.noApproximateBoundaryDataWitness⟩
  status := .conditional_interface

/-- A compact-graph adjoint-domain realization source supplies the pointwise
    `L2` output evidence required by the actual Hilbert-adjoint graph
    predicate.

The output is the selected graph Laplacian of the selected representative.
The load-bearing graph provenance, Green law, and non-diagnostic guardrails
come from the compact-graph realization source rather than from the selected
domain alone. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource.toHilbertAdjointGraphL2OutputEvidence
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource)
    (u : source.adjoint) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphL2OutputEvidence
      source.adjoint u
    where
  adjointOutput :=
    g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian
      (source.toSelected u)
  outputInSelectedL2 :=
    G8BookIIICh23FloorNormalizedA13L2Output.squareIntegrable
      (g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian
        (source.toSelected u))
  outputInSelectedL2Witness :=
    (g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian
      (source.toSelected u)).squareIntegrableWitness
  outputSquareIntegrableAligned :=
    rfl
  outputRepresentsAdjointFunctional :=
    source.representsHilbertAdjointGraph
  outputRepresentsAdjointFunctionalWitness :=
    source.representsHilbertAdjointGraphWitness
  adjointPairingIdentityAgainstClosedTests :=
    fun _ => source.greenPairingAgainstAllKirchhoffTests
  adjointPairingIdentityWitness :=
    fun _ => source.greenPairingAgainstAllKirchhoffTestsWitness
  pairingLawIdentifiesHilbertAdjointGraph :=
    source.representsHilbertAdjointGraph
  pairingLawIdentifiesHilbertAdjointGraphWitness :=
    source.representsHilbertAdjointGraphWitness
  status := .conditional_interface

/-- A compact-graph adjoint-domain realization source gives the actual
    Hilbert-adjoint graph predicate by the `L2` output/all-test pairing law. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource.toActualHilbertAdjointGraphPredicateSource
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource) :
    G8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource
    where
  candidate :=
    source.adjoint
  candidateNonempty :=
    source.adjointNonempty
  hilbertAdjointGraphPredicate :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphExistsL2Output u
  predicateIffExistsL2Output :=
    fun _ => Iff.rfl
  predicateMembershipWitness :=
    fun u =>
      ⟨source.toHilbertAdjointGraphL2OutputEvidence u⟩
  graphPredicateIsActualHilbertAdjointDomain :=
    source.representsHilbertAdjointGraph
  graphPredicateIsActualHilbertAdjointDomainWitness :=
    source.representsHilbertAdjointGraphWitness
  noFiniteTestSubsetDefinition :=
    source.noFiniteDiagnosticSubstitute
  noFiniteTestSubsetDefinitionWitness :=
    source.noFiniteDiagnosticSubstituteWitness
  status := .conditional_interface

/-- A compact-graph adjoint-domain realization source supplies selected
    representative extraction for every Hilbert-adjoint graph candidate. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource.toSelectedRepresentativeExtractionSource
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource) :
    G8BookIIICh23FloorNormalizedA15SelectedRepresentativeExtractionSource
    where
  graphPredicate :=
    source.toActualHilbertAdjointGraphPredicateSource
  selectedRepresentative :=
    source.toSelected
  selectedRepresentativeExtractedAt :=
    fun _ => source.representsHilbertAdjointGraph
  selectedRepresentativeExtractedWitness :=
    fun _ => source.representsHilbertAdjointGraphWitness
  selectedRepresentativeCompatibleWithA13At :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15SelectedTraceRecovery
        (source.toSelected u)
  selectedRepresentativeCompatibleWithA13Witness :=
    fun u =>
      g8BookIIICh23FloorNormalizedA15SelectedTraceRecovery_closed
        (source.toSelected u)
  selectedRepresentativeAlignmentIsExact :=
    source.representsHilbertAdjointGraph ∧
      source.noSelectedDomainShortcut
  selectedRepresentativeAlignmentIsExactWitness :=
    ⟨source.representsHilbertAdjointGraphWitness,
      source.noSelectedDomainShortcutWitness⟩
  noSelectedDomainShortcut :=
    source.noSelectedDomainShortcut
  noSelectedDomainShortcutWitness :=
    source.noSelectedDomainShortcutWitness
  status := .conditional_interface

/-- Compact-graph adjoint realization supplies the distributional equation
    stone in the graph-predicate route. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource.toDistributionalEquationFromAdjointPairingSource
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource) :
    G8BookIIICh23FloorNormalizedA15DistributionalEquationFromAdjointPairingSource
    where
  extraction :=
    source.toSelectedRepresentativeExtractionSource
  distributionalAdjointEquationAt :=
    fun _ => source.distributionalAdjointEquation
  distributionalAdjointEquationAtWitness :=
    fun _ => source.distributionalAdjointEquationWitness
  obtainedFromInteriorSupportedKirchhoffTests :=
    source.distributionalAdjointEquation ∧
      source.noFiniteDiagnosticSubstitute
  obtainedFromInteriorSupportedKirchhoffTestsWitness :=
    ⟨source.distributionalAdjointEquationWitness,
      source.noFiniteDiagnosticSubstituteWitness⟩
  status := .conditional_interface

/-- Compact-graph adjoint realization supplies graph-`H2` trace recovery. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource.toGraphH2RecoveryFromHilbertAdjointGraphSource
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource) :
    G8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphSource
    where
  distributional :=
    source.toDistributionalEquationFromAdjointPairingSource
  graphH2TraceRecoveryAt :=
    fun _ => source.graphH2TraceRecoveryFromAdjointEquation
  graphH2TraceRecoveryAtWitness :=
    fun _ => source.graphH2TraceRecoveryWitness
  recoveredFromL2OutputAndDistributionalSecondDerivative :=
    source.graphH2TraceRecoveryFromAdjointEquation ∧
      source.distributionalAdjointEquation
  recoveredFromL2OutputAndDistributionalSecondDerivativeWitness :=
    ⟨source.graphH2TraceRecoveryWitness,
      source.distributionalAdjointEquationWitness⟩
  status := .conditional_interface

/-- Compact-graph adjoint realization supplies the all-test Green identity
    stone. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource.toAllTestGreenIdentityFromGraphH2Source
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource) :
    G8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source
    where
  graphH2 :=
    source.toGraphH2RecoveryFromHilbertAdjointGraphSource
  allTestGreenIdentityAt :=
    fun _ _ => source.greenPairingAgainstAllKirchhoffTests
  allTestGreenIdentityAtWitness :=
    fun _ _ => source.greenPairingAgainstAllKirchhoffTestsWitness
  greenIdentityMatchesAdjointPairingLawAt :=
    fun _ =>
      source.greenPairingAgainstAllKirchhoffTests ∧
        source.representsHilbertAdjointGraph
  greenIdentityMatchesAdjointPairingLawWitness :=
    fun _ =>
      ⟨source.greenPairingAgainstAllKirchhoffTestsWitness,
        source.representsHilbertAdjointGraphWitness⟩
  obtainedByEdgewiseIntegrationByParts :=
    source.greenPairingAgainstAllKirchhoffTests
  obtainedByEdgewiseIntegrationByPartsWitness :=
    source.greenPairingAgainstAllKirchhoffTestsWitness
  status := .conditional_interface

/-- Compact-graph adjoint realization supplies the boundary-annihilator
    hookup using the already-closed finite boundary algebra. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource.toBoundaryAnnihilatorHookupSource
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource) :
    G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource
    where
  green :=
    source.toAllTestGreenIdentityFromGraphH2Source
  boundaryTraceAnnihilatorAt :=
    fun _ => source.boundaryTraceAnnihilatorClassification
  boundaryTraceAnnihilatorAtWitness :=
    fun _ => source.boundaryTraceAnnihilatorClassificationWitness
  boundaryTraceForcesKirchhoffAt :=
    fun _ => source.boundaryTraceForcesKirchhoffConditions
  boundaryTraceForcesKirchhoffAtWitness :=
    fun _ => source.boundaryTraceForcesKirchhoffConditionsWitness
  usesClosedFiniteBoundaryAlgebra :=
    source.boundaryTraceAnnihilatorClassification ∧
      source.boundaryTraceForcesKirchhoffConditions
  usesClosedFiniteBoundaryAlgebraWitness :=
    ⟨source.boundaryTraceAnnihilatorClassificationWitness,
      source.boundaryTraceForcesKirchhoffConditionsWitness⟩
  noApproximateBoundaryData :=
    source.noFiniteDiagnosticSubstitute
  noApproximateBoundaryDataWitness :=
    source.noFiniteDiagnosticSubstituteWitness
  status := .conditional_interface

/-- A compact-graph adjoint-domain realization source supplies the full
    Hilbert-adjoint graph-predicate route. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource.toHilbertAdjointGraphPredicateRouteSource
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource
    where
  annihilator :=
    source.toBoundaryAnnihilatorHookupSource
  reverseInclusionIntoSelectedKirchhoffDomainAt :=
    fun _ => source.reverseInclusionIntoSelectedKirchhoffDomain
  reverseInclusionIntoSelectedKirchhoffDomainAtWitness :=
    fun _ => source.reverseInclusionWitness
  reverseInclusionUsesDistributionalH2GreenAndBoundaryForcing :=
    source.reverseInclusionIntoSelectedKirchhoffDomain ∧
      source.graphH2TraceRecoveryFromAdjointEquation ∧
        source.boundaryTraceForcesKirchhoffConditions
  reverseInclusionUsesDistributionalH2GreenAndBoundaryForcingWitness :=
    ⟨source.reverseInclusionWitness,
      source.graphH2TraceRecoveryWitness,
      source.boundaryTraceForcesKirchhoffConditionsWitness⟩
  graphDefinitionIsGlobal :=
    source.representsHilbertAdjointGraph ∧
      source.reverseInclusionIntoSelectedKirchhoffDomain
  graphDefinitionIsGlobalWitness :=
    ⟨source.representsHilbertAdjointGraphWitness,
      source.reverseInclusionWitness⟩
  noFiniteDiagnosticSubstitute :=
    source.noFiniteDiagnosticSubstitute
  noFiniteDiagnosticSubstituteWitness :=
    source.noFiniteDiagnosticSubstituteWitness
  status := .conditional_interface

/-- Target-level adapter: the compact-graph adjoint-domain realization theorem
    discharges the Hilbert-adjoint graph-predicate route target. -/
theorem
    g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget_ofCompactGraphAdjointDomainRealization
    (target :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget :=
  target.elim fun source =>
    ⟨source.toHilbertAdjointGraphPredicateRouteSource⟩

/-- A graph-predicate route proves the graph-definition target. -/
theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.toGraphDefinitionTarget
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget :=
  ⟨source.toGraphDefinitionSource⟩

/-- Target-level adapter from the graph-predicate route to the graph-definition
    target. -/
theorem
    g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget_ofPredicateRoute
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget :=
  target.elim fun source =>
    source.toGraphDefinitionTarget

/-- The graph-predicate route is sufficient for the previous graph-candidate
    target. -/
theorem
    g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateTarget_ofPredicateRoute
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateTarget :=
  g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateTarget_ofGraphDefinition
    (g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget_ofPredicateRoute
      target)

/-- The graph-predicate route is sufficient for pointwise adjoint-domain
    realization. -/
theorem
    g8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget_ofPredicateRoute
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget) :
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget :=
  g8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget_ofGraphDefinition
    (g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget_ofPredicateRoute
      target)

/-- The graph-predicate route is sufficient for A1.5 maximality. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofPredicateRoute
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofGraphDefinition
    (g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget_ofPredicateRoute
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A predicate not equivalent to the `L2`-output/all-test pairing law cannot
    serve as the actual Hilbert-adjoint graph definition. -/
structure
    G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutL2OutputIff
    where
  source :
    G8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource
  missingIff :
    ¬ (∀ u : source.candidate,
      source.hilbertAdjointGraphPredicate u ↔
        G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphExistsL2Output u)

theorem
    G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutL2OutputIff.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutL2OutputIff) :
    False :=
  gap.missingIff gap.source.predicateIffExistsL2Output

/-- Without selected representative extraction, graph membership alone does
    not assemble the A1.5 route. -/
structure
    G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutSelectedRepresentativeExtraction
    where
  predicate :
    G8BookIIICh23FloorNormalizedA15ActualHilbertAdjointGraphPredicateSource
  missingExtraction :
    ¬ G8BookIIICh23FloorNormalizedA15SelectedRepresentativeExtractionTarget

theorem
    G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutSelectedRepresentativeExtraction.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutSelectedRepresentativeExtraction)
    (extraction :
      G8BookIIICh23FloorNormalizedA15SelectedRepresentativeExtractionSource) :
    False :=
  gap.missingExtraction ⟨extraction⟩

/-- Without distributional equation recovery from the adjoint pairing, the
    route cannot proceed to graph-H2 regularity. -/
structure
    G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutDistributionalEquation
    where
  extraction :
    G8BookIIICh23FloorNormalizedA15SelectedRepresentativeExtractionSource
  missingDistributional :
    ¬ G8BookIIICh23FloorNormalizedA15DistributionalEquationFromAdjointPairingTarget

theorem
    G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutDistributionalEquation.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutDistributionalEquation)
    (distributional :
      G8BookIIICh23FloorNormalizedA15DistributionalEquationFromAdjointPairingSource) :
    False :=
  gap.missingDistributional ⟨distributional⟩

/-- Without graph-H2 recovery, the boundary traces and all-test Green identity
    remain unavailable. -/
structure
    G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutGraphH2Recovery
    where
  distributional :
    G8BookIIICh23FloorNormalizedA15DistributionalEquationFromAdjointPairingSource
  missingGraphH2 :
    ¬ G8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphTarget

theorem
    G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutGraphH2Recovery.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutGraphH2Recovery)
    (graphH2 :
      G8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphSource) :
    False :=
  gap.missingGraphH2 ⟨graphH2⟩

/-- Without the all-test Green identity, finite boundary-annihilator algebra
    cannot be hooked into the actual adjoint graph. -/
structure
    G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutAllTestGreenIdentity
    where
  graphH2 :
    G8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphSource
  missingGreen :
    ¬ G8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Target

theorem
    G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutAllTestGreenIdentity.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutAllTestGreenIdentity)
    (green :
      G8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source) :
    False :=
  gap.missingGreen ⟨green⟩

/-- Without the finite boundary-annihilator hookup, all-test Green identity
    alone does not yield Kirchhoff reverse inclusion. -/
structure
    G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutBoundaryAnnihilatorHookup
    where
  green :
    G8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source
  missingAnnihilator :
    ¬ G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupTarget

theorem
    G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutBoundaryAnnihilatorHookup.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15GraphPredicateWithoutBoundaryAnnihilatorHookup)
    (annihilator :
      G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource) :
    False :=
  gap.missingAnnihilator ⟨annihilator⟩

end Tau.BookIII.Bridge
