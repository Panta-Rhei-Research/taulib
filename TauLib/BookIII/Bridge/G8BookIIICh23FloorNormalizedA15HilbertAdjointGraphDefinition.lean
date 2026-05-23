import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Hilbert-Adjoint Graph Definition

This module defines the actual Hilbert-adjoint graph object used by the
remaining A1.5 reverse-inclusion proof.

The previous layer exposed a graph-candidate target.  Here we make the graph
law itself proof-facing:

```text
candidate u
  -> selected Kirchhoff representative rep(u)
  -> selected L2 output w(u)
  -> w(u) is square-integrable
  -> the adjoint pairing identity holds against every closed Kirchhoff test
  -> the output/pairing law is the Hilbert-adjoint graph law
```

This still does not prove the compact-graph adjoint theorem.  It gives the
next proof a precise object to construct and proves that such an object is
sufficient for the Hilbert-adjoint graph candidate source.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- POINTWISE HILBERT-ADJOINT GRAPH OBJECT
-- ============================================================

/-- A pointwise Hilbert-adjoint graph candidate for the selected Ch.23
    Kirchhoff operator.

The selected representative is the graph-domain function side.  The
`adjointOutput` is the `L2` element witnessing membership in the Hilbert
adjoint graph.  The all-test pairing law is deliberately universal over the
closed Kirchhoff test presentation, so a finite diagnostic subset cannot
inhabit the graph law. -/
structure G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObject where
  selectedRepresentative :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain
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
  selectedRepresentativeIsFunctionSide : Prop
  selectedRepresentativeIsFunctionSideWitness :
    selectedRepresentativeIsFunctionSide
  status : SpineStatus := .conditional_interface

/-- The pointwise graph-membership predicate carried by a Hilbert-adjoint graph
    object. -/
def G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObject.membership
    (graph :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObject) :
    Prop :=
  graph.outputInSelectedL2 ∧
    graph.outputRepresentsAdjointFunctional ∧
      (∀ test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest,
        graph.adjointPairingIdentityAgainstClosedTests test) ∧
        graph.pairingLawIdentifiesHilbertAdjointGraph

/-- A graph object witnesses its own graph membership. -/
theorem G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObject.membershipWitness
    (graph :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObject) :
    graph.membership :=
  ⟨graph.outputInSelectedL2Witness,
    graph.outputRepresentsAdjointFunctionalWitness,
    graph.adjointPairingIdentityWitness,
    graph.pairingLawIdentifiesHilbertAdjointGraphWitness⟩

/-- The all-test adjoint pairing readout carried by a graph object. -/
def G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObject.allTestPairing
    (graph :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObject) :
    Prop :=
  ∀ test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest,
    graph.adjointPairingIdentityAgainstClosedTests test

/-- A graph object supplies its all-test adjoint pairing readout. -/
theorem G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObject.allTestPairingWitness
    (graph :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObject) :
    graph.allTestPairing :=
  graph.adjointPairingIdentityWitness

-- ============================================================
-- GLOBAL GRAPH-DEFINITION SOURCE
-- ============================================================

/-- A source of Hilbert-adjoint graph objects for all actual adjoint
    candidates, plus the analytic consequences needed by A1.5.

This is the next sharp theorem target.  It separates the definition of the
Hilbert adjoint graph from the downstream regularity and boundary-forcing
work. -/
structure G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource where
  candidate : Type 1
  candidateNonempty : Nonempty candidate
  graphObject :
    candidate →
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObject
  graphObjectIsActualHilbertAdjointGraph : Prop
  graphObjectIsActualHilbertAdjointGraphWitness :
    graphObjectIsActualHilbertAdjointGraph
  selectedRepresentativeAlignmentAt :
    candidate → Prop
  selectedRepresentativeAlignmentWitness :
    ∀ u : candidate, selectedRepresentativeAlignmentAt u
  selectedRepresentativeAlignmentIsExact : Prop
  selectedRepresentativeAlignmentIsExactWitness :
    selectedRepresentativeAlignmentIsExact
  distributionalAdjointEquationAt :
    candidate → Prop
  distributionalAdjointEquationAtWitness :
    ∀ u : candidate, distributionalAdjointEquationAt u
  graphH2TraceRecoveryAt :
    candidate → Prop
  graphH2TraceRecoveryAtWitness :
    ∀ u : candidate, graphH2TraceRecoveryAt u
  boundaryTraceAnnihilatorAt :
    candidate → Prop
  boundaryTraceAnnihilatorAtWitness :
    ∀ u : candidate, boundaryTraceAnnihilatorAt u
  boundaryTraceForcesKirchhoffAt :
    candidate → Prop
  boundaryTraceForcesKirchhoffAtWitness :
    ∀ u : candidate, boundaryTraceForcesKirchhoffAt u
  reverseInclusionIntoSelectedKirchhoffDomainAt :
    candidate → Prop
  reverseInclusionIntoSelectedKirchhoffDomainAtWitness :
    ∀ u : candidate,
      reverseInclusionIntoSelectedKirchhoffDomainAt u
  noSelectedDomainShortcut : Prop
  noSelectedDomainShortcutWitness :
    noSelectedDomainShortcut
  noFiniteDiagnosticSubstitute : Prop
  noFiniteDiagnosticSubstituteWitness :
    noFiniteDiagnosticSubstitute
  status : SpineStatus := .conditional_interface

/-- Target for constructing the Hilbert-adjoint graph definition source. -/
def G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource

-- ============================================================
-- READOUTS FROM THE GRAPH-DEFINITION SOURCE
-- ============================================================

/-- Every graph object supplied by the definition source is a member of the
    Hilbert adjoint graph. -/
def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource.graphMembershipAll
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource) :
    Prop :=
  ∀ u : source.candidate, (source.graphObject u).membership

theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource.graphMembershipAllWitness
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource) :
    source.graphMembershipAll :=
  fun u => (source.graphObject u).membershipWitness

/-- The global graph law combines actual Hilbert-adjoint graph provenance with
    pointwise membership. -/
def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource.globalGraphLaw
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource) :
    Prop :=
  source.graphObjectIsActualHilbertAdjointGraph ∧
    source.graphMembershipAll

theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource.globalGraphLawWitness
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource) :
    source.globalGraphLaw :=
  ⟨source.graphObjectIsActualHilbertAdjointGraphWitness,
    source.graphMembershipAllWitness⟩

/-- The selected representative of a candidate is read from its graph object. -/
def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource.selectedRepresentative
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource)
    (u : source.candidate) :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain :=
  (source.graphObject u).selectedRepresentative

/-- The graph object's all-test pairing supplies the Green pairing slot of the
    candidate-source route. -/
def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource.greenPairingAgainstClosedTestsAt
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource)
    (u : source.candidate)
    (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest) :
    Prop :=
  (source.graphObject u).adjointPairingIdentityAgainstClosedTests test

theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource.greenPairingAgainstClosedTestsAtWitness
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource) :
    ∀ (u : source.candidate)
      (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest),
        source.greenPairingAgainstClosedTestsAt u test :=
  fun u test => (source.graphObject u).adjointPairingIdentityWitness test

-- ============================================================
-- ADAPTER TO THE HILBERT-ADJOINT GRAPH CANDIDATE SOURCE
-- ============================================================

/-- A Hilbert-adjoint graph definition source supplies the graph-candidate
    source from the previous layer. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource.toHilbertAdjointGraphCandidateSource
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource
    where
  candidate := source.candidate
  candidateNonempty := source.candidateNonempty
  selectedRepresentative := source.selectedRepresentative
  hilbertAdjointGraphMembershipAt :=
    fun u => (source.graphObject u).membership
  hilbertAdjointGraphMembershipWitness :=
    source.graphMembershipAllWitness
  selectedRepresentativeAlignedAt :=
    source.selectedRepresentativeAlignmentAt
  selectedRepresentativeAlignedWitness :=
    source.selectedRepresentativeAlignmentWitness
  distributionalAdjointEquationAt :=
    source.distributionalAdjointEquationAt
  distributionalAdjointEquationAtWitness :=
    source.distributionalAdjointEquationAtWitness
  graphH2TraceRecoveryAt :=
    source.graphH2TraceRecoveryAt
  graphH2TraceRecoveryAtWitness :=
    source.graphH2TraceRecoveryAtWitness
  greenPairingAgainstClosedTestsAt :=
    source.greenPairingAgainstClosedTestsAt
  greenPairingAgainstClosedTestsAtWitness :=
    source.greenPairingAgainstClosedTestsAtWitness
  boundaryTraceAnnihilatorAt :=
    source.boundaryTraceAnnihilatorAt
  boundaryTraceAnnihilatorAtWitness :=
    source.boundaryTraceAnnihilatorAtWitness
  boundaryTraceForcesKirchhoffAt :=
    source.boundaryTraceForcesKirchhoffAt
  boundaryTraceForcesKirchhoffAtWitness :=
    source.boundaryTraceForcesKirchhoffAtWitness
  reverseInclusionIntoSelectedKirchhoffDomainAt :=
    source.reverseInclusionIntoSelectedKirchhoffDomainAt
  reverseInclusionIntoSelectedKirchhoffDomainAtWitness :=
    source.reverseInclusionIntoSelectedKirchhoffDomainAtWitness
  graphMembershipIsHilbertAdjointOperatorGraph :=
    source.globalGraphLaw
  graphMembershipIsHilbertAdjointOperatorGraphWitness :=
    source.globalGraphLawWitness
  selectedRepresentativeAlignmentIsExact :=
    source.selectedRepresentativeAlignmentIsExact
  selectedRepresentativeAlignmentIsExactWitness :=
    source.selectedRepresentativeAlignmentIsExactWitness
  noSelectedDomainShortcut :=
    source.noSelectedDomainShortcut
  noSelectedDomainShortcutWitness :=
    source.noSelectedDomainShortcutWitness
  noFiniteDiagnosticSubstitute :=
    source.noFiniteDiagnosticSubstitute
  noFiniteDiagnosticSubstituteWitness :=
    source.noFiniteDiagnosticSubstituteWitness
  status := .conditional_interface

/-- A graph-definition source proves the previous graph-candidate target. -/
theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource.toHilbertAdjointGraphCandidateTarget
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateTarget :=
  ⟨source.toHilbertAdjointGraphCandidateSource⟩

/-- Target-level adapter from the graph-definition target to the previous
    graph-candidate target. -/
theorem
    g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateTarget_ofGraphDefinition
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateTarget :=
  target.elim fun source =>
    source.toHilbertAdjointGraphCandidateTarget

/-- A graph-definition target is sufficient for pointwise adjoint-domain
    realization. -/
theorem
    g8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget_ofGraphDefinition
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget) :
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget :=
  g8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget_ofHilbertAdjointGraphCandidates
    (g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateTarget_ofGraphDefinition
      target)

/-- A graph-definition target is sufficient for A1.5 maximality. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofGraphDefinition
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofHilbertAdjointGraphCandidates
    (g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateTarget_ofGraphDefinition
      target)

-- ============================================================
-- EXACT COMPACT-GRAPH REALIZATION ALIGNMENT
-- ============================================================

/-- The pointwise Hilbert-adjoint graph object selected by a compact-graph
    adjoint-domain realization source.

The output is the selected graph Laplacian of the selected representative.
The graph-law and all-test pairing fields remain supplied by the compact
realization source, not by a selected-domain shortcut. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource.toHilbertAdjointGraphObject
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource)
    (u : source.adjoint) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObject
    where
  selectedRepresentative := source.toSelected u
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
  outputSquareIntegrableAligned := rfl
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
  selectedRepresentativeIsFunctionSide :=
    G8BookIIICh23FloorNormalizedA15SelectedTraceRecovery
      (source.toSelected u)
  selectedRepresentativeIsFunctionSideWitness :=
    g8BookIIICh23FloorNormalizedA15SelectedTraceRecovery_closed
      (source.toSelected u)
  status := .conditional_interface

/-- A compact-graph adjoint-domain realization source supplies the
    Hilbert-adjoint graph-definition source directly.

This is the non-circular alignment theorem for the new target: the compact
realization source is still the load-bearing input, and the graph-definition
source is exactly the Hilbert-adjoint graph readout of that input. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource.toHilbertAdjointGraphDefinitionSource
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource
    where
  candidate := source.adjoint
  candidateNonempty := source.adjointNonempty
  graphObject :=
    source.toHilbertAdjointGraphObject
  graphObjectIsActualHilbertAdjointGraph :=
    source.representsHilbertAdjointGraph
  graphObjectIsActualHilbertAdjointGraphWitness :=
    source.representsHilbertAdjointGraphWitness
  selectedRepresentativeAlignmentAt :=
    fun _ => source.representsHilbertAdjointGraph
  selectedRepresentativeAlignmentWitness :=
    fun _ => source.representsHilbertAdjointGraphWitness
  selectedRepresentativeAlignmentIsExact :=
    source.representsHilbertAdjointGraph ∧
      source.noSelectedDomainShortcut
  selectedRepresentativeAlignmentIsExactWitness :=
    ⟨source.representsHilbertAdjointGraphWitness,
      source.noSelectedDomainShortcutWitness⟩
  distributionalAdjointEquationAt :=
    fun _ => source.distributionalAdjointEquation
  distributionalAdjointEquationAtWitness :=
    fun _ => source.distributionalAdjointEquationWitness
  graphH2TraceRecoveryAt :=
    fun _ => source.graphH2TraceRecoveryFromAdjointEquation
  graphH2TraceRecoveryAtWitness :=
    fun _ => source.graphH2TraceRecoveryWitness
  boundaryTraceAnnihilatorAt :=
    fun _ => source.boundaryTraceAnnihilatorClassification
  boundaryTraceAnnihilatorAtWitness :=
    fun _ => source.boundaryTraceAnnihilatorClassificationWitness
  boundaryTraceForcesKirchhoffAt :=
    fun _ => source.boundaryTraceForcesKirchhoffConditions
  boundaryTraceForcesKirchhoffAtWitness :=
    fun _ => source.boundaryTraceForcesKirchhoffConditionsWitness
  reverseInclusionIntoSelectedKirchhoffDomainAt :=
    fun _ => source.reverseInclusionIntoSelectedKirchhoffDomain
  reverseInclusionIntoSelectedKirchhoffDomainAtWitness :=
    fun _ => source.reverseInclusionWitness
  noSelectedDomainShortcut :=
    source.noSelectedDomainShortcut
  noSelectedDomainShortcutWitness :=
    source.noSelectedDomainShortcutWitness
  noFiniteDiagnosticSubstitute :=
    source.noFiniteDiagnosticSubstitute
  noFiniteDiagnosticSubstituteWitness :=
    source.noFiniteDiagnosticSubstituteWitness
  status := .conditional_interface

/-- Target-level adapter: compact-graph adjoint-domain realization supplies
    the Hilbert-adjoint graph-definition target. -/
theorem
    g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget_ofCompactGraphAdjointDomainRealization
    (target :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget) :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget :=
  target.elim fun source =>
    ⟨source.toHilbertAdjointGraphDefinitionSource⟩

/-- Conversely, the Hilbert-adjoint graph-definition target is sufficient for
    the compact-graph adjoint-domain realization target through the existing
    pointwise realization adapter. -/
theorem
    g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_ofHilbertAdjointGraphDefinition
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget :=
  g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_ofPointwiseRealization
    (g8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget_ofGraphDefinition
      target)

/-- The Hilbert-adjoint graph-definition target is theorem-equivalent to the
    compact-graph adjoint-domain realization target.  This records exactly
    what remains to be proved, without collapsing the compact-graph analytic
    payload into selected-domain bookkeeping. -/
theorem
    g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget_iff_compactGraphAdjointDomainRealization :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget ↔
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget :=
  ⟨g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_ofHilbertAdjointGraphDefinition,
    g8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionTarget_ofCompactGraphAdjointDomainRealization⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Without an `L2` output, a pointwise graph object cannot supply graph
    membership. -/
structure G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObjectWithoutL2Output where
  graph :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObject
  missingL2Output :
    ¬ graph.outputInSelectedL2

theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObjectWithoutL2Output.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObjectWithoutL2Output) :
    False :=
  gap.missingL2Output gap.graph.outputInSelectedL2Witness

/-- Without all-test pairing, a pointwise graph object cannot supply graph
    membership. -/
structure G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObjectWithoutAllTestPairing where
  graph :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObject
  missingAllTestPairing :
    ¬ graph.allTestPairing

theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObjectWithoutAllTestPairing.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphObjectWithoutAllTestPairing) :
    False :=
  gap.missingAllTestPairing gap.graph.allTestPairingWitness

/-- A graph-definition source without exact representative alignment cannot
    feed the graph-candidate route. -/
structure
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionWithoutRepresentativeAlignment
    where
  source :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionSource
  missingAlignment :
    ¬ source.selectedRepresentativeAlignmentIsExact

theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionWithoutRepresentativeAlignment.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphDefinitionWithoutRepresentativeAlignment) :
    False :=
  gap.missingAlignment
    gap.source.selectedRepresentativeAlignmentIsExactWitness

end Tau.BookIII.Bridge
