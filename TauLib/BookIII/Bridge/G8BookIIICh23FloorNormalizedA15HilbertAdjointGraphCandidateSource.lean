import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15AdjointDomainRealizationProofWork

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Hilbert-Adjoint Graph Candidate Source

This module takes the next load-bearing step below the pointwise adjoint-domain
realization target.

The previous layer isolated:

```text
G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget
```

Here we split the first hard phrase, "actual Hilbert-adjoint candidate", into
a pointwise graph-candidate source:

```text
candidate u in the Hilbert adjoint graph
  -> selected Kirchhoff representative rep(u)
  -> representative alignment with the Hilbert adjoint graph
  -> distributional equation / graph-H2 recovery / all-test Green pairing
  -> boundary annihilator forcing
  -> reverse inclusion
```

This is still an upstream A1.5 module.  It does not import spectral, A3,
final RH, O3, determinant, divisor, accepted-coverage, or completion sources.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- HILBERT-ADJOINT GRAPH CANDIDATE SOURCE
-- ============================================================

/-- A proof-facing source for actual Hilbert-adjoint graph candidates.

The carrier is the genuine adjoint-graph side of the proof.  The selected
Kirchhoff representative is allowed only with explicit graph-membership and
representative-alignment witnesses; the source therefore cannot be inhabited
by merely choosing the selected Kirchhoff domain as a shortcut. -/
structure
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource
    where
  candidate : Type 1
  candidateNonempty : Nonempty candidate
  selectedRepresentative :
    candidate →
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain
  hilbertAdjointGraphMembershipAt :
    candidate → Prop
  hilbertAdjointGraphMembershipWitness :
    ∀ u : candidate, hilbertAdjointGraphMembershipAt u
  selectedRepresentativeAlignedAt :
    candidate → Prop
  selectedRepresentativeAlignedWitness :
    ∀ u : candidate, selectedRepresentativeAlignedAt u
  distributionalAdjointEquationAt :
    candidate → Prop
  distributionalAdjointEquationAtWitness :
    ∀ u : candidate, distributionalAdjointEquationAt u
  graphH2TraceRecoveryAt :
    candidate → Prop
  graphH2TraceRecoveryAtWitness :
    ∀ u : candidate, graphH2TraceRecoveryAt u
  greenPairingAgainstClosedTestsAt :
    candidate →
      G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest →
        Prop
  greenPairingAgainstClosedTestsAtWitness :
    ∀ (u : candidate)
      (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest),
        greenPairingAgainstClosedTestsAt u test
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
  graphMembershipIsHilbertAdjointOperatorGraph : Prop
  graphMembershipIsHilbertAdjointOperatorGraphWitness :
    graphMembershipIsHilbertAdjointOperatorGraph
  selectedRepresentativeAlignmentIsExact : Prop
  selectedRepresentativeAlignmentIsExactWitness :
    selectedRepresentativeAlignmentIsExact
  noSelectedDomainShortcut : Prop
  noSelectedDomainShortcutWitness :
    noSelectedDomainShortcut
  noFiniteDiagnosticSubstitute : Prop
  noFiniteDiagnosticSubstituteWitness :
    noFiniteDiagnosticSubstitute
  status : SpineStatus := .conditional_interface

/-- Target for constructing the Hilbert-adjoint graph candidate source. -/
def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource

-- ============================================================
-- GLOBAL READOUTS FROM THE POINTWISE GRAPH SOURCE
-- ============================================================

/-- Every candidate lies in the Hilbert-adjoint graph. -/
def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource.hilbertAdjointGraphMembershipAll
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource) :
    Prop :=
  ∀ u : source.candidate,
    source.hilbertAdjointGraphMembershipAt u

theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource.hilbertAdjointGraphMembershipAllWitness
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource) :
    source.hilbertAdjointGraphMembershipAll :=
  source.hilbertAdjointGraphMembershipWitness

/-- Every selected representative is aligned with its Hilbert-adjoint graph
    candidate. -/
def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource.selectedRepresentativeAlignmentAll
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource) :
    Prop :=
  ∀ u : source.candidate,
    source.selectedRepresentativeAlignedAt u

theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource.selectedRepresentativeAlignmentAllWitness
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource) :
    source.selectedRepresentativeAlignmentAll :=
  source.selectedRepresentativeAlignedWitness

/-- The global Hilbert-adjoint graph readout records both graph
    membership and exact representative alignment. -/
def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource.globalGraphReadout
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource) :
    Prop :=
  source.graphMembershipIsHilbertAdjointOperatorGraph ∧
    source.hilbertAdjointGraphMembershipAll

theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource.globalGraphReadoutWitness
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource) :
    source.globalGraphReadout :=
  ⟨source.graphMembershipIsHilbertAdjointOperatorGraphWitness,
    source.hilbertAdjointGraphMembershipAllWitness⟩

/-- The global selected-representative readout records exact alignment of
    selected Kirchhoff representatives with the Hilbert-adjoint graph. -/
def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource.globalRepresentativeAlignment
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource) :
    Prop :=
  source.selectedRepresentativeAlignmentIsExact ∧
    source.selectedRepresentativeAlignmentAll

theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource.globalRepresentativeAlignmentWitness
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource) :
    source.globalRepresentativeAlignment :=
  ⟨source.selectedRepresentativeAlignmentIsExactWitness,
    source.selectedRepresentativeAlignmentAllWitness⟩

-- ============================================================
-- ADAPTER TO THE POINTWISE REALIZATION TARGET
-- ============================================================

/-- A Hilbert-adjoint graph candidate source supplies the pointwise
    adjoint-domain realization source isolated in the previous layer. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource.toPointwiseAdjointDomainRealizationSource
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource) :
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource
    where
  adjoint := source.candidate
  adjointNonempty := source.candidateNonempty
  toSelected := source.selectedRepresentative
  representsHilbertAdjointGraph := source.globalGraphReadout
  representsHilbertAdjointGraphWitness :=
    source.globalGraphReadoutWitness
  selectedRepresentativeMatchesHilbertAdjointGraph :=
    source.globalRepresentativeAlignment
  selectedRepresentativeMatchesWitness :=
    source.globalRepresentativeAlignmentWitness
  candidateBelongsToHilbertAdjointGraph :=
    source.hilbertAdjointGraphMembershipAt
  candidateBelongsToHilbertAdjointGraphWitness :=
    source.hilbertAdjointGraphMembershipWitness
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
  noSelectedDomainShortcut :=
    source.noSelectedDomainShortcut
  noSelectedDomainShortcutWitness :=
    source.noSelectedDomainShortcutWitness
  noFiniteDiagnosticSubstitute :=
    source.noFiniteDiagnosticSubstitute
  noFiniteDiagnosticSubstituteWitness :=
    source.noFiniteDiagnosticSubstituteWitness
  status := .conditional_interface

/-- A Hilbert-adjoint graph candidate source proves the pointwise realization
    target. -/
theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource.toPointwiseAdjointDomainRealizationTarget
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource) :
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget :=
  ⟨source.toPointwiseAdjointDomainRealizationSource⟩

/-- Target-level adapter from Hilbert-adjoint graph candidates to the
    pointwise realization target. -/
theorem
    g8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget_ofHilbertAdjointGraphCandidates
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateTarget) :
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget :=
  target.elim fun source =>
    source.toPointwiseAdjointDomainRealizationTarget

/-- Hilbert-adjoint graph candidates are sufficient for compact-graph
    adjoint-domain realization. -/
theorem
    g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_ofHilbertAdjointGraphCandidates
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateTarget) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget :=
  g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_ofPointwiseRealization
    (g8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget_ofHilbertAdjointGraphCandidates
      target)

/-- Hilbert-adjoint graph candidates are sufficient for A1.5 maximality. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofHilbertAdjointGraphCandidates
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofPointwiseRealization
    (g8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget_ofHilbertAdjointGraphCandidates
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Missing pointwise Hilbert-adjoint graph membership refutes the candidate
    source. -/
structure
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateWithoutMembership
    where
  source :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource
  missingMembership :
    ¬ source.hilbertAdjointGraphMembershipAll

theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateWithoutMembership.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateWithoutMembership) :
    False :=
  gap.missingMembership
    gap.source.hilbertAdjointGraphMembershipAllWitness

/-- Missing exact representative alignment refutes the candidate source. -/
structure
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateWithoutRepresentativeAlignment
    where
  source :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource
  missingRepresentativeAlignment :
    ¬ source.globalRepresentativeAlignment

theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateWithoutRepresentativeAlignment.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateWithoutRepresentativeAlignment) :
    False :=
  gap.missingRepresentativeAlignment
    gap.source.globalRepresentativeAlignmentWitness

/-- Missing reverse inclusion blocks the Hilbert-adjoint graph candidate route
    to A1.5 maximality. -/
structure
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateWithoutReverseInclusion
    where
  source :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateSource
  missingReverseInclusion :
    ¬ (∀ u : source.candidate,
      source.reverseInclusionIntoSelectedKirchhoffDomainAt u)

theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateWithoutReverseInclusion.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphCandidateWithoutReverseInclusion) :
    False :=
  gap.missingReverseInclusion
    gap.source.reverseInclusionIntoSelectedKirchhoffDomainAtWitness

end Tau.BookIII.Bridge
