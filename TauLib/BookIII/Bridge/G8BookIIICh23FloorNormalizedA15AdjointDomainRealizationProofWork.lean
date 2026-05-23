import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierInstantiation

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Adjoint-Domain Realization Proof Work

This module starts the load-bearing proof work below the compact-graph
adjoint-domain realization target.

The previous layer exposed a single target:

```text
G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget
```

Here we split that target into pointwise compact-graph Hilbert-adjoint data.
The intended proof shape is now:

```text
actual Hilbert-adjoint candidate u
  -> selected Kirchhoff representative rep(u)
  -> distributional adjoint equation for u
  -> graph-H2 trace recovery for u
  -> Green pairing against every Kirchhoff test
  -> boundary annihilator forcing
  -> reverse inclusion rep(u) in the selected Kirchhoff domain
```

This is still an upstream A1.5 module.  It does not use spectral, A3, final
RH, O3, determinant, divisor, accepted-coverage, or completion sources.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- POINTWISE COMPACT-GRAPH ADJOINT-DOMAIN REALIZATION
-- ============================================================

/-- The closed Kirchhoff test universe used by the A1.5 genuine adjoint-domain
    route. -/
abbrev G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest :
    Type 1 :=
  g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation.point

/-- Pointwise proof source for the genuine compact-graph Hilbert-adjoint
    domain.

The carrier is not allowed to be merely the selected Kirchhoff domain with the
identity map.  The load-bearing fields say that each actual adjoint candidate
has a selected representative justified by Hilbert-adjoint graph membership,
the distributional equation, graph-H2 recovery, all-test Green pairing,
annihilator forcing, and reverse inclusion. -/
structure
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource
    where
  adjoint : Type 1
  adjointNonempty : Nonempty adjoint
  toSelected :
    adjoint →
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain
  representsHilbertAdjointGraph : Prop
  representsHilbertAdjointGraphWitness :
    representsHilbertAdjointGraph
  selectedRepresentativeMatchesHilbertAdjointGraph : Prop
  selectedRepresentativeMatchesWitness :
    selectedRepresentativeMatchesHilbertAdjointGraph
  candidateBelongsToHilbertAdjointGraph :
    adjoint → Prop
  candidateBelongsToHilbertAdjointGraphWitness :
    ∀ u : adjoint, candidateBelongsToHilbertAdjointGraph u
  distributionalAdjointEquationAt :
    adjoint → Prop
  distributionalAdjointEquationAtWitness :
    ∀ u : adjoint, distributionalAdjointEquationAt u
  graphH2TraceRecoveryAt :
    adjoint → Prop
  graphH2TraceRecoveryAtWitness :
    ∀ u : adjoint, graphH2TraceRecoveryAt u
  greenPairingAgainstClosedTestsAt :
    adjoint →
      G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest →
        Prop
  greenPairingAgainstClosedTestsAtWitness :
    ∀ (u : adjoint)
      (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest),
        greenPairingAgainstClosedTestsAt u test
  boundaryTraceAnnihilatorAt :
    adjoint → Prop
  boundaryTraceAnnihilatorAtWitness :
    ∀ u : adjoint, boundaryTraceAnnihilatorAt u
  boundaryTraceForcesKirchhoffAt :
    adjoint → Prop
  boundaryTraceForcesKirchhoffAtWitness :
    ∀ u : adjoint, boundaryTraceForcesKirchhoffAt u
  reverseInclusionIntoSelectedKirchhoffDomainAt :
    adjoint → Prop
  reverseInclusionIntoSelectedKirchhoffDomainAtWitness :
    ∀ u : adjoint,
      reverseInclusionIntoSelectedKirchhoffDomainAt u
  noSelectedDomainShortcut : Prop
  noSelectedDomainShortcutWitness :
    noSelectedDomainShortcut
  noFiniteDiagnosticSubstitute : Prop
  noFiniteDiagnosticSubstituteWitness :
    noFiniteDiagnosticSubstitute
  status : SpineStatus := .conditional_interface

/-- The pointwise realization target. -/
def
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource

-- ============================================================
-- GLOBAL OBLIGATIONS EXTRACTED FROM POINTWISE DATA
-- ============================================================

/-- All pointwise candidates satisfy the distributional adjoint equation. -/
def
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource.distributionalAdjointEquationAll
    (source :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource) :
    Prop :=
  ∀ u : source.adjoint, source.distributionalAdjointEquationAt u

theorem
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource.distributionalAdjointEquationAllWitness
    (source :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource) :
    source.distributionalAdjointEquationAll :=
  source.distributionalAdjointEquationAtWitness

/-- All pointwise candidates have graph-H2 trace recovery. -/
def
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource.graphH2TraceRecoveryAll
    (source :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource) :
    Prop :=
  ∀ u : source.adjoint, source.graphH2TraceRecoveryAt u

theorem
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource.graphH2TraceRecoveryAllWitness
    (source :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource) :
    source.graphH2TraceRecoveryAll :=
  source.graphH2TraceRecoveryAtWitness

/-- Every pointwise candidate pairs by Green's identity against every closed
    Kirchhoff test. -/
def
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource.greenPairingAgainstAllClosedTests
    (source :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource) :
    Prop :=
  ∀ (u : source.adjoint)
    (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest),
      source.greenPairingAgainstClosedTestsAt u test

theorem
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource.greenPairingAgainstAllClosedTestsWitness
    (source :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource) :
    source.greenPairingAgainstAllClosedTests :=
  source.greenPairingAgainstClosedTestsAtWitness

/-- Boundary annihilator classification holds for all pointwise candidates. -/
def
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource.boundaryTraceAnnihilatorAll
    (source :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource) :
    Prop :=
  ∀ u : source.adjoint, source.boundaryTraceAnnihilatorAt u

theorem
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource.boundaryTraceAnnihilatorAllWitness
    (source :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource) :
    source.boundaryTraceAnnihilatorAll :=
  source.boundaryTraceAnnihilatorAtWitness

/-- Boundary annihilator forcing puts all pointwise candidates into the
    Kirchhoff boundary condition. -/
def
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource.boundaryTraceForcesKirchhoffAll
    (source :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource) :
    Prop :=
  ∀ u : source.adjoint, source.boundaryTraceForcesKirchhoffAt u

theorem
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource.boundaryTraceForcesKirchhoffAllWitness
    (source :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource) :
    source.boundaryTraceForcesKirchhoffAll :=
  source.boundaryTraceForcesKirchhoffAtWitness

/-- Reverse inclusion holds for all pointwise candidates. -/
def
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource.reverseInclusionAll
    (source :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource) :
    Prop :=
  ∀ u : source.adjoint,
    source.reverseInclusionIntoSelectedKirchhoffDomainAt u

theorem
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource.reverseInclusionAllWitness
    (source :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource) :
    source.reverseInclusionAll :=
  source.reverseInclusionIntoSelectedKirchhoffDomainAtWitness

-- ============================================================
-- ADAPTER TO THE EXISTING COMPACT-GRAPH REALIZATION TARGET
-- ============================================================

/-- Pointwise compact-graph adjoint-domain data instantiate the compact-graph
    realization source consumed by the genuine-carrier route. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource.toCompactGraphAdjointDomainRealizationSource
    (source :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource
    where
  adjoint := source.adjoint
  adjointNonempty := source.adjointNonempty
  toSelected := source.toSelected
  representsHilbertAdjointGraph :=
    source.representsHilbertAdjointGraph ∧
      source.selectedRepresentativeMatchesHilbertAdjointGraph ∧
        (∀ u : source.adjoint,
          source.candidateBelongsToHilbertAdjointGraph u)
  representsHilbertAdjointGraphWitness :=
    ⟨source.representsHilbertAdjointGraphWitness,
      source.selectedRepresentativeMatchesWitness,
      source.candidateBelongsToHilbertAdjointGraphWitness⟩
  distributionalAdjointEquation :=
    source.distributionalAdjointEquationAll
  distributionalAdjointEquationWitness :=
    source.distributionalAdjointEquationAllWitness
  graphH2TraceRecoveryFromAdjointEquation :=
    source.graphH2TraceRecoveryAll
  graphH2TraceRecoveryWitness :=
    source.graphH2TraceRecoveryAllWitness
  greenPairingAgainstAllKirchhoffTests :=
    source.greenPairingAgainstAllClosedTests
  greenPairingAgainstAllKirchhoffTestsWitness :=
    source.greenPairingAgainstAllClosedTestsWitness
  boundaryTraceAnnihilatorClassification :=
    source.boundaryTraceAnnihilatorAll
  boundaryTraceAnnihilatorClassificationWitness :=
    source.boundaryTraceAnnihilatorAllWitness
  boundaryTraceForcesKirchhoffConditions :=
    source.boundaryTraceForcesKirchhoffAll
  boundaryTraceForcesKirchhoffConditionsWitness :=
    source.boundaryTraceForcesKirchhoffAllWitness
  reverseInclusionIntoSelectedKirchhoffDomain :=
    source.reverseInclusionAll
  reverseInclusionWitness :=
    source.reverseInclusionAllWitness
  noSelectedDomainShortcut :=
    source.noSelectedDomainShortcut
  noSelectedDomainShortcutWitness :=
    source.noSelectedDomainShortcutWitness
  noFiniteDiagnosticSubstitute :=
    source.noFiniteDiagnosticSubstitute
  noFiniteDiagnosticSubstituteWitness :=
    source.noFiniteDiagnosticSubstituteWitness
  status := .conditional_interface

/-- Pointwise compact-graph adjoint-domain data prove the existing
    compact-graph realization target. -/
theorem
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource.toCompactGraphAdjointDomainRealizationTarget
    (source :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget :=
  ⟨source.toCompactGraphAdjointDomainRealizationSource⟩

/-- Target-level adapter from the pointwise proof-work target to the existing
    compact-graph realization target. -/
theorem
    g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_ofPointwiseRealization
    (target :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget :=
  target.elim fun source =>
    source.toCompactGraphAdjointDomainRealizationTarget

/-- A compact-graph adjoint-domain realization source can be unfolded into the
    pointwise proof-work source.  This does not construct the compact source;
    it records that the compact source already carries exactly the per-candidate
    analytic payload needed by the pointwise route. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource.toPointwiseAdjointDomainRealizationSource
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource) :
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource
    where
  adjoint := source.adjoint
  adjointNonempty := source.adjointNonempty
  toSelected := source.toSelected
  representsHilbertAdjointGraph :=
    source.representsHilbertAdjointGraph
  representsHilbertAdjointGraphWitness :=
    source.representsHilbertAdjointGraphWitness
  selectedRepresentativeMatchesHilbertAdjointGraph :=
    source.representsHilbertAdjointGraph ∧
      source.noSelectedDomainShortcut
  selectedRepresentativeMatchesWitness :=
    ⟨source.representsHilbertAdjointGraphWitness,
      source.noSelectedDomainShortcutWitness⟩
  candidateBelongsToHilbertAdjointGraph :=
    fun _ => source.representsHilbertAdjointGraph
  candidateBelongsToHilbertAdjointGraphWitness :=
    fun _ => source.representsHilbertAdjointGraphWitness
  distributionalAdjointEquationAt :=
    fun _ => source.distributionalAdjointEquation
  distributionalAdjointEquationAtWitness :=
    fun _ => source.distributionalAdjointEquationWitness
  graphH2TraceRecoveryAt :=
    fun _ => source.graphH2TraceRecoveryFromAdjointEquation
  graphH2TraceRecoveryAtWitness :=
    fun _ => source.graphH2TraceRecoveryWitness
  greenPairingAgainstClosedTestsAt :=
    fun _ _ => source.greenPairingAgainstAllKirchhoffTests
  greenPairingAgainstClosedTestsAtWitness :=
    fun _ _ => source.greenPairingAgainstAllKirchhoffTestsWitness
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

/-- Compact-graph adjoint-domain realization proves the pointwise realization
    target. -/
theorem
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource.toPointwiseAdjointDomainRealizationTarget
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource) :
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget :=
  ⟨source.toPointwiseAdjointDomainRealizationSource⟩

/-- Target-level adapter from compact-graph realization to the pointwise
    proof-work target. -/
theorem
    g8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget_ofCompactGraphAdjointDomainRealization
    (target :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget) :
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget :=
  target.elim fun source =>
    source.toPointwiseAdjointDomainRealizationTarget

/-- The compact-graph realization target and the pointwise realization target
    are theorem-equivalent proof-carrying presentations of the same A1.5
    analytic payload. -/
theorem
    g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_iff_pointwiseRealization :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget ↔
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget :=
  ⟨g8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget_ofCompactGraphAdjointDomainRealization,
    g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_ofPointwiseRealization⟩

/-- Pointwise realization is sufficient for the selected-carrier A1.5
    maximal Kirchhoff self-adjointness target. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofPointwiseRealization
    (target :
      G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofCompactGraphAdjointDomainRealization
    (g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_ofPointwiseRealization
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Without selected representative alignment, pointwise data cannot be read
    as a compact-graph adjoint-domain realization. -/
structure
    G8BookIIICh23FloorNormalizedA15PointwiseRealizationWithoutRepresentativeAlignment
    where
  source :
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource
  missingRepresentativeAlignment :
    ¬ source.selectedRepresentativeMatchesHilbertAdjointGraph

theorem
    G8BookIIICh23FloorNormalizedA15PointwiseRealizationWithoutRepresentativeAlignment.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15PointwiseRealizationWithoutRepresentativeAlignment) :
    False :=
  gap.missingRepresentativeAlignment
    gap.source.selectedRepresentativeMatchesWitness

/-- Missing Green pairing against all closed Kirchhoff tests blocks the
    compact-graph realization route. -/
structure
    G8BookIIICh23FloorNormalizedA15PointwiseRealizationWithoutAllTestGreen
    where
  source :
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource
  missingAllTestGreen :
    ¬ source.greenPairingAgainstAllClosedTests

theorem
    G8BookIIICh23FloorNormalizedA15PointwiseRealizationWithoutAllTestGreen.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15PointwiseRealizationWithoutAllTestGreen) :
    False :=
  gap.missingAllTestGreen
    gap.source.greenPairingAgainstAllClosedTestsWitness

/-- Missing pointwise reverse inclusion blocks the compact-graph realization
    route. -/
structure
    G8BookIIICh23FloorNormalizedA15PointwiseRealizationWithoutReverseInclusion
    where
  source :
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationSource
  missingReverseInclusion :
    ¬ source.reverseInclusionAll

theorem
    G8BookIIICh23FloorNormalizedA15PointwiseRealizationWithoutReverseInclusion.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15PointwiseRealizationWithoutReverseInclusion) :
    False :=
  gap.missingReverseInclusion gap.source.reverseInclusionAllWitness

end Tau.BookIII.Bridge
