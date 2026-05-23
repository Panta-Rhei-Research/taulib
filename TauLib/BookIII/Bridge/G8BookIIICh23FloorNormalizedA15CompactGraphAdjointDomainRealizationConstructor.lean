import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRoute

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Compact-Graph Adjoint-Domain Realization Constructor

This module builds the explicit source-level constructor behind
`G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource`.

The input is the seven-stone Hilbert-adjoint graph predicate route:

```text
actual Hilbert-adjoint graph predicate
  -> selected representative extraction
  -> distributional equation from adjoint pairing
  -> graph-H2 recovery
  -> all-test Green identity
  -> finite boundary-annihilator hookup
  -> reverse inclusion into the selected Kirchhoff domain
```

From that route we construct the compact-graph adjoint-domain realization
source directly.  No selected-domain shortcut, finite diagnostic substitute,
spectral statement, A3 actual-`xi` membership, accepted coverage, O3,
determinant transfer, divisor transfer, completion uniqueness, or RH-facing
handoff is imported or used.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- SOURCE-LEVEL ANALYTIC CONSTRUCTOR
-- ============================================================

/-- The actual Hilbert-adjoint graph predicate route constructs the
    compact-graph adjoint-domain realization source.

This is the source-level constructor for the A1.5 domain-realization target.
The fields are read directly from the graph-predicate route:

* graph predicate and selected representative extraction give the adjoint
  carrier and selected representative map;
* the distributional, graph-H2, Green, boundary-annihilator, and
  reverse-inclusion stones become the load-bearing analytic fields;
* the no-shortcut and no-finite-diagnostic guardrails are preserved. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.toCompactGraphAdjointDomainRealizationSource
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource
    where
  adjoint := source.graphPredicate.candidate
  adjointNonempty := source.graphPredicate.candidateNonempty
  toSelected := source.extraction.selectedRepresentative
  representsHilbertAdjointGraph :=
    source.graphPredicate.graphPredicateIsActualHilbertAdjointDomain ∧
      source.graphDefinitionIsGlobal ∧
        (∀ u : source.graphPredicate.candidate,
          source.graphPredicate.hilbertAdjointGraphPredicate u)
  representsHilbertAdjointGraphWitness :=
    ⟨source.graphPredicate.graphPredicateIsActualHilbertAdjointDomainWitness,
      source.graphDefinitionIsGlobalWitness,
      source.graphPredicate.predicateMembershipWitness⟩
  distributionalAdjointEquation :=
    ∀ u : source.graphPredicate.candidate,
      source.annihilator.green.graphH2.distributional.distributionalAdjointEquationAt u
  distributionalAdjointEquationWitness :=
    source.annihilator.green.graphH2.distributional.distributionalAdjointEquationAtWitness
  graphH2TraceRecoveryFromAdjointEquation :=
    ∀ u : source.graphPredicate.candidate,
      source.annihilator.green.graphH2.graphH2TraceRecoveryAt u
  graphH2TraceRecoveryWitness :=
    source.annihilator.green.graphH2.graphH2TraceRecoveryAtWitness
  greenPairingAgainstAllKirchhoffTests :=
    ∀ (u : source.graphPredicate.candidate)
      (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest),
        source.annihilator.green.allTestGreenIdentityAt u test
  greenPairingAgainstAllKirchhoffTestsWitness :=
    source.annihilator.green.allTestGreenIdentityAtWitness
  boundaryTraceAnnihilatorClassification :=
    ∀ u : source.graphPredicate.candidate,
      source.annihilator.boundaryTraceAnnihilatorAt u
  boundaryTraceAnnihilatorClassificationWitness :=
    source.annihilator.boundaryTraceAnnihilatorAtWitness
  boundaryTraceForcesKirchhoffConditions :=
    ∀ u : source.graphPredicate.candidate,
      source.annihilator.boundaryTraceForcesKirchhoffAt u
  boundaryTraceForcesKirchhoffConditionsWitness :=
    source.annihilator.boundaryTraceForcesKirchhoffAtWitness
  reverseInclusionIntoSelectedKirchhoffDomain :=
    ∀ u : source.graphPredicate.candidate,
      source.reverseInclusionIntoSelectedKirchhoffDomainAt u
  reverseInclusionWitness :=
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

/-- Source-level constructor packaged as the compact-graph realization target. -/
theorem
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource.toCompactGraphAdjointDomainRealizationTarget
    (source :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget :=
  ⟨source.toCompactGraphAdjointDomainRealizationSource⟩

/-- Target-level constructor from the actual Hilbert-adjoint graph predicate
    route to compact-graph adjoint-domain realization. -/
theorem
    g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_ofPredicateRouteConstructor
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget :=
  target.elim fun source =>
    source.toCompactGraphAdjointDomainRealizationTarget

/-- The explicit constructor also supplies the pointwise realization target
    through the already-proved compact/pointwise equivalence. -/
theorem
    g8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget_ofPredicateRouteConstructor
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget) :
    G8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget :=
  g8BookIIICh23FloorNormalizedA15PointwiseAdjointDomainRealizationTarget_ofCompactGraphAdjointDomainRealization
    (g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_ofPredicateRouteConstructor
      target)

/-- The explicit constructor feeds the selected-carrier maximal Kirchhoff
    self-adjointness target. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofPredicateRouteConstructor
    (target :
      G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofCompactGraphAdjointDomainRealization
    (g8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget_ofPredicateRouteConstructor
      target)

-- ============================================================
-- CONSTRUCTOR GUARDRAILS
-- ============================================================

/-- Without actual Hilbert-adjoint graph provenance, the constructor cannot
    supply the compact realization's graph-representation field. -/
structure
    G8BookIIICh23FloorNormalizedA15PredicateRouteWithoutActualGraphProvenance
    where
  source :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource
  missingActualGraphProvenance :
    ¬ source.graphPredicate.graphPredicateIsActualHilbertAdjointDomain

theorem
    G8BookIIICh23FloorNormalizedA15PredicateRouteWithoutActualGraphProvenance.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15PredicateRouteWithoutActualGraphProvenance) :
    False :=
  gap.missingActualGraphProvenance
    gap.source.graphPredicate.graphPredicateIsActualHilbertAdjointDomainWitness

/-- Without reverse inclusion, the explicit constructor cannot produce the
    compact-graph adjoint-domain realization source. -/
structure
    G8BookIIICh23FloorNormalizedA15PredicateRouteWithoutReverseInclusion
    where
  source :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource
  missingReverseInclusion :
    ¬ (∀ u : source.graphPredicate.candidate,
      source.reverseInclusionIntoSelectedKirchhoffDomainAt u)

theorem
    G8BookIIICh23FloorNormalizedA15PredicateRouteWithoutReverseInclusion.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15PredicateRouteWithoutReverseInclusion) :
    False :=
  gap.missingReverseInclusion
    gap.source.reverseInclusionIntoSelectedKirchhoffDomainAtWitness

/-- A predicate route with finite or approximate boundary data cannot be read
    as the compact graph realization constructor. -/
structure
    G8BookIIICh23FloorNormalizedA15PredicateRouteWithFiniteDiagnosticSubstitute
    where
  source :
    G8BookIIICh23FloorNormalizedA15HilbertAdjointGraphPredicateRouteSource
  diagnosticOnly :
    ¬ (source.noFiniteDiagnosticSubstitute ∧
        source.graphPredicate.noFiniteTestSubsetDefinition ∧
          source.annihilator.noApproximateBoundaryData)

theorem
    G8BookIIICh23FloorNormalizedA15PredicateRouteWithFiniteDiagnosticSubstitute.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15PredicateRouteWithFiniteDiagnosticSubstitute) :
    False :=
  gap.diagnosticOnly
    ⟨gap.source.noFiniteDiagnosticSubstituteWitness,
      gap.source.graphPredicate.noFiniteTestSubsetDefinitionWitness,
      gap.source.annihilator.noApproximateBoundaryDataWitness⟩

end Tau.BookIII.Bridge
