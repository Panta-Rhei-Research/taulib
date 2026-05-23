import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15AdjointCalculusEngine

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Genuine Adjoint-Domain Carrier

This module introduces the preferred A1.5 reverse-inclusion carrier:

```text
actual adjoint-domain candidate
  + distributional graph-H2 recovery from the adjoint equation
  + Green pairing against every Kirchhoff test
  + boundary-form annihilator forcing
  -> selected Kirchhoff-domain representative
```

The selected Kirchhoff domain is not used as a shortcut for the adjoint
domain.  The load-bearing fields explicitly say that the carrier represents
the Hilbert adjoint graph and that the map into the selected Kirchhoff domain
is justified by the analytic regularity and boundary-forcing route.

No endpoint maximality, A2 spectrum, A3 actual-`xi`, or RH-facing theorem is
imported or proved here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- GENUINE ADJOINT-DOMAIN CARRIER
-- ============================================================

/-- A genuine adjoint-domain carrier for the floor-normalized Ch.23 graph
    operator.

The carrier is allowed to map into the already-built selected Kirchhoff
operator domain, but the proof fields record why that map is legitimate:
Hilbert-adjoint graph membership, distributional `H2` recovery, all-test Green
pairing, and finite boundary annihilator forcing. -/
structure
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource where
  adjoint : Type 1
  adjointNonempty : Nonempty adjoint
  toSelected :
    adjoint →
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain
  tests :
    G8BookIIICh23FloorNormalizedA15KirchhoffTestPresentation
  representsHilbertAdjointGraph : Prop
  representsHilbertAdjointGraphWitness :
    representsHilbertAdjointGraph
  distributionalAdjointEquation : Prop
  distributionalAdjointEquationWitness :
    distributionalAdjointEquation
  graphH2TraceRecoveryFromAdjointEquation : Prop
  graphH2TraceRecoveryWitness :
    graphH2TraceRecoveryFromAdjointEquation
  greenPairingAgainstAllKirchhoffTests : Prop
  greenPairingAgainstAllKirchhoffTestsWitness :
    greenPairingAgainstAllKirchhoffTests
  boundaryTraceAnnihilatorClassification : Prop
  boundaryTraceAnnihilatorClassificationWitness :
    boundaryTraceAnnihilatorClassification
  boundaryTraceForcesKirchhoffConditions : Prop
  boundaryTraceForcesKirchhoffConditionsWitness :
    boundaryTraceForcesKirchhoffConditions
  reverseInclusionIntoSelectedKirchhoffDomain : Prop
  reverseInclusionWitness :
    reverseInclusionIntoSelectedKirchhoffDomain
  noSelectedDomainShortcut : Prop
  noSelectedDomainShortcutWitness :
    noSelectedDomainShortcut
  noFiniteDiagnosticSubstitute : Prop
  noFiniteDiagnosticSubstituteWitness :
    noFiniteDiagnosticSubstitute
  adjointEquationInSelectedL2 :
    adjoint → Prop
  adjointEquationWitness :
    ∀ u : adjoint, adjointEquationInSelectedL2 u
  adjointDistributionalSecondDerivativeInSelectedL2 :
    adjoint → Prop
  adjointDistributionalSecondDerivativeWitness :
    ∀ u : adjoint,
      adjointDistributionalSecondDerivativeInSelectedL2 u
  graphH2RegularityFromAdjointEquation :
    adjoint → Prop
  graphH2RegularityWitness :
    ∀ u : adjoint,
      graphH2RegularityFromAdjointEquation u
  valueTraceRecoveredFromSobolevTrace :
    adjoint → Prop
  valueTraceRecoveredWitness :
    ∀ u : adjoint,
      valueTraceRecoveredFromSobolevTrace u
  derivativeTraceRecoveredFromSobolevTrace :
    adjoint → Prop
  derivativeTraceRecoveredWitness :
    ∀ u : adjoint,
      derivativeTraceRecoveredFromSobolevTrace u
  traceRecoveryFromAdjointEquation :
    adjoint → Prop
  traceRecoveryWitness :
    ∀ u : adjoint,
      traceRecoveryFromAdjointEquation u
  valueAndDerivativeBoundaryTracesExist :
    adjoint → Prop
  valueAndDerivativeBoundaryTracesExistWitness :
    ∀ u : adjoint,
      valueAndDerivativeBoundaryTracesExist u
  adjointPairingIdentityAgainstKirchhoffTests :
    adjoint → tests.point → Prop
  adjointPairingIdentityWitness :
    ∀ (u : adjoint) (v : tests.point),
      adjointPairingIdentityAgainstKirchhoffTests u v
  edgewiseGreenIdentityAgainstKirchhoffTests :
    adjoint → tests.point → Prop
  edgewiseGreenIdentityWitness :
    ∀ (u : adjoint) (v : tests.point),
      edgewiseGreenIdentityAgainstKirchhoffTests u v
  boundaryFormEqualsAdjointDefectPairing :
    adjoint → tests.point → Prop
  boundaryFormEqualsAdjointDefectPairingWitness :
    ∀ (u : adjoint) (v : tests.point),
      boundaryFormEqualsAdjointDefectPairing u v
  adjointDefectPairingVanishes :
    adjoint → tests.point → Prop
  adjointDefectPairingVanishesWitness :
    ∀ (u : adjoint) (v : tests.point),
      adjointDefectPairingVanishes u v
  annihilatesKirchhoffBoundaryForm :
    adjoint → tests.point → Prop
  annihilatesKirchhoffBoundaryFormWitness :
    ∀ (u : adjoint) (v : tests.point),
      annihilatesKirchhoffBoundaryForm u v
  status : SpineStatus := .conditional_interface

/-- The exact full-coverage predicate supplied by a genuine adjoint-domain
    carrier.  This bundles the Hilbert adjoint graph, distributional
    regularity, all-test Green pairing, boundary annihilator forcing, and
    reverse inclusion into the selected Kirchhoff domain. -/
def
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource.coverage
    (source :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource) :
    Prop :=
  source.representsHilbertAdjointGraph ∧
    source.distributionalAdjointEquation ∧
      source.graphH2TraceRecoveryFromAdjointEquation ∧
        source.greenPairingAgainstAllKirchhoffTests ∧
          source.boundaryTraceAnnihilatorClassification ∧
            source.boundaryTraceForcesKirchhoffConditions ∧
              source.reverseInclusionIntoSelectedKirchhoffDomain

/-- A genuine adjoint-domain carrier supplies its own full-coverage witness. -/
theorem
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource.coverageWitness
    (source :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource) :
    source.coverage :=
  ⟨source.representsHilbertAdjointGraphWitness,
    source.distributionalAdjointEquationWitness,
    source.graphH2TraceRecoveryWitness,
    source.greenPairingAgainstAllKirchhoffTestsWitness,
    source.boundaryTraceAnnihilatorClassificationWitness,
    source.boundaryTraceForcesKirchhoffConditionsWitness,
    source.reverseInclusionWitness⟩

/-- The selected representative of every genuine adjoint candidate has the
    closed selected trace-recovery package. -/
def
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource.usesSelectedGraphDomain
    (source :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource) :
    Prop :=
  ∀ u : source.adjoint,
    G8BookIIICh23FloorNormalizedA15SelectedTraceRecovery
      (source.toSelected u)

/-- Selected-domain trace recovery is theorem-backed once a genuine adjoint
    candidate has been mapped to its selected Kirchhoff representative. -/
theorem
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource.usesSelectedGraphDomainWitness
    (source :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource) :
    source.usesSelectedGraphDomain :=
  fun u =>
    g8BookIIICh23FloorNormalizedA15SelectedTraceRecovery_closed
      (source.toSelected u)

-- ============================================================
-- ADAPTERS INTO THE EXISTING A1.5 ENGINE
-- ============================================================

/-- Convert a genuine adjoint-domain carrier into the candidate presentation
    consumed by the concrete A1.5 adjoint-calculus engine. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource.toAdjointCandidatePresentation
    (source :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCandidatePresentation where
  point := source.adjoint
  pointNonempty := source.adjointNonempty
  realize := source.toSelected
  representsFullAdjointDomain := source.coverage
  representsFullAdjointDomainWitness := source.coverageWitness
  realizationUsesSelectedGraphDomain := source.usesSelectedGraphDomain
  realizationUsesSelectedGraphDomainWitness :=
    source.usesSelectedGraphDomainWitness
  noFiniteDiagnosticSubstitute :=
    source.noFiniteDiagnosticSubstitute ∧ source.noSelectedDomainShortcut
  noFiniteDiagnosticSubstituteWitness :=
    ⟨source.noFiniteDiagnosticSubstituteWitness,
      source.noSelectedDomainShortcutWitness⟩
  status := .conditional_interface

/-- The candidate and test presentations both land in the selected A1.3 graph
    operator domain. -/
def
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource.sameSelectedA13Domain
    (source :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource) :
    Prop :=
  source.usesSelectedGraphDomain ∧
    source.tests.realizationUsesSelectedGraphDomain

/-- A genuine adjoint-domain carrier witnesses same-domain provenance for the
    candidate and Kirchhoff-test presentations. -/
theorem
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource.sameSelectedA13DomainWitness
    (source :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource) :
    source.sameSelectedA13Domain :=
  ⟨source.usesSelectedGraphDomainWitness,
    source.tests.realizationUsesSelectedGraphDomainWitness⟩

/-- Convert a genuine adjoint-domain carrier directly into the concrete A1.5
    adjoint-calculus engine source. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource.toAdjointCalculusEngineSource
    (source :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource where
  candidates := source.toAdjointCandidatePresentation
  tests := source.tests
  presentationsUseSameSelectedA13Domain := source.sameSelectedA13Domain
  presentationsUseSameSelectedA13DomainWitness :=
    source.sameSelectedA13DomainWitness
  status := .conditional_interface

/-- A genuine adjoint-domain carrier discharges the concrete A1.5 engine
    target. -/
theorem
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource.toAdjointCalculusEngineTarget
    (source :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :=
  ⟨source.toAdjointCalculusEngineSource⟩

-- ============================================================
-- DIRECT COMPACT-GRAPH CALCULUS ADAPTER
-- ============================================================

/-- The same genuine carrier can also be read directly as the compact-graph
    adjoint calculus source, preserving the distributional/Green fields
    instead of routing through selected closed selectors. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource.toCompactGraphAdjointCalculusSource
    (source :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource where
  candidate := source.adjoint
  kirchhoffTest := source.tests.point
  candidateNonempty := source.adjointNonempty
  kirchhoffTestNonempty := source.tests.pointNonempty
  candidatesRepresentAdjointDomain := source.coverage
  candidatesRepresentAdjointDomainWitness := source.coverageWitness
  testsExhaustKirchhoffDomain :=
    source.tests.exhaustsSelectedKirchhoffDomain
  testsExhaustKirchhoffDomainWitness :=
    source.tests.exhaustsSelectedKirchhoffDomainWitness
  noFiniteDiagnosticSubstitute :=
    source.noFiniteDiagnosticSubstitute ∧
      source.noSelectedDomainShortcut ∧
        source.tests.noFiniteDiagnosticSubstitute
  noFiniteDiagnosticSubstituteWitness :=
    ⟨source.noFiniteDiagnosticSubstituteWitness,
      source.noSelectedDomainShortcutWitness,
      source.tests.noFiniteDiagnosticSubstituteWitness⟩
  adjointEquationInSelectedL2 := source.adjointEquationInSelectedL2
  adjointEquationWitness := source.adjointEquationWitness
  adjointDistributionalSecondDerivativeInSelectedL2 :=
    source.adjointDistributionalSecondDerivativeInSelectedL2
  adjointDistributionalSecondDerivativeWitness :=
    source.adjointDistributionalSecondDerivativeWitness
  graphH2RegularityFromAdjointEquation :=
    source.graphH2RegularityFromAdjointEquation
  graphH2RegularityWitness := source.graphH2RegularityWitness
  valueTraceRecoveredFromSobolevTrace :=
    source.valueTraceRecoveredFromSobolevTrace
  valueTraceRecoveredWitness := source.valueTraceRecoveredWitness
  derivativeTraceRecoveredFromSobolevTrace :=
    source.derivativeTraceRecoveredFromSobolevTrace
  derivativeTraceRecoveredWitness :=
    source.derivativeTraceRecoveredWitness
  traceRecoveryFromAdjointEquation :=
    source.traceRecoveryFromAdjointEquation
  traceRecoveryWitness := source.traceRecoveryWitness
  valueAndDerivativeBoundaryTracesExist :=
    source.valueAndDerivativeBoundaryTracesExist
  valueAndDerivativeBoundaryTracesExistWitness :=
    source.valueAndDerivativeBoundaryTracesExistWitness
  adjointPairingIdentityAgainstKirchhoffTests :=
    source.adjointPairingIdentityAgainstKirchhoffTests
  adjointPairingIdentityWitness :=
    source.adjointPairingIdentityWitness
  edgewiseGreenIdentityAgainstKirchhoffTests :=
    source.edgewiseGreenIdentityAgainstKirchhoffTests
  edgewiseGreenIdentityWitness :=
    source.edgewiseGreenIdentityWitness
  boundaryFormEqualsAdjointDefectPairing :=
    source.boundaryFormEqualsAdjointDefectPairing
  boundaryFormEqualsAdjointDefectPairingWitness :=
    source.boundaryFormEqualsAdjointDefectPairingWitness
  adjointDefectPairingVanishes :=
    source.adjointDefectPairingVanishes
  adjointDefectPairingVanishesWitness :=
    source.adjointDefectPairingVanishesWitness
  annihilatesKirchhoffBoundaryForm :=
    source.annihilatesKirchhoffBoundaryForm
  annihilatesKirchhoffBoundaryFormWitness :=
    source.annihilatesKirchhoffBoundaryFormWitness
  status := .conditional_interface

/-- A genuine adjoint-domain carrier discharges the compact-graph adjoint
    calculus target. -/
theorem
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource.toCompactGraphAdjointCalculusTarget
    (source :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusTarget :=
  ⟨source.toCompactGraphAdjointCalculusSource⟩

/-- Target form for the genuine adjoint-domain carrier route. -/
def G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource

/-- Target-level adapter from the genuine adjoint-domain carrier to the
    concrete A1.5 engine target. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofGenuineAdjointDomainCarrier
    (target :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :=
  target.elim fun source => source.toAdjointCalculusEngineTarget

/-- Target-level adapter from the genuine adjoint-domain carrier to the
    compact-graph adjoint calculus target. -/
theorem
    g8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusTarget_ofGenuineAdjointDomainCarrier
    (target :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierTarget) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusTarget :=
  target.elim fun source => source.toCompactGraphAdjointCalculusTarget

/-- The genuine carrier supplies the two analytic laws through the
    compact-graph calculus surface. -/
theorem
    g8BookIIICh23FloorNormalizedA15TwoAnalyticLawTargets_ofGenuineAdjointDomainCarrier
    (target :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierTarget) :
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquationTarget ∧
      G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTestsTarget :=
  g8BookIIICh23FloorNormalizedA15TwoAnalyticLawTargets_ofCompactGraphCalculus
    (g8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusTarget_ofGenuineAdjointDomainCarrier
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A genuine carrier without Hilbert-adjoint graph coverage is refuted by its
    own source fields. -/
structure
    G8BookIIICh23FloorNormalizedA15GenuineCarrierWithoutAdjointGraphCoverage
    where
  source :
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource
  missingAdjointGraphCoverage :
    ¬ source.representsHilbertAdjointGraph

theorem
    G8BookIIICh23FloorNormalizedA15GenuineCarrierWithoutAdjointGraphCoverage.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15GenuineCarrierWithoutAdjointGraphCoverage) :
    False :=
  gap.missingAdjointGraphCoverage
    gap.source.representsHilbertAdjointGraphWitness

/-- Selected-domain identity data alone cannot fill the genuine carrier if
    the no-shortcut provenance is missing. -/
structure
    G8BookIIICh23FloorNormalizedA15SelectedDomainShortcutCarrierGap where
  source :
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource
  selectedShortcutOnly :
    ¬ source.noSelectedDomainShortcut

theorem
    G8BookIIICh23FloorNormalizedA15SelectedDomainShortcutCarrierGap.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15SelectedDomainShortcutCarrierGap) :
    False :=
  gap.selectedShortcutOnly gap.source.noSelectedDomainShortcutWitness

/-- Finite trace data alone cannot substitute for the genuine
    distributional/pairing adjoint-domain carrier. -/
structure
    G8BookIIICh23FloorNormalizedA15FiniteTraceOnlyGenuineCarrierGap where
  source :
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource
  finiteTraceOnly :
    ¬ source.noFiniteDiagnosticSubstitute

theorem
    G8BookIIICh23FloorNormalizedA15FiniteTraceOnlyGenuineCarrierGap.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15FiniteTraceOnlyGenuineCarrierGap) :
    False :=
  gap.finiteTraceOnly gap.source.noFiniteDiagnosticSubstituteWitness

/-- A carrier missing all-test Green pairing is not the option-1
    distributional/pairing source. -/
structure
    G8BookIIICh23FloorNormalizedA15GenuineCarrierWithoutAllTestGreenPairing
    where
  source :
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource
  missingAllTestGreenPairing :
    ¬ source.greenPairingAgainstAllKirchhoffTests

theorem
    G8BookIIICh23FloorNormalizedA15GenuineCarrierWithoutAllTestGreenPairing.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15GenuineCarrierWithoutAllTestGreenPairing) :
    False :=
  gap.missingAllTestGreenPairing
    gap.source.greenPairingAgainstAllKirchhoffTestsWitness

end Tau.BookIII.Bridge
