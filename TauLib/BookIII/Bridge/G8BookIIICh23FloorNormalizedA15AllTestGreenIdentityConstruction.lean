import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15GraphH2RecoveryConstruction

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 All-Test Green Identity Construction

This module closes the next lower-route A1.5 stone after graph-H2 recovery:

```text
graph-H2 trace recovery
  -> selected A1.4 edgewise Green bookkeeping
  -> adjoint pairing identity against every closed Kirchhoff test
  -> boundary-form defect representation and vanishing
  -> all-test Green identity source
```

It remains upstream of the finite boundary-annihilator forcing step and the
reverse-inclusion/maximality assembly.  No spectral, A3 actual-`xi`, final RH,
O3, determinant, divisor, accepted-coverage, or completion source is imported
or used.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- POINTWISE ALL-TEST GREEN IDENTITY
-- ============================================================

/-- Pointwise all-test Green identity for an actual adjoint candidate against
    a closed Kirchhoff test. -/
def
    G8BookIIICh23FloorNormalizedA15ActualAllTestGreenIdentityAt
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate)
    (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity
    u.selectedRepresentative
    (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
      |>.realize test)

/-- The selected A1.4 Green identity closes the pointwise all-test identity. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualAllTestGreenIdentityAt_closed
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate)
    (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest) :
    G8BookIIICh23FloorNormalizedA15ActualAllTestGreenIdentityAt
      u test :=
  g8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity_closed
    u.selectedRepresentative
    (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
      |>.realize test)

/-- The edgewise integration-by-parts identity used inside the all-test Green
    identity. -/
def
    G8BookIIICh23FloorNormalizedA15ActualEdgewiseGreenIdentityAt
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate)
    (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenIdentity
    u.selectedRepresentative
    (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
      |>.realize test)

/-- The closed selected edgewise Green identity applies to every actual
    candidate and closed Kirchhoff test. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualEdgewiseGreenIdentityAt_closed
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate)
    (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest) :
    G8BookIIICh23FloorNormalizedA15ActualEdgewiseGreenIdentityAt
      u test :=
  g8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenIdentity_closed
    u.selectedRepresentative
    (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
      |>.realize test)

/-- Boundary-form defect representation for the selected lower route. -/
def
    G8BookIIICh23FloorNormalizedA15ActualBoundaryFormEqualsAdjointDefect :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedBoundaryFormEqualsAdjointDefect

/-- The selected A1.4 endpoint-cancellation input supplies boundary-form
    defect representation. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualBoundaryFormEqualsAdjointDefect_closed :
    G8BookIIICh23FloorNormalizedA15ActualBoundaryFormEqualsAdjointDefect :=
  g8BookIIICh23FloorNormalizedA15SelectedBoundaryFormEqualsAdjointDefect_closed

/-- Vanishing of the adjoint-defect pairing on the selected lower route. -/
def
    G8BookIIICh23FloorNormalizedA15ActualAdjointDefectPairingVanishes :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedAdjointDefectPairingVanishes

/-- The selected A1.4 symmetry law supplies adjoint-defect vanishing. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualAdjointDefectPairingVanishes_closed :
    G8BookIIICh23FloorNormalizedA15ActualAdjointDefectPairingVanishes :=
  g8BookIIICh23FloorNormalizedA15SelectedAdjointDefectPairingVanishes_closed

/-- Boundary-form annihilation on the selected lower route. -/
def
    G8BookIIICh23FloorNormalizedA15ActualAnnihilatesKirchhoffBoundaryForm :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedAnnihilatesBoundaryForm

/-- The selected A1.4 boundary-form cancellation theorem supplies
    annihilation of the Kirchhoff boundary form. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualAnnihilatesKirchhoffBoundaryForm_closed :
    G8BookIIICh23FloorNormalizedA15ActualAnnihilatesKirchhoffBoundaryForm :=
  g8BookIIICh23FloorNormalizedA15SelectedAnnihilatesBoundaryForm_closed

-- ============================================================
-- MATCHING THE ADJOINT PAIRING LAW
-- ============================================================

/-- The Green identity remains aligned with the actual candidate's all-test
    adjoint-pairing law. -/
def
    G8BookIIICh23FloorNormalizedA15ActualGreenIdentityMatchesAdjointPairingLawAt
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate) :
    Prop :=
  ∀ test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest,
    G8BookIIICh23FloorNormalizedA15ActualAdjointCandidateL2PairingEvidence.allTestAdjointPairingLaw
      (G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate.evidence u)
      test ∧
      G8BookIIICh23FloorNormalizedA15ActualAllTestGreenIdentityAt u test

/-- The actual candidate evidence and selected A1.4 Green identity jointly
    prove alignment with the adjoint-pairing law. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualGreenIdentityMatchesAdjointPairingLawAt_closed
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate) :
    G8BookIIICh23FloorNormalizedA15ActualGreenIdentityMatchesAdjointPairingLawAt
      u :=
  fun test =>
    ⟨G8BookIIICh23FloorNormalizedA15ActualAdjointCandidateL2PairingEvidence.allTestAdjointPairingWitness
        (G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate.evidence u)
        test,
      g8BookIIICh23FloorNormalizedA15ActualAllTestGreenIdentityAt_closed
        u test⟩

/-- The all-test identity is obtained by edgewise integration by parts plus
    the selected boundary-form defect and vanishing laws. -/
def
    G8BookIIICh23FloorNormalizedA15ActualObtainedByEdgewiseIntegrationByParts :
    Prop :=
  ∀ (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate)
    (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest),
      G8BookIIICh23FloorNormalizedA15ActualEdgewiseGreenIdentityAt u test ∧
        G8BookIIICh23FloorNormalizedA15ActualBoundaryFormEqualsAdjointDefect ∧
          G8BookIIICh23FloorNormalizedA15ActualAdjointDefectPairingVanishes ∧
            G8BookIIICh23FloorNormalizedA15ActualAnnihilatesKirchhoffBoundaryForm

/-- Edgewise integration by parts and the selected A1.4 boundary laws are
    theorem-backed for every actual candidate and closed test. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualObtainedByEdgewiseIntegrationByParts_closed :
    G8BookIIICh23FloorNormalizedA15ActualObtainedByEdgewiseIntegrationByParts :=
  fun u test =>
    ⟨g8BookIIICh23FloorNormalizedA15ActualEdgewiseGreenIdentityAt_closed
        u test,
      g8BookIIICh23FloorNormalizedA15ActualBoundaryFormEqualsAdjointDefect_closed,
      g8BookIIICh23FloorNormalizedA15ActualAdjointDefectPairingVanishes_closed,
      g8BookIIICh23FloorNormalizedA15ActualAnnihilatesKirchhoffBoundaryForm_closed⟩

-- ============================================================
-- LOWER GRAPH-PREDICATE ROUTE SOURCE
-- ============================================================

/-- The all-test Green identity source consumed by the lower graph-predicate
    route. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source_closed :
    G8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source
    where
  graphH2 :=
    g8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphSource_closed
  allTestGreenIdentityAt :=
    G8BookIIICh23FloorNormalizedA15ActualAllTestGreenIdentityAt
  allTestGreenIdentityAtWitness :=
    g8BookIIICh23FloorNormalizedA15ActualAllTestGreenIdentityAt_closed
  greenIdentityMatchesAdjointPairingLawAt :=
    G8BookIIICh23FloorNormalizedA15ActualGreenIdentityMatchesAdjointPairingLawAt
  greenIdentityMatchesAdjointPairingLawWitness :=
    g8BookIIICh23FloorNormalizedA15ActualGreenIdentityMatchesAdjointPairingLawAt_closed
  obtainedByEdgewiseIntegrationByParts :=
    G8BookIIICh23FloorNormalizedA15ActualObtainedByEdgewiseIntegrationByParts
  obtainedByEdgewiseIntegrationByPartsWitness :=
    g8BookIIICh23FloorNormalizedA15ActualObtainedByEdgewiseIntegrationByParts_closed
  status := .conditional_interface

/-- Target-level closure of the all-test Green identity in the lower route. -/
theorem
    g8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Target_closed :
    G8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Target :=
  ⟨g8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source_closed⟩

-- ============================================================
-- ANALYTIC GREEN-LAW SOURCE
-- ============================================================

/-- The closed Kirchhoff-test presentation really ranges over the selected
    Kirchhoff domain. -/
def
    G8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain :
    Prop :=
  g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
    |>.exhaustsSelectedKirchhoffDomain

/-- Exhaustivity of the closed Kirchhoff-test presentation. -/
theorem
    g8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain_closed :
    G8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain :=
  g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation_exhaustive

/-- The closed selected lower route proves the analytic Green identity law
    consumed by the trace/annihilator classification layer. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests_closed :
    G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests
    where
  selectedGreenBookkeeping :=
    g8BookIIICh23FloorNormalizedA15SelectedGreenBookkeepingForAdjoint_closed
  traceSource :=
    g8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation_closed
      |>.toTraceExistenceSource
  testsAllKirchhoffDomainElements :=
    G8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain
  testsAllKirchhoffDomainElementsWitness :=
    g8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain_closed
  adjointPairingIdentityAgainstKirchhoffTests :=
    ∀ (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate)
      (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest),
        G8BookIIICh23FloorNormalizedA15ActualAllTestGreenIdentityAt u test
  adjointPairingIdentityWitness :=
    g8BookIIICh23FloorNormalizedA15ActualAllTestGreenIdentityAt_closed
  edgewiseGreenIdentityAgainstKirchhoffTests :=
    ∀ (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate)
      (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest),
        G8BookIIICh23FloorNormalizedA15ActualEdgewiseGreenIdentityAt u test
  edgewiseGreenIdentityWitness :=
    g8BookIIICh23FloorNormalizedA15ActualEdgewiseGreenIdentityAt_closed
  boundaryFormEqualsAdjointDefectPairing :=
    G8BookIIICh23FloorNormalizedA15ActualBoundaryFormEqualsAdjointDefect
  boundaryFormEqualsAdjointDefectPairingWitness :=
    g8BookIIICh23FloorNormalizedA15ActualBoundaryFormEqualsAdjointDefect_closed
  adjointDefectPairingVanishes :=
    G8BookIIICh23FloorNormalizedA15ActualAdjointDefectPairingVanishes
  adjointDefectPairingVanishesWitness :=
    g8BookIIICh23FloorNormalizedA15ActualAdjointDefectPairingVanishes_closed
  annihilatesKirchhoffBoundaryForm :=
    G8BookIIICh23FloorNormalizedA15ActualAnnihilatesKirchhoffBoundaryForm
  annihilatesKirchhoffBoundaryFormWitness :=
    g8BookIIICh23FloorNormalizedA15ActualAnnihilatesKirchhoffBoundaryForm_closed
  status := .conditional_interface

/-- Target-level closure of the analytic all-test Green identity law. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTestsTarget_closed :
    G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTestsTarget :=
  ⟨g8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests_closed⟩

/-- Combined graph-H2 recovery plus Green identity source for the first two
    reverse-inclusion stones. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource_closed :
    G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource
    where
  traceRecovery :=
    g8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation_closed
  greenIdentity :=
    g8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTests_closed
  greenUsesRecoveredTrace :=
    rfl
  status := .conditional_interface

/-- Target-level closure of the combined graph-H2/Green source. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentityTarget_closed :
    G8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentityTarget :=
  ⟨g8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource_closed⟩

/-- The all-test Green identity plus graph-H2 recovery closes the
    trace/annihilator classification source target. -/
theorem
    g8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSourceTarget_ofAllTestGreen :
    Nonempty
      G8BookIIICh23FloorNormalizedA15TraceAnnihilatorClassificationSource :=
  g8BookIIICh23FloorNormalizedA15AdjointEquationGreenIdentitySource_closed
    |>.toFirstTwoStonesTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Graph-H2 recovery without all closed Kirchhoff tests does not provide the
    all-test Green identity source. -/
structure
    G8BookIIICh23FloorNormalizedA15GraphH2WithoutClosedKirchhoffTests
    where
  graphH2 :
    G8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphSource
  missingClosedTestExhaustion :
    ¬ G8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain

theorem
    G8BookIIICh23FloorNormalizedA15GraphH2WithoutClosedKirchhoffTests.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15GraphH2WithoutClosedKirchhoffTests) :
    False :=
  gap.missingClosedTestExhaustion
    g8BookIIICh23FloorNormalizedA15ClosedTestsExhaustKirchhoffDomain_closed

/-- Edgewise Green identity without boundary-form defect bookkeeping is not
    enough for the adjoint Green law. -/
structure
    G8BookIIICh23FloorNormalizedA15EdgewiseGreenWithoutBoundaryDefect
    where
  edgewise :
    ∀ (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate)
      (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest),
        G8BookIIICh23FloorNormalizedA15ActualEdgewiseGreenIdentityAt u test
  missingBoundaryDefect :
    ¬ G8BookIIICh23FloorNormalizedA15ActualBoundaryFormEqualsAdjointDefect

theorem
    G8BookIIICh23FloorNormalizedA15EdgewiseGreenWithoutBoundaryDefect.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15EdgewiseGreenWithoutBoundaryDefect) :
    False :=
  gap.missingBoundaryDefect
    g8BookIIICh23FloorNormalizedA15ActualBoundaryFormEqualsAdjointDefect_closed

/-- The all-test Green identity alone still does not force the final
    Kirchhoff boundary condition; the finite boundary-annihilator hookup is
    the next separate stone. -/
structure
    G8BookIIICh23FloorNormalizedA15AllTestGreenWithoutBoundaryHookup
    where
  green :
    G8BookIIICh23FloorNormalizedA15AllTestGreenIdentityFromGraphH2Source
  missingBoundaryHookup :
    ¬ G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupTarget

theorem
    G8BookIIICh23FloorNormalizedA15AllTestGreenWithoutBoundaryHookup.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15AllTestGreenWithoutBoundaryHookup)
    (hookup :
      G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorHookupSource) :
    False :=
  gap.missingBoundaryHookup ⟨hookup⟩

end Tau.BookIII.Bridge
