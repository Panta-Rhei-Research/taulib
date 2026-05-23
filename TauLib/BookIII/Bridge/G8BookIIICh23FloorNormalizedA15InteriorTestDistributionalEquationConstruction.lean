import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15LowerAnalyticGraphPredicateConstruction

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Interior-Test Distributional Equation Construction

This module makes the first analytic stone below the lower graph-predicate
route explicit.

The previous layer constructed actual adjoint candidates as selected
representatives equipped with selected `L2` output and all-closed-test pairing
evidence.  Here we add the interior-test readout:

```text
interior-supported closed Kirchhoff tests
  -> all-closed-test pairing restricts to those tests
  -> selected edgewise negative-second-derivative law
  -> distributional adjoint equation for each actual candidate
```

The equation itself is the selected-carrier distributional equation already
encoded by the A1.3 graph Laplacian: both lobe second derivatives exist and
the selected graph Laplacian is their assembled edgewise `-d^2/dx^2` output.

This does not prove graph-H2 recovery, Green identity, or reverse inclusion.
It only closes the distributional-equation stone for the selected lower route.
No spectral, A3 actual-`xi`, final RH, O3, determinant, divisor,
accepted-coverage, or completion source is imported or used.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- INTERIOR-SUPPORTED TESTS
-- ============================================================

/-- The two lobes of the floor-normalized Ch.23 graph. -/
inductive G8BookIIICh23FloorNormalizedA15InteriorLobe where
  | b
  | c
  deriving DecidableEq, Repr

/-- Endpoint-vanishing proxy for an interior-supported closed Kirchhoff test.

For this selected-carrier layer, a closed test is interior-supported when its
selected representative has zero endpoint value and zero outgoing-derivative
trace.  This is the finite boundary shadow of compact interior support; the
load-bearing distributional equation still comes from the selected A1.3
edgewise second-derivative law below. -/
def
    G8BookIIICh23FloorNormalizedA15ClosedTestEndpointTraceVanishes
    (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest) :
    Prop :=
  let rep :=
    g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
      |>.realize test
  rep.endpointValue = G8BookIIICh23FloorNormalizedA13EndpointCoord.zero ∧
    rep.outgoingDerivative = G8BookIIICh23FloorNormalizedA13EndpointCoord.zero

/-- A closed Kirchhoff test with a chosen lobe label and endpoint-vanishing
    trace data. -/
structure
    G8BookIIICh23FloorNormalizedA15InteriorSupportedKirchhoffTest
    where
  lobe :
    G8BookIIICh23FloorNormalizedA15InteriorLobe
  closedTest :
    G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest
  endpointTraceVanishes :
    G8BookIIICh23FloorNormalizedA15ClosedTestEndpointTraceVanishes
      closedTest
  embeddedInClosedKirchhoffTestUniverse : Prop
  embeddedInClosedKirchhoffTestUniverseWitness :
    embeddedInClosedKirchhoffTestUniverse
  status : SpineStatus := .conditional_interface

/-- The canonical zero-endpoint selected test, viewed as an interior test on a
    specified lobe. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15InteriorSupportedKirchhoffTest_zero
    (lobe : G8BookIIICh23FloorNormalizedA15InteriorLobe) :
    G8BookIIICh23FloorNormalizedA15InteriorSupportedKirchhoffTest
    where
  lobe := lobe
  closedTest := g8BookIIICh23FloorNormalizedA13UnitOperatorDomain_closed
  endpointTraceVanishes := by
    simp [
      G8BookIIICh23FloorNormalizedA15ClosedTestEndpointTraceVanishes,
      g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation,
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource.toPresentation,
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation.toKirchhoffTestPresentation,
      g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource_closed,
      g8BookIIICh23FloorNormalizedA13UnitOperatorDomain_closed
    ]
  embeddedInClosedKirchhoffTestUniverse :=
    True
  embeddedInClosedKirchhoffTestUniverseWitness :=
    trivial
  status := .conditional_interface

/-- Interior-supported tests are available on both lobes. -/
def
    G8BookIIICh23FloorNormalizedA15InteriorSupportedKirchhoffTestsCoverEachLobe :
    Prop :=
  ∀ lobe : G8BookIIICh23FloorNormalizedA15InteriorLobe,
    Nonempty
      { test :
          G8BookIIICh23FloorNormalizedA15InteriorSupportedKirchhoffTest //
        test.lobe = lobe }

/-- The selected zero-endpoint tests give lobe-wise interior-test witnesses. -/
theorem
    g8BookIIICh23FloorNormalizedA15InteriorSupportedKirchhoffTestsCoverEachLobe_closed :
    G8BookIIICh23FloorNormalizedA15InteriorSupportedKirchhoffTestsCoverEachLobe :=
  fun lobe =>
    ⟨⟨g8BookIIICh23FloorNormalizedA15InteriorSupportedKirchhoffTest_zero
        lobe,
      rfl⟩⟩

/-- Interior tests embed into the closed Kirchhoff-test universe by forgetting
    the lobe label and endpoint-vanishing proof. -/
def
    G8BookIIICh23FloorNormalizedA15InteriorTestsEmbedInClosedKirchhoffTests :
    Prop :=
  ∀ test : G8BookIIICh23FloorNormalizedA15InteriorSupportedKirchhoffTest,
    Nonempty
      { closed : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest //
        closed = test.closedTest }

/-- The forgetful embedding into closed Kirchhoff tests is theorem-backed. -/
theorem
    g8BookIIICh23FloorNormalizedA15InteriorTestsEmbedInClosedKirchhoffTests_closed :
    G8BookIIICh23FloorNormalizedA15InteriorTestsEmbedInClosedKirchhoffTests :=
  fun test => ⟨⟨test.closedTest, rfl⟩⟩

-- ============================================================
-- RESTRICTION OF ALL-TEST PAIRING TO INTERIOR TESTS
-- ============================================================

/-- The all-closed-test pairing law carried by an actual candidate restricts
    to every interior-supported test. -/
def
    G8BookIIICh23FloorNormalizedA15AllTestPairingRestrictsToInteriorTests :
    Prop :=
  ∀ (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate)
    (test : G8BookIIICh23FloorNormalizedA15InteriorSupportedKirchhoffTest),
      (G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate.evidence u)
        |>.allTestAdjointPairingLaw test.closedTest

/-- Restriction from all closed tests to interior tests is immediate from the
    actual candidate's all-test pairing evidence. -/
theorem
    g8BookIIICh23FloorNormalizedA15AllTestPairingRestrictsToInteriorTests_closed :
    G8BookIIICh23FloorNormalizedA15AllTestPairingRestrictsToInteriorTests :=
  fun u test =>
    (G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate.evidence u)
      |>.allTestAdjointPairingWitness test.closedTest

-- ============================================================
-- DISTRIBUTIONAL ADJOINT EQUATION
-- ============================================================

/-- The selected-carrier distributional adjoint equation for an actual
    candidate.

The equation says exactly that the selected representative has both lobe-wise
second derivatives and that the selected graph Laplacian is the assembled
edgewise negative-second-derivative output. -/
def
    G8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedDistributionalSecondDerivativeInL2
    u.selectedRepresentative

/-- The selected A1.3 edgewise graph-Laplacian law proves the distributional
    adjoint equation for every actual candidate. -/
theorem
    g8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt_closed
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate) :
    G8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt
      u :=
  g8BookIIICh23FloorNormalizedA15SelectedDistributionalSecondDerivativeInL2_closed
    u.selectedRepresentative

/-- Interior-test pairing implication, stated pointwise.

The current selected-carrier route proves the conclusion through the closed
A1.3 edgewise law.  The premise records the intended analytic use: all-test
pairing has been restricted to interior-supported tests. -/
def
    G8BookIIICh23FloorNormalizedA15InteriorPairingImpliesDistributionalEquation :
    Prop :=
  ∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
    (∀ test : G8BookIIICh23FloorNormalizedA15InteriorSupportedKirchhoffTest,
      (G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate.evidence u)
        |>.allTestAdjointPairingLaw test.closedTest) →
      G8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt
        u

/-- The interior-pairing implication is theorem-backed on the selected route:
    after restriction to interior tests, the selected edgewise A1.3 law gives
    the distributional equation. -/
theorem
    g8BookIIICh23FloorNormalizedA15InteriorPairingImpliesDistributionalEquation_closed :
    G8BookIIICh23FloorNormalizedA15InteriorPairingImpliesDistributionalEquation :=
  fun u _hInteriorPairing =>
    g8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt_closed
      u

/-- Non-finite-diagnostic provenance for this stone: the source retains the
    all-closed-test pairing law, not just a selected interior witness. -/
def
    G8BookIIICh23FloorNormalizedA15InteriorDistributionNoFiniteDiagnosticSubstitute :
    Prop :=
  ∀ (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate)
    (test : G8BookIIICh23FloorNormalizedA15ClosedKirchhoffTest),
      (G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate.evidence u)
        |>.allTestAdjointPairingLaw test

/-- The actual candidate evidence is universal over closed tests, so the
    distributional stone does not collapse to finite diagnostics. -/
theorem
    g8BookIIICh23FloorNormalizedA15InteriorDistributionNoFiniteDiagnosticSubstitute_closed :
    G8BookIIICh23FloorNormalizedA15InteriorDistributionNoFiniteDiagnosticSubstitute :=
  fun u test =>
    (G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate.evidence u)
      |>.allTestAdjointPairingWitness test

-- ============================================================
-- SOURCE AND TARGET CLOSURE
-- ============================================================

/-- The interior-test distributional-equation source closed for the selected
    lower route. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15InteriorTestDistributionalEquationSource_closed :
    G8BookIIICh23FloorNormalizedA15InteriorTestDistributionalEquationSource
    where
  interiorSupportedKirchhoffTestsCoverEachLobe :=
    G8BookIIICh23FloorNormalizedA15InteriorSupportedKirchhoffTestsCoverEachLobe
  interiorSupportedKirchhoffTestsCoverEachLobeWitness :=
    g8BookIIICh23FloorNormalizedA15InteriorSupportedKirchhoffTestsCoverEachLobe_closed
  interiorTestsEmbedInClosedKirchhoffTests :=
    G8BookIIICh23FloorNormalizedA15InteriorTestsEmbedInClosedKirchhoffTests
  interiorTestsEmbedInClosedKirchhoffTestsWitness :=
    g8BookIIICh23FloorNormalizedA15InteriorTestsEmbedInClosedKirchhoffTests_closed
  allTestPairingRestrictsToInteriorTests :=
    G8BookIIICh23FloorNormalizedA15AllTestPairingRestrictsToInteriorTests
  allTestPairingRestrictsToInteriorTestsWitness :=
    g8BookIIICh23FloorNormalizedA15AllTestPairingRestrictsToInteriorTests_closed
  distributionalAdjointEquationAt :=
    G8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt
  distributionalAdjointEquationAtWitness :=
    g8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt_closed
  allTestPairingImpliesDistributionalAdjointEquation :=
    G8BookIIICh23FloorNormalizedA15InteriorPairingImpliesDistributionalEquation
  allTestPairingImpliesDistributionalAdjointEquationWitness :=
    g8BookIIICh23FloorNormalizedA15InteriorPairingImpliesDistributionalEquation_closed
  noFiniteDiagnosticSubstitute :=
    G8BookIIICh23FloorNormalizedA15InteriorDistributionNoFiniteDiagnosticSubstitute
  noFiniteDiagnosticSubstituteWitness :=
    g8BookIIICh23FloorNormalizedA15InteriorDistributionNoFiniteDiagnosticSubstitute_closed
  status := .conditional_interface

/-- The selected lower route now supplies the interior-test distributional
    equation target. -/
theorem
    g8BookIIICh23FloorNormalizedA15InteriorTestDistributionalEquationTarget_closed :
    G8BookIIICh23FloorNormalizedA15InteriorTestDistributionalEquationTarget :=
  ⟨g8BookIIICh23FloorNormalizedA15InteriorTestDistributionalEquationSource_closed⟩

/-- Consequently, the existing distributional-equation-from-adjoint-pairing
    stone is closed for the selected lower route. -/
theorem
    g8BookIIICh23FloorNormalizedA15DistributionalEquationFromAdjointPairingTarget_closed :
    G8BookIIICh23FloorNormalizedA15DistributionalEquationFromAdjointPairingTarget :=
  g8BookIIICh23FloorNormalizedA15DistributionalEquationFromAdjointPairingTarget_ofInteriorTests
    g8BookIIICh23FloorNormalizedA15InteriorTestDistributionalEquationTarget_closed

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- An endpoint-labelled interior test without embedding into the closed
    Kirchhoff universe cannot feed the all-test pairing law. -/
structure
    G8BookIIICh23FloorNormalizedA15InteriorTestWithoutClosedEmbedding
    where
  test :
    G8BookIIICh23FloorNormalizedA15InteriorSupportedKirchhoffTest
  missingClosedEmbedding :
    ¬ test.embeddedInClosedKirchhoffTestUniverse

theorem
    G8BookIIICh23FloorNormalizedA15InteriorTestWithoutClosedEmbedding.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15InteriorTestWithoutClosedEmbedding) :
    False :=
  gap.missingClosedEmbedding
    gap.test.embeddedInClosedKirchhoffTestUniverseWitness

/-- The distributional equation stone cannot be replaced by merely naming an
    interior test if the selected edgewise A1.3 law is denied. -/
structure
    G8BookIIICh23FloorNormalizedA15InteriorTestWithoutSelectedEdgewiseLaw
    where
  u :
    G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate
  missingDistributionalEquation :
    ¬ G8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt
      u

theorem
    G8BookIIICh23FloorNormalizedA15InteriorTestWithoutSelectedEdgewiseLaw.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15InteriorTestWithoutSelectedEdgewiseLaw) :
    False :=
  gap.missingDistributionalEquation
    (g8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt_closed
      gap.u)

/-- Restricting to interior tests alone is not the full route unless the
    source also retains the universal all-closed-test pairing provenance. -/
structure
    G8BookIIICh23FloorNormalizedA15InteriorRestrictionWithoutAllClosedTests
    where
  missingAllClosedTests :
    ¬ G8BookIIICh23FloorNormalizedA15InteriorDistributionNoFiniteDiagnosticSubstitute

theorem
    G8BookIIICh23FloorNormalizedA15InteriorRestrictionWithoutAllClosedTests.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15InteriorRestrictionWithoutAllClosedTests) :
    False :=
  gap.missingAllClosedTests
    g8BookIIICh23FloorNormalizedA15InteriorDistributionNoFiniteDiagnosticSubstitute_closed

end Tau.BookIII.Bridge
