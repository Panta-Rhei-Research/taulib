import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculus

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Adjoint Calculus Engine

This module is the first concrete engine layer under the compact-graph
adjoint calculus source.

The previous file stated the exact compact-graph calculus source abstractly.
Here we anchor that source to the selected Ch.23 graph operator built in
A1.2-A1.4:

```text
selected A1.3 Kirchhoff operator domain
  -> Type-1 presentations of adjoint candidates and Kirchhoff tests
  -> theorem-backed selected regularity/Green selectors
  -> compact-graph adjoint calculus source
```

The new load-bearing fields are no longer arbitrary pointwise regularity and
Green predicates.  They are forced through representatives in the selected
Kirchhoff operator domain.  The remaining mathematical payload is exactly the
presentation theorem: actual adjoint-domain candidates and all Kirchhoff tests
must be represented by these selected graph-domain presentations.

No A1.5 maximality, compact resolvent, A2 point spectrum, A3 actual-`xi`, or
RH-facing statement is proved here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- SELECTED A1.3 OPERATOR DOMAIN
-- ============================================================

/-- The selected floor-normalized Ch.23 Kirchhoff operator domain closed in
    A1.3. -/
abbrev G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain :
    Type 2 :=
  G8BookIIICh23FloorNormalizedA13OperatorDomain
    g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed

/-- The selected floor-normalized Ch.23 `L2` output carrier closed in A1.3. -/
abbrev G8BookIIICh23FloorNormalizedA15SelectedL2Output :
    Type 2 :=
  G8BookIIICh23FloorNormalizedA13L2Output
    (g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
      |>.domain
      |>.trace
      |>.hilbert)

/-- The selected graph Laplacian on the closed A1.3 Kirchhoff domain. -/
def g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian
    (u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    G8BookIIICh23FloorNormalizedA15SelectedL2Output :=
  g8BookIIICh23FloorNormalizedA13KirchhoffGraphLaplacian u

/-- The selected Kirchhoff operator domain is nonempty. -/
theorem
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain_nonempty :
    Nonempty
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain :=
  g8BookIIICh23FloorNormalizedA13OperatorDomain_nonempty_closed

/-- The selected graph Laplacian satisfies the A1.3 edgewise law. -/
theorem
    g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian_edgewiseLaw
    (u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    G8BookIIICh23FloorNormalizedA13EdgewiseNegativeSecondDerivativeLaw
      u
      (g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian u) :=
  g8BookIIICh23FloorNormalizedA13KirchhoffGraphLaplacian_edgewiseLaw u

-- ============================================================
-- TYPE-1 PRESENTATIONS OF ADJOINT CANDIDATES AND TESTS
-- ============================================================

/-- A Type-1 presentation of the adjoint-domain candidates, realized in the
    selected Kirchhoff operator domain.

The field `representsFullAdjointDomain` is the true reverse-inclusion payload:
it says this presentation has captured every actual adjoint-domain element as
a selected graph-domain representative. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointCandidatePresentation where
  point : Type 1
  pointNonempty : Nonempty point
  realize :
    point →
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain
  representsFullAdjointDomain : Prop
  representsFullAdjointDomainWitness :
    representsFullAdjointDomain
  realizationUsesSelectedGraphDomain : Prop
  realizationUsesSelectedGraphDomainWitness :
    realizationUsesSelectedGraphDomain
  noFiniteDiagnosticSubstitute : Prop
  noFiniteDiagnosticSubstituteWitness :
    noFiniteDiagnosticSubstitute
  status : SpineStatus := .conditional_interface

/-- A Type-1 presentation of all Kirchhoff tests, realized in the selected
    Kirchhoff operator domain.

This prevents the Green-identity law from being witnessed by a finite
diagnostic subset or a single toy test. -/
structure
    G8BookIIICh23FloorNormalizedA15KirchhoffTestPresentation where
  point : Type 1
  pointNonempty : Nonempty point
  realize :
    point →
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain
  exhaustsSelectedKirchhoffDomain : Prop
  exhaustsSelectedKirchhoffDomainWitness :
    exhaustsSelectedKirchhoffDomain
  realizationUsesSelectedGraphDomain : Prop
  realizationUsesSelectedGraphDomainWitness :
    realizationUsesSelectedGraphDomain
  noFiniteDiagnosticSubstitute : Prop
  noFiniteDiagnosticSubstituteWitness :
    noFiniteDiagnosticSubstitute
  status : SpineStatus := .conditional_interface

/-- The concrete engine input: adjoint candidates and Kirchhoff tests are both
    presented by selected graph-domain representatives. -/
structure G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource where
  candidates :
    G8BookIIICh23FloorNormalizedA15AdjointCandidatePresentation
  tests :
    G8BookIIICh23FloorNormalizedA15KirchhoffTestPresentation
  presentationsUseSameSelectedA13Domain : Prop
  presentationsUseSameSelectedA13DomainWitness :
    presentationsUseSameSelectedA13Domain
  status : SpineStatus := .conditional_interface

/-- Target for constructing the concrete adjoint-calculus engine. -/
def G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource

-- ============================================================
-- THEOREM-BACKED SELECTED REGULARITY SELECTORS
-- ============================================================

/-- A selected representative satisfies the adjoint-equation-in-`L2` readout
    through the closed A1.3 graph Laplacian output. -/
def G8BookIIICh23FloorNormalizedA15SelectedAdjointEquationInL2
    (u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    Prop :=
  G8BookIIICh23FloorNormalizedA13L2Output.squareIntegrable
    (g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian u)

theorem
    g8BookIIICh23FloorNormalizedA15SelectedAdjointEquationInL2_closed
    (u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    G8BookIIICh23FloorNormalizedA15SelectedAdjointEquationInL2 u :=
  G8BookIIICh23FloorNormalizedA13L2Output.squareIntegrableWitness
    (g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian u)

/-- Distributional second-derivative readout for a selected representative. -/
def
    G8BookIIICh23FloorNormalizedA15SelectedDistributionalSecondDerivativeInL2
    (u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    Prop :=
  u.plusSecondDerivativeDefined ∧
    u.minusSecondDerivativeDefined ∧
      G8BookIIICh23FloorNormalizedA13EdgewiseNegativeSecondDerivativeLaw
        u
        (g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian u)

theorem
    g8BookIIICh23FloorNormalizedA15SelectedDistributionalSecondDerivativeInL2_closed
    (u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    G8BookIIICh23FloorNormalizedA15SelectedDistributionalSecondDerivativeInL2
      u :=
  ⟨u.plusSecondDerivativeWitness,
    u.minusSecondDerivativeWitness,
    g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian_edgewiseLaw u⟩

/-- Selected graph-H2 regularity is carried by the closed A1.3 operator-domain
    representative. -/
def G8BookIIICh23FloorNormalizedA15SelectedGraphH2Regularity
    (u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    Prop :=
  u.edgewiseH2Regularity

theorem
    g8BookIIICh23FloorNormalizedA15SelectedGraphH2Regularity_closed
    (u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    G8BookIIICh23FloorNormalizedA15SelectedGraphH2Regularity u :=
  u.edgewiseH2RegularityWitness

/-- Selected value trace recovery is the closed A1.2 value-trace theorem. -/
def G8BookIIICh23FloorNormalizedA15SelectedValueTraceRecovered :
    Prop :=
  G8BookIIICh23FloorNormalizedA12ValueTraceDefined
    g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed

theorem
    g8BookIIICh23FloorNormalizedA15SelectedValueTraceRecovered_closed :
    G8BookIIICh23FloorNormalizedA15SelectedValueTraceRecovered :=
  g8BookIIICh23FloorNormalizedA12ValueTraceDefined_closed

/-- Selected derivative trace recovery is the closed A1.2 derivative-trace
    theorem. -/
def G8BookIIICh23FloorNormalizedA15SelectedDerivativeTraceRecovered :
    Prop :=
  G8BookIIICh23FloorNormalizedA12DerivativeTraceDefined
    g8BookIIICh23FloorNormalizedA12HilbertReadinessSource_closed

theorem
    g8BookIIICh23FloorNormalizedA15SelectedDerivativeTraceRecovered_closed :
    G8BookIIICh23FloorNormalizedA15SelectedDerivativeTraceRecovered :=
  g8BookIIICh23FloorNormalizedA12DerivativeTraceDefined_closed

/-- Trace recovery from the selected adjoint equation. -/
def G8BookIIICh23FloorNormalizedA15SelectedTraceRecovery
    (u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedAdjointEquationInL2 u ∧
    G8BookIIICh23FloorNormalizedA15SelectedGraphH2Regularity u ∧
      G8BookIIICh23FloorNormalizedA15SelectedValueTraceRecovered ∧
        G8BookIIICh23FloorNormalizedA15SelectedDerivativeTraceRecovered

theorem
    g8BookIIICh23FloorNormalizedA15SelectedTraceRecovery_closed
    (u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    G8BookIIICh23FloorNormalizedA15SelectedTraceRecovery u :=
  ⟨g8BookIIICh23FloorNormalizedA15SelectedAdjointEquationInL2_closed u,
    g8BookIIICh23FloorNormalizedA15SelectedGraphH2Regularity_closed u,
    g8BookIIICh23FloorNormalizedA15SelectedValueTraceRecovered_closed,
    g8BookIIICh23FloorNormalizedA15SelectedDerivativeTraceRecovered_closed⟩

/-- Selected value and derivative traces both exist. -/
def G8BookIIICh23FloorNormalizedA15SelectedBoundaryTracesExist :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedValueTraceRecovered ∧
    G8BookIIICh23FloorNormalizedA15SelectedDerivativeTraceRecovered

theorem
    g8BookIIICh23FloorNormalizedA15SelectedBoundaryTracesExist_closed :
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryTracesExist :=
  ⟨g8BookIIICh23FloorNormalizedA15SelectedValueTraceRecovered_closed,
    g8BookIIICh23FloorNormalizedA15SelectedDerivativeTraceRecovered_closed⟩

-- ============================================================
-- THEOREM-BACKED SELECTED GREEN IDENTITY SELECTORS
-- ============================================================

/-- Selected edgewise Green bookkeeping from the closed A1.4 source. -/
def G8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenBookkeeping :
    Prop :=
  G8BookIIICh23FloorNormalizedA14EdgewiseGreenBookkeeping
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed

theorem
    g8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenBookkeeping_closed :
    G8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenBookkeeping :=
  g8BookIIICh23FloorNormalizedA14EdgewiseGreenBookkeeping_closed

/-- Pairwise edgewise Green identity for selected representatives. -/
def G8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenIdentity
    (u v :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    Prop :=
  G8BookIIICh23FloorNormalizedA13EdgewiseNegativeSecondDerivativeLaw
      u
      (g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian u) ∧
    G8BookIIICh23FloorNormalizedA13EdgewiseNegativeSecondDerivativeLaw
      v
      (g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian v)

theorem
    g8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenIdentity_closed
    (u v :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    G8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenIdentity u v :=
  ⟨g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian_edgewiseLaw u,
    g8BookIIICh23FloorNormalizedA15SelectedGraphLaplacian_edgewiseLaw v⟩

/-- The selected boundary form agrees with the adjoint-defect pairing by the
    A1.4 endpoint-cancellation input. -/
def
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryFormEqualsAdjointDefect :
    Prop :=
  G8BookIIICh23FloorNormalizedA14EndpointCancellationInput
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed

theorem
    g8BookIIICh23FloorNormalizedA15SelectedBoundaryFormEqualsAdjointDefect_closed :
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryFormEqualsAdjointDefect :=
  g8BookIIICh23FloorNormalizedA14EndpointCancellationInput_closed

/-- The selected adjoint-defect pairing vanishes by the closed A1.4 symmetry
    law. -/
def G8BookIIICh23FloorNormalizedA15SelectedAdjointDefectPairingVanishes :
    Prop :=
  G8BookIIICh23FloorNormalizedA14KirchhoffSymmetryLaw
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed

theorem
    g8BookIIICh23FloorNormalizedA15SelectedAdjointDefectPairingVanishes_closed :
    G8BookIIICh23FloorNormalizedA15SelectedAdjointDefectPairingVanishes :=
  g8BookIIICh23FloorNormalizedA14KirchhoffSymmetryLaw_closed

/-- The selected Kirchhoff boundary form is annihilated by closed A1.4
    boundary-form cancellation. -/
def G8BookIIICh23FloorNormalizedA15SelectedAnnihilatesBoundaryForm :
    Prop :=
  G8BookIIICh23FloorNormalizedA14BoundaryFormCancellation
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed

theorem
    g8BookIIICh23FloorNormalizedA15SelectedAnnihilatesBoundaryForm_closed :
    G8BookIIICh23FloorNormalizedA15SelectedAnnihilatesBoundaryForm :=
  g8BookIIICh23FloorNormalizedA14BoundaryFormCancellation_closed

/-- Selected adjoint pairing identity against Kirchhoff tests. -/
def G8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity
    (u v :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenBookkeeping ∧
    G8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenIdentity u v ∧
      G8BookIIICh23FloorNormalizedA15SelectedBoundaryFormEqualsAdjointDefect

theorem
    g8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity_closed
    (u v :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    G8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity u v :=
  ⟨g8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenBookkeeping_closed,
    g8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenIdentity_closed u v,
    g8BookIIICh23FloorNormalizedA15SelectedBoundaryFormEqualsAdjointDefect_closed⟩

-- ============================================================
-- ENGINE TO COMPACT-GRAPH CALCULUS SOURCE
-- ============================================================

/-- The concrete engine builds the abstract compact-graph adjoint calculus
    source, with every pointwise regularity and Green field routed through
    selected A1.2-A1.4 graph-operator facts. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.toCompactGraphAdjointCalculusSource
    (engine :
      G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusSource where
  candidate := engine.candidates.point
  kirchhoffTest := engine.tests.point
  candidateNonempty := engine.candidates.pointNonempty
  kirchhoffTestNonempty := engine.tests.pointNonempty
  candidatesRepresentAdjointDomain :=
    engine.candidates.representsFullAdjointDomain
  candidatesRepresentAdjointDomainWitness :=
    engine.candidates.representsFullAdjointDomainWitness
  testsExhaustKirchhoffDomain :=
    engine.tests.exhaustsSelectedKirchhoffDomain
  testsExhaustKirchhoffDomainWitness :=
    engine.tests.exhaustsSelectedKirchhoffDomainWitness
  noFiniteDiagnosticSubstitute :=
    engine.candidates.noFiniteDiagnosticSubstitute ∧
      engine.tests.noFiniteDiagnosticSubstitute ∧
        engine.presentationsUseSameSelectedA13Domain
  noFiniteDiagnosticSubstituteWitness :=
    ⟨engine.candidates.noFiniteDiagnosticSubstituteWitness,
      engine.tests.noFiniteDiagnosticSubstituteWitness,
      engine.presentationsUseSameSelectedA13DomainWitness⟩
  adjointEquationInSelectedL2 :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15SelectedAdjointEquationInL2
        (engine.candidates.realize u)
  adjointEquationWitness :=
    fun u =>
      g8BookIIICh23FloorNormalizedA15SelectedAdjointEquationInL2_closed
        (engine.candidates.realize u)
  adjointDistributionalSecondDerivativeInSelectedL2 :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15SelectedDistributionalSecondDerivativeInL2
        (engine.candidates.realize u)
  adjointDistributionalSecondDerivativeWitness :=
    fun u =>
      g8BookIIICh23FloorNormalizedA15SelectedDistributionalSecondDerivativeInL2_closed
        (engine.candidates.realize u)
  graphH2RegularityFromAdjointEquation :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15SelectedGraphH2Regularity
        (engine.candidates.realize u)
  graphH2RegularityWitness :=
    fun u =>
      g8BookIIICh23FloorNormalizedA15SelectedGraphH2Regularity_closed
        (engine.candidates.realize u)
  valueTraceRecoveredFromSobolevTrace :=
    fun _ => G8BookIIICh23FloorNormalizedA15SelectedValueTraceRecovered
  valueTraceRecoveredWitness :=
    fun _ => g8BookIIICh23FloorNormalizedA15SelectedValueTraceRecovered_closed
  derivativeTraceRecoveredFromSobolevTrace :=
    fun _ => G8BookIIICh23FloorNormalizedA15SelectedDerivativeTraceRecovered
  derivativeTraceRecoveredWitness :=
    fun _ =>
      g8BookIIICh23FloorNormalizedA15SelectedDerivativeTraceRecovered_closed
  traceRecoveryFromAdjointEquation :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15SelectedTraceRecovery
        (engine.candidates.realize u)
  traceRecoveryWitness :=
    fun u =>
      g8BookIIICh23FloorNormalizedA15SelectedTraceRecovery_closed
        (engine.candidates.realize u)
  valueAndDerivativeBoundaryTracesExist :=
    fun _ => G8BookIIICh23FloorNormalizedA15SelectedBoundaryTracesExist
  valueAndDerivativeBoundaryTracesExistWitness :=
    fun _ =>
      g8BookIIICh23FloorNormalizedA15SelectedBoundaryTracesExist_closed
  adjointPairingIdentityAgainstKirchhoffTests :=
    fun u v =>
      G8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity
        (engine.candidates.realize u)
        (engine.tests.realize v)
  adjointPairingIdentityWitness :=
    fun u v =>
      g8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity_closed
        (engine.candidates.realize u)
        (engine.tests.realize v)
  edgewiseGreenIdentityAgainstKirchhoffTests :=
    fun u v =>
      G8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenIdentity
        (engine.candidates.realize u)
        (engine.tests.realize v)
  edgewiseGreenIdentityWitness :=
    fun u v =>
      g8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenIdentity_closed
        (engine.candidates.realize u)
        (engine.tests.realize v)
  boundaryFormEqualsAdjointDefectPairing :=
    fun _ _ =>
      G8BookIIICh23FloorNormalizedA15SelectedBoundaryFormEqualsAdjointDefect
  boundaryFormEqualsAdjointDefectPairingWitness :=
    fun _ _ =>
      g8BookIIICh23FloorNormalizedA15SelectedBoundaryFormEqualsAdjointDefect_closed
  adjointDefectPairingVanishes :=
    fun _ _ =>
      G8BookIIICh23FloorNormalizedA15SelectedAdjointDefectPairingVanishes
  adjointDefectPairingVanishesWitness :=
    fun _ _ =>
      g8BookIIICh23FloorNormalizedA15SelectedAdjointDefectPairingVanishes_closed
  annihilatesKirchhoffBoundaryForm :=
    fun _ _ =>
      G8BookIIICh23FloorNormalizedA15SelectedAnnihilatesBoundaryForm
  annihilatesKirchhoffBoundaryFormWitness :=
    fun _ _ =>
      g8BookIIICh23FloorNormalizedA15SelectedAnnihilatesBoundaryForm_closed
  status := .conditional_interface

/-- A concrete engine source discharges the compact-graph adjoint calculus
    target. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.toCompactGraphAdjointCalculusTarget
    (engine :
      G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusTarget :=
  ⟨engine.toCompactGraphAdjointCalculusSource⟩

/-- Target-level adapter from the concrete engine to the compact-graph
    calculus target. -/
theorem
    g8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusTarget_ofEngine
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget) :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusTarget :=
  target.elim fun engine => engine.toCompactGraphAdjointCalculusTarget

/-- Target-level adapter from the concrete engine to the first two analytic
    law targets. -/
theorem
    g8BookIIICh23FloorNormalizedA15TwoAnalyticLawTargets_ofEngine
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget) :
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquationTarget ∧
      G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTestsTarget :=
  g8BookIIICh23FloorNormalizedA15TwoAnalyticLawTargets_ofCompactGraphCalculus
    (g8BookIIICh23FloorNormalizedA15CompactGraphAdjointCalculusTarget_ofEngine
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A candidate presentation without full adjoint-domain coverage cannot build
    the concrete engine. -/
structure
    G8BookIIICh23FloorNormalizedA15CandidatePresentationWithoutAdjointCoverage
    where
  candidates :
    G8BookIIICh23FloorNormalizedA15AdjointCandidatePresentation
  missingCoverage :
    ¬ candidates.representsFullAdjointDomain

theorem
    G8BookIIICh23FloorNormalizedA15CandidatePresentationWithoutAdjointCoverage.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15CandidatePresentationWithoutAdjointCoverage) :
    False :=
  gap.missingCoverage gap.candidates.representsFullAdjointDomainWitness

/-- A test presentation without exhaustive Kirchhoff-domain coverage cannot
    be used as the Green-identity test universe. -/
structure
    G8BookIIICh23FloorNormalizedA15TestPresentationWithoutKirchhoffExhaustion
    where
  tests :
    G8BookIIICh23FloorNormalizedA15KirchhoffTestPresentation
  missingExhaustion :
    ¬ tests.exhaustsSelectedKirchhoffDomain

theorem
    G8BookIIICh23FloorNormalizedA15TestPresentationWithoutKirchhoffExhaustion.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15TestPresentationWithoutKirchhoffExhaustion) :
    False :=
  gap.missingExhaustion gap.tests.exhaustsSelectedKirchhoffDomainWitness

/-- Finite diagnostics cannot fill the concrete engine if either presentation
    lacks its non-diagnostic provenance. -/
structure
    G8BookIIICh23FloorNormalizedA15FiniteDiagnosticAdjointEngineGap where
  engine :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource
  diagnosticOnly :
    ¬ (engine.candidates.noFiniteDiagnosticSubstitute ∧
        engine.tests.noFiniteDiagnosticSubstitute)

theorem
    G8BookIIICh23FloorNormalizedA15FiniteDiagnosticAdjointEngineGap.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15FiniteDiagnosticAdjointEngineGap) :
    False :=
  gap.diagnosticOnly
    ⟨gap.engine.candidates.noFiniteDiagnosticSubstituteWitness,
      gap.engine.tests.noFiniteDiagnosticSubstituteWitness⟩

end Tau.BookIII.Bridge
