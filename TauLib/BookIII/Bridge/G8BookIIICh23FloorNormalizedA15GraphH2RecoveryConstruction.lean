import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15InteriorTestDistributionalEquationConstruction

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Graph-H2 Recovery Construction

This module closes the next lower-route A1.5 stone after the interior-test
distributional equation:

```text
actual adjoint candidate
  -> selected L2 graph-Laplacian output
  -> selected distributional second-derivative equation
  -> selected graph-H2 regularity
  -> value/derivative trace recovery
```

The proof is intentionally still upstream of the all-test Green identity and
boundary-form annihilator classification.  It constructs only the graph-H2
trace-recovery law and the graph-H2 recovery source consumed by the lower
Hilbert-adjoint graph-predicate route.

No spectral, A3 actual-`xi`, final RH, O3, determinant, divisor,
accepted-coverage, or completion source is imported or used.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- POINTWISE GRAPH-H2 RECOVERY FOR ACTUAL ADJOINT CANDIDATES
-- ============================================================

/-- The selected adjoint equation in `L2` for an actual adjoint candidate. -/
def
    G8BookIIICh23FloorNormalizedA15ActualAdjointEquationInSelectedL2At
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedAdjointEquationInL2
    u.selectedRepresentative

/-- The selected graph-Laplacian output is square-integrable for every actual
    adjoint candidate. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualAdjointEquationInSelectedL2At_closed
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate) :
    G8BookIIICh23FloorNormalizedA15ActualAdjointEquationInSelectedL2At
      u :=
  g8BookIIICh23FloorNormalizedA15SelectedAdjointEquationInL2_closed
    u.selectedRepresentative

/-- The graph-H2 regularity recovered for an actual adjoint candidate. -/
def
    G8BookIIICh23FloorNormalizedA15ActualGraphH2RegularityRecoveredAt
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedGraphH2Regularity
    u.selectedRepresentative

/-- Every actual adjoint candidate has selected graph-H2 regularity on the
    lower route. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualGraphH2RegularityRecoveredAt_closed
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate) :
    G8BookIIICh23FloorNormalizedA15ActualGraphH2RegularityRecoveredAt
      u :=
  g8BookIIICh23FloorNormalizedA15SelectedGraphH2Regularity_closed
    u.selectedRepresentative

/-- Value-trace recovery for actual adjoint candidates through the selected
    A1.2 Sobolev trace package. -/
def
    G8BookIIICh23FloorNormalizedA15ActualValueTraceRecoveredFromSobolevTrace :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedValueTraceRecovered

/-- The selected A1.2 value-trace theorem supplies the value trace. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualValueTraceRecoveredFromSobolevTrace_closed :
    G8BookIIICh23FloorNormalizedA15ActualValueTraceRecoveredFromSobolevTrace :=
  g8BookIIICh23FloorNormalizedA15SelectedValueTraceRecovered_closed

/-- Derivative-trace recovery for actual adjoint candidates through the
    selected A1.2 Sobolev trace package. -/
def
    G8BookIIICh23FloorNormalizedA15ActualDerivativeTraceRecoveredFromSobolevTrace :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedDerivativeTraceRecovered

/-- The selected A1.2 derivative-trace theorem supplies the derivative
    trace. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualDerivativeTraceRecoveredFromSobolevTrace_closed :
    G8BookIIICh23FloorNormalizedA15ActualDerivativeTraceRecoveredFromSobolevTrace :=
  g8BookIIICh23FloorNormalizedA15SelectedDerivativeTraceRecovered_closed

/-- Full trace recovery at an actual adjoint candidate. -/
def
    G8BookIIICh23FloorNormalizedA15ActualTraceRecoveryFromAdjointEquationAt
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedTraceRecovery
    u.selectedRepresentative

/-- The selected trace-recovery theorem closes the pointwise recovery at each
    actual adjoint candidate. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualTraceRecoveryFromAdjointEquationAt_closed
    (u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate) :
    G8BookIIICh23FloorNormalizedA15ActualTraceRecoveryFromAdjointEquationAt
      u :=
  g8BookIIICh23FloorNormalizedA15SelectedTraceRecovery_closed
    u.selectedRepresentative

/-- Actual adjoint candidates have both value and derivative boundary traces
    after graph-H2 recovery. -/
def
    G8BookIIICh23FloorNormalizedA15ActualBoundaryTracesExist :
    Prop :=
  G8BookIIICh23FloorNormalizedA15SelectedBoundaryTracesExist

/-- The selected A1.2 trace package supplies both boundary traces. -/
theorem
    g8BookIIICh23FloorNormalizedA15ActualBoundaryTracesExist_closed :
    G8BookIIICh23FloorNormalizedA15ActualBoundaryTracesExist :=
  g8BookIIICh23FloorNormalizedA15SelectedBoundaryTracesExist_closed

-- ============================================================
-- GRAPH-H2 TRACE-RECOVERY LAW
-- ============================================================

/-- The selected lower route proves the graph-H2 trace-recovery law. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation_closed :
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation
    where
  selectedTraceReadiness :=
    g8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint_closed
  selectedEdgewiseH2KirchhoffDomainReady :=
    g8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady_closed
  adjointEquationInSelectedL2 :=
    ∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      G8BookIIICh23FloorNormalizedA15ActualAdjointEquationInSelectedL2At
        u
  adjointEquationInSelectedL2Witness :=
    g8BookIIICh23FloorNormalizedA15ActualAdjointEquationInSelectedL2At_closed
  adjointDistributionalSecondDerivativeInSelectedL2 :=
    ∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      G8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt
        u
  adjointDistributionalSecondDerivativeWitness :=
    g8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt_closed
  graphH2RegularityFromAdjointEquation :=
    ∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      G8BookIIICh23FloorNormalizedA15ActualGraphH2RegularityRecoveredAt
        u
  graphH2RegularityFromAdjointEquationWitness :=
    g8BookIIICh23FloorNormalizedA15ActualGraphH2RegularityRecoveredAt_closed
  valueTraceRecoveredFromSobolevTrace :=
    G8BookIIICh23FloorNormalizedA15ActualValueTraceRecoveredFromSobolevTrace
  valueTraceRecoveredWitness :=
    g8BookIIICh23FloorNormalizedA15ActualValueTraceRecoveredFromSobolevTrace_closed
  derivativeTraceRecoveredFromSobolevTrace :=
    G8BookIIICh23FloorNormalizedA15ActualDerivativeTraceRecoveredFromSobolevTrace
  derivativeTraceRecoveredWitness :=
    g8BookIIICh23FloorNormalizedA15ActualDerivativeTraceRecoveredFromSobolevTrace_closed
  traceRecoveryFromAdjointEquation :=
    ∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      G8BookIIICh23FloorNormalizedA15ActualTraceRecoveryFromAdjointEquationAt
        u
  traceRecoveryFromAdjointEquationWitness :=
    g8BookIIICh23FloorNormalizedA15ActualTraceRecoveryFromAdjointEquationAt_closed
  valueAndDerivativeBoundaryTracesExist :=
    G8BookIIICh23FloorNormalizedA15ActualBoundaryTracesExist
  valueAndDerivativeBoundaryTracesExistWitness :=
    g8BookIIICh23FloorNormalizedA15ActualBoundaryTracesExist_closed
  status := .conditional_interface

/-- Target-level closure of graph-H2 trace recovery from the adjoint
    equation. -/
theorem
    g8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquationTarget_closed :
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquationTarget :=
  ⟨g8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation_closed⟩

-- ============================================================
-- LOWER GRAPH-PREDICATE ROUTE SOURCE
-- ============================================================

/-- The proof that graph-H2 recovery is driven by L2 output plus the
    distributional second-derivative equation, not by a finite diagnostic
    trace sample. -/
def
    G8BookIIICh23FloorNormalizedA15RecoveredFromL2OutputAndDistributionalSecondDerivative :
    Prop :=
  ∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
    G8BookIIICh23FloorNormalizedA15ActualAdjointEquationInSelectedL2At u ∧
      G8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt u ∧
        G8BookIIICh23FloorNormalizedA15ActualGraphH2RegularityRecoveredAt u

/-- The selected lower route supplies the L2, distributional, and graph-H2
    data for every actual adjoint candidate. -/
theorem
    g8BookIIICh23FloorNormalizedA15RecoveredFromL2OutputAndDistributionalSecondDerivative_closed :
    G8BookIIICh23FloorNormalizedA15RecoveredFromL2OutputAndDistributionalSecondDerivative :=
  fun u =>
    ⟨g8BookIIICh23FloorNormalizedA15ActualAdjointEquationInSelectedL2At_closed
        u,
      g8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt_closed
        u,
      g8BookIIICh23FloorNormalizedA15ActualGraphH2RegularityRecoveredAt_closed
        u⟩

/-- The graph-H2 recovery source consumed by the Hilbert-adjoint
    graph-predicate route. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphSource_closed :
    G8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphSource
    where
  distributional :=
    g8BookIIICh23FloorNormalizedA15InteriorTestDistributionalEquationSource_closed
      |>.toDistributionalEquationFromAdjointPairingSource
  graphH2TraceRecoveryAt :=
    G8BookIIICh23FloorNormalizedA15ActualTraceRecoveryFromAdjointEquationAt
  graphH2TraceRecoveryAtWitness :=
    g8BookIIICh23FloorNormalizedA15ActualTraceRecoveryFromAdjointEquationAt_closed
  recoveredFromL2OutputAndDistributionalSecondDerivative :=
    G8BookIIICh23FloorNormalizedA15RecoveredFromL2OutputAndDistributionalSecondDerivative
  recoveredFromL2OutputAndDistributionalSecondDerivativeWitness :=
    g8BookIIICh23FloorNormalizedA15RecoveredFromL2OutputAndDistributionalSecondDerivative_closed
  status := .conditional_interface

/-- Target-level closure of graph-H2 recovery in the lower graph-predicate
    route. -/
theorem
    g8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphTarget_closed :
    G8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphTarget :=
  ⟨g8BookIIICh23FloorNormalizedA15GraphH2RecoveryFromHilbertAdjointGraphSource_closed⟩

-- ============================================================
-- TRACE-EXISTENCE CONSEQUENCES
-- ============================================================

/-- The closed graph-H2 trace-recovery law supplies adjoint boundary trace
    existence. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource_ofGraphH2Recovery :
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource :=
  g8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquation_closed
    |>.toTraceExistenceSource

/-- Target-level adjoint trace existence follows from graph-H2 recovery. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointTraceExistenceSourceTarget_ofGraphH2Recovery :
    Nonempty
      G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource :=
  ⟨g8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource_ofGraphH2Recovery⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- L2 output alone is not the graph-H2 recovery stone; the distributional
    second-derivative equation is also load-bearing. -/
structure
    G8BookIIICh23FloorNormalizedA15GraphH2RecoveryWithoutDistributionalEquation
    where
  l2Only :
    ∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      G8BookIIICh23FloorNormalizedA15ActualAdjointEquationInSelectedL2At u
  missingDistributional :
    ¬ (∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      G8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt
        u)

theorem
    G8BookIIICh23FloorNormalizedA15GraphH2RecoveryWithoutDistributionalEquation.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15GraphH2RecoveryWithoutDistributionalEquation) :
    False :=
  gap.missingDistributional
    g8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt_closed

/-- Distributional second-derivative data without selected graph-H2 regularity
    cannot produce endpoint trace recovery. -/
structure
    G8BookIIICh23FloorNormalizedA15DistributionalEquationWithoutGraphH2Regularity
    where
  distributional :
    ∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      G8BookIIICh23FloorNormalizedA15InteriorTestDistributionalAdjointEquationAt
        u
  missingGraphH2 :
    ¬ (∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      G8BookIIICh23FloorNormalizedA15ActualGraphH2RegularityRecoveredAt u)

theorem
    G8BookIIICh23FloorNormalizedA15DistributionalEquationWithoutGraphH2Regularity.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15DistributionalEquationWithoutGraphH2Regularity) :
    False :=
  gap.missingGraphH2
    g8BookIIICh23FloorNormalizedA15ActualGraphH2RegularityRecoveredAt_closed

/-- Graph-H2 regularity without Sobolev trace readiness is not enough for the
    downstream endpoint-trace route. -/
structure
    G8BookIIICh23FloorNormalizedA15GraphH2RegularityWithoutTraceReadiness
    where
  graphH2 :
    ∀ u : G8BookIIICh23FloorNormalizedA15ActualAdjointCandidate,
      G8BookIIICh23FloorNormalizedA15ActualGraphH2RegularityRecoveredAt u
  missingTraceReadiness :
    ¬ G8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint

theorem
    G8BookIIICh23FloorNormalizedA15GraphH2RegularityWithoutTraceReadiness.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15GraphH2RegularityWithoutTraceReadiness) :
    False :=
  gap.missingTraceReadiness
    g8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint_closed

end Tau.BookIII.Bridge
