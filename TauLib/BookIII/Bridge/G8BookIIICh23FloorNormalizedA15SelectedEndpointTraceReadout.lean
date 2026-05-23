import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadout

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Selected Endpoint Trace Readout

This module constructs the concrete finite four-coordinate boundary trace used
by the A1.5 reverse-inclusion route.

The previous compact-graph finite-trace layer exposed the exact remaining
payload:

```text
compact graph adjoint calculus
  + finite boundary trace for every adjoint candidate
  + annihilator law against all Kirchhoff tests
  -> A1.5 maximal Kirchhoff self-adjointness
```

Here the trace is read from the selected A1.3 Kirchhoff-domain representative
carried by the concrete A1.5 engine.  The selected representative stores its
four endpoint values and four outgoing derivatives, together with the
Kirchhoff endpoint laws supplied by the selected domain.  The closed finite
boundary algebra then proves that this trace annihilates every Kirchhoff test
trace.

This does not construct the concrete engine itself: the remaining
operator-theory payload is still the presentation/reverse-inclusion theorem
that actual adjoint-domain candidates are represented by the selected
Kirchhoff domain.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- SELECTED REPRESENTATIVE FINITE TRACE
-- ============================================================

/-- Translate the A1.3 endpoint-coordinate carrier into the A1.5 finite
    boundary-coordinate carrier. -/
def
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryCoord.ofA13
    (x : G8BookIIICh23FloorNormalizedA13EndpointCoord) :
    G8BookIIICh23FloorNormalizedA15BoundaryTrace.Coord where
  b0 := x.b0
  b1 := x.b1
  c0 := x.c0
  c1 := x.c1

/-- The A1.3 endpoint-value balance is the A1.5 finite boundary-value
    balance after coordinate translation. -/
theorem
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryCoord.ofA13_balanced
    {x : G8BookIIICh23FloorNormalizedA13EndpointCoord}
    (hx : G8BookIIICh23FloorNormalizedA13EndpointCoord.balanced x) :
    G8BookIIICh23FloorNormalizedA15BoundaryTrace.Coord.balanced
      (G8BookIIICh23FloorNormalizedA15FiniteBoundaryCoord.ofA13 x) := by
  rcases hx with ⟨h01, h0c0, h0c1⟩
  exact ⟨h01, h0c0, h0c1⟩

/-- The A1.3 outgoing-derivative balance is the A1.5 finite derivative
    balance after coordinate translation. -/
theorem
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryCoord.ofA13_sum
    {x : G8BookIIICh23FloorNormalizedA13EndpointCoord}
    (hx : G8BookIIICh23FloorNormalizedA13EndpointCoord.sum x = 0) :
    G8BookIIICh23FloorNormalizedA15BoundaryTrace.Coord.sum
      (G8BookIIICh23FloorNormalizedA15FiniteBoundaryCoord.ofA13 x) = 0 := by
  simpa [
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryCoord.ofA13,
    G8BookIIICh23FloorNormalizedA15BoundaryTrace.Coord.sum,
    G8BookIIICh23FloorNormalizedA13EndpointCoord.sum
  ] using hx

/-- The finite endpoint trace read from a selected Kirchhoff-domain
    representative. -/
def
    G8BookIIICh23FloorNormalizedA15SelectedEndpointFiniteTrace
    (u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace where
  value :=
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryCoord.ofA13
      u.endpointValue
  deriv :=
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryCoord.ofA13
      u.outgoingDerivative

/-- A selected representative has a Kirchhoff finite endpoint trace by the
    endpoint laws carried in the selected A1.3 operator domain. -/
theorem
    G8BookIIICh23FloorNormalizedA15SelectedEndpointFiniteTrace_kirchhoff
    (u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.Kirchhoff
      (G8BookIIICh23FloorNormalizedA15SelectedEndpointFiniteTrace u) :=
  ⟨G8BookIIICh23FloorNormalizedA15FiniteBoundaryCoord.ofA13_balanced
      u.endpointValueBalanced,
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryCoord.ofA13_sum
      u.outgoingDerivativeBalanced⟩

/-- A selected representative's finite endpoint trace annihilates all
    Kirchhoff test traces. -/
theorem
    G8BookIIICh23FloorNormalizedA15SelectedEndpointFiniteTrace_annihilatesKirchhoff
    (u : G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain) :
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
      (G8BookIIICh23FloorNormalizedA15SelectedEndpointFiniteTrace u) :=
  G8BookIIICh23FloorNormalizedA15BoundaryTrace.annihilatesKirchhoff_of_kirchhoff
    (G8BookIIICh23FloorNormalizedA15SelectedEndpointFiniteTrace_kirchhoff u)

-- ============================================================
-- FULL ENGINE READOUT
-- ============================================================

/-- The concrete engine reads finite traces from the selected representative
    used for each adjoint candidate. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.boundaryTrace
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource)
    (candidate : engine.candidates.point) :
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace :=
  G8BookIIICh23FloorNormalizedA15SelectedEndpointFiniteTrace
    (engine.candidates.realize candidate)

/-- The engine finite-trace readout annihilates every Kirchhoff finite test
    trace. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.boundaryTrace_annihilatesKirchhoff
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource)
    (candidate : engine.candidates.point) :
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
      (engine.boundaryTrace candidate) :=
  G8BookIIICh23FloorNormalizedA15SelectedEndpointFiniteTrace_annihilatesKirchhoff
    (engine.candidates.realize candidate)

/-- The engine also carries the full Green-pairing law against the complete
    Kirchhoff test presentation.  This predicate records that the finite trace
    readout is paired with the non-diagnostic all-tests Green source, not just
    a finite boundary calculation. -/
def
    G8BookIIICh23FloorNormalizedA15EngineFiniteTraceUsesFullGreenPairing
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource) :
    Prop :=
  ∀ (candidate : engine.candidates.point) (test : engine.tests.point),
    (engine.toCompactGraphAdjointCalculusSource).annihilatesKirchhoffBoundaryForm
      candidate test

/-- The full Green-pairing provenance is closed for an engine source because
    the compact-graph calculus source was built with all selected Kirchhoff
    tests as its test universe. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.fullGreenPairing
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource) :
    G8BookIIICh23FloorNormalizedA15EngineFiniteTraceUsesFullGreenPairing
      engine := by
  intro candidate test
  exact
    (engine.toCompactGraphAdjointCalculusSource)
      |>.annihilatesKirchhoffBoundaryFormWitness candidate test

/-- A concrete A1.5 engine source supplies the compact-graph finite-trace
    readout source. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.toCompactGraphFiniteTraceReadoutSource
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource) :
    G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutSource where
  calculus := engine.toCompactGraphAdjointCalculusSource
  boundaryTrace := engine.boundaryTrace
  finiteTraceAnnihilatesKirchhoff :=
    engine.boundaryTrace_annihilatesKirchhoff
  boundaryTraceExtractsRecoveredTrace :=
    ∀ candidate : engine.candidates.point,
      (engine.toCompactGraphAdjointCalculusSource)
        |>.valueAndDerivativeBoundaryTracesExist candidate
  boundaryTraceExtractsRecoveredTraceWitness :=
    (engine.toCompactGraphAdjointCalculusSource)
      |>.valueAndDerivativeBoundaryTracesExistWitness
  boundaryTraceGreenPairingRealizesAnnihilator :=
    G8BookIIICh23FloorNormalizedA15EngineFiniteTraceUsesFullGreenPairing
      engine
  boundaryTraceGreenPairingRealizesAnnihilatorWitness :=
    engine.fullGreenPairing
  finiteTraceReadoutIsGlobal :=
    engine.candidates.representsFullAdjointDomain ∧
      engine.tests.exhaustsSelectedKirchhoffDomain
  finiteTraceReadoutIsGlobalWitness :=
    ⟨engine.candidates.representsFullAdjointDomainWitness,
      engine.tests.exhaustsSelectedKirchhoffDomainWitness⟩
  finiteTraceReadoutUsesAllKirchhoffTests :=
    engine.tests.exhaustsSelectedKirchhoffDomain ∧
      engine.tests.noFiniteDiagnosticSubstitute
  finiteTraceReadoutUsesAllKirchhoffTestsWitness :=
    ⟨engine.tests.exhaustsSelectedKirchhoffDomainWitness,
      engine.tests.noFiniteDiagnosticSubstituteWitness⟩
  status := .conditional_interface

/-- A concrete A1.5 engine source discharges the compact-graph finite trace
    readout target. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource.toCompactGraphFiniteTraceReadoutTarget
    (engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource) :
    G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutTarget :=
  ⟨engine.toCompactGraphFiniteTraceReadoutSource⟩

/-- Target-level adapter from the concrete engine to the compact-graph finite
    trace readout target. -/
theorem
    g8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutTarget_ofEngine
    (target : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget) :
    G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutTarget :=
  target.elim fun engine =>
    engine.toCompactGraphFiniteTraceReadoutTarget

/-- A concrete engine is now sufficient for the selected-carrier A1.5 maximal
    Kirchhoff self-adjoint extension target through the endpoint trace
    readout. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofEngine_viaEndpointTrace
    (target : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofCompactGraphFiniteTraceReadout
    (g8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutTarget_ofEngine
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Without the endpoint trace carried by the selected representative, the
    engine-level finite readout cannot be constructed by this route. -/
structure
    G8BookIIICh23FloorNormalizedA15SelectedEndpointTraceMissing
    where
  engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource
  noReadout :
    ¬ G8BookIIICh23FloorNormalizedA15CompactGraphFiniteTraceReadoutTarget

theorem
    G8BookIIICh23FloorNormalizedA15SelectedEndpointTraceMissing.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15SelectedEndpointTraceMissing) :
    False :=
  gap.noReadout
    gap.engine.toCompactGraphFiniteTraceReadoutTarget

/-- A selected endpoint trace whose value/derivative laws fail cannot be
    treated as a Kirchhoff finite trace. -/
structure
    G8BookIIICh23FloorNormalizedA15SelectedEndpointTraceLawFailure
    where
  selected :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain
  notKirchhoff :
    ¬ G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.Kirchhoff
      (G8BookIIICh23FloorNormalizedA15SelectedEndpointFiniteTrace selected)

theorem
    G8BookIIICh23FloorNormalizedA15SelectedEndpointTraceLawFailure.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15SelectedEndpointTraceLawFailure) :
    False :=
  gap.notKirchhoff
    (G8BookIIICh23FloorNormalizedA15SelectedEndpointFiniteTrace_kirchhoff
      gap.selected)

/-- Finite endpoint algebra alone is not recorded as the whole story: the
    engine source must still carry all Kirchhoff tests through the Green
    pairing provenance. -/
structure
    G8BookIIICh23FloorNormalizedA15EndpointTraceWithoutFullGreenPairing
    where
  engine : G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineSource
  missingFullGreenPairing :
    ¬ G8BookIIICh23FloorNormalizedA15EngineFiniteTraceUsesFullGreenPairing
      engine

theorem
    G8BookIIICh23FloorNormalizedA15EndpointTraceWithoutFullGreenPairing.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15EndpointTraceWithoutFullGreenPairing) :
    False :=
  gap.missingFullGreenPairing gap.engine.fullGreenPairing

end Tau.BookIII.Bridge
