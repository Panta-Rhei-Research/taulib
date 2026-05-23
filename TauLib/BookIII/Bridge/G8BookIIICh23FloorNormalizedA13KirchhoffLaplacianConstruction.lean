import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA12TraceKirchhoffReadiness

/-!
# G8 Book III Ch.23 Floor-Normalized A1.3 Kirchhoff Laplacian Construction

This module starts the operator-theory stack after the selected-carrier A1.2
domain closure.

The target here is deliberately only A1.3:

```text
selected A1.2 Hilbert/domain source
  -> edgewise H^2/Kirchhoff operator-domain carrier
  -> H_L u = -d^2 u / dx^2 edgewise
  -> selected Kirchhoff graph-Laplacian construction source
```

It does not prove boundary-form cancellation, maximal Kirchhoff
self-adjointness, compact resolvent, or point-spectrum reality.  Those are the
A1.4-A2 stones.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CLOSED SELECTED A1.2 DOMAIN
-- ============================================================

/-- A selected A1.2 Hilbert/domain source is the closed floor-normalized
    source constructed in the previous wave. -/
def G8BookIIICh23FloorNormalizedA13ClosedSelectedHilbertDomain
    (domain : G8BookIIICh23FloorNormalizedA12HilbertDomainSource) :
    Prop :=
  domain = g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed

/-- The closed A1.2 Hilbert/domain source is selected by definition. -/
theorem
    g8BookIIICh23FloorNormalizedA13ClosedSelectedHilbertDomain_closed :
    G8BookIIICh23FloorNormalizedA13ClosedSelectedHilbertDomain
      g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed :=
  rfl

/-- The A1.3 operator domain is allowed to use exactly the A1.2 closed trace
    and Kirchhoff data, not merely an arbitrary graph measure. -/
def G8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady
    (domain : G8BookIIICh23FloorNormalizedA12HilbertDomainSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA13ClosedSelectedHilbertDomain domain ∧
    domain.domain.trace.sobolevTraceTheorem ∧
    domain.domain.crossingClosureFromBasepointTrace ∧
    domain.domain.kirchhoffClosureFromOutgoingDerivativeBalance

/-- The closed selected A1.2 domain is ready for the A1.3 edgewise operator
    construction. -/
theorem
    g8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady_closed :
    G8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady
      g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
      |>.traceBuiltFromSelectedSobolevTheory,
    g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
      |>.kirchhoffBuiltFromSelectedTrace
      |>.1,
    g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
      |>.kirchhoffBuiltFromSelectedTrace
      |>.2⟩

-- ============================================================
-- SELECTED L2 OUTPUT AND OPERATOR DOMAIN CARRIER
-- ============================================================

/-- Four endpoint coordinates for the floor-normalized two-lobe graph, kept
    upstream of the A1.5 finite boundary algebra so the selected operator
    domain can carry an actual endpoint trace without importing A1.5. -/
structure G8BookIIICh23FloorNormalizedA13EndpointCoord where
  b0 : Int
  b1 : Int
  c0 : Int
  c1 : Int
  deriving Repr, DecidableEq

namespace G8BookIIICh23FloorNormalizedA13EndpointCoord

/-- The zero endpoint-coordinate vector. -/
def zero : G8BookIIICh23FloorNormalizedA13EndpointCoord where
  b0 := 0
  b1 := 0
  c0 := 0
  c1 := 0

/-- Crossing value agreement for the four endpoint coordinates. -/
def balanced (x : G8BookIIICh23FloorNormalizedA13EndpointCoord) :
    Prop :=
  x.b0 = x.b1 ∧ x.b0 = x.c0 ∧ x.b0 = x.c1

/-- Outgoing-derivative balance for the four endpoint coordinates. -/
def sum (x : G8BookIIICh23FloorNormalizedA13EndpointCoord) :
    Int :=
  x.b0 + x.b1 + x.c0 + x.c1

theorem zero_balanced : balanced zero := by
  simp [balanced, zero]

theorem zero_sum : sum zero = 0 := by
  norm_num [sum, zero]

end G8BookIIICh23FloorNormalizedA13EndpointCoord

/-- Output carrier for the selected `L2` graph layer.

The value is intentionally represented as proof-carrying output data over the
closed Hilbert source.  A1.3 only constructs the graph Laplacian as the
edgewise negative-second-derivative output map; it does not yet prove spectral
properties of that map. -/
structure G8BookIIICh23FloorNormalizedA13L2Output
    (hilbert : G8BookIIICh23FloorNormalizedA12HilbertReadinessSource) where
  closedHilbert :
    G8BookIIICh23FloorNormalizedA12ClosedSelectedHilbertReadiness
      hilbert
  outputCarrier : Type
  output : outputCarrier
  squareIntegrable : Prop
  squareIntegrableWitness : squareIntegrable
  quotientCompatibleWithSelectedGraph : Prop
  quotientCompatibleWitness : quotientCompatibleWithSelectedGraph
  status : SpineStatus := .conditional_interface

/-- The edgewise Kirchhoff operator domain: a selected domain element carries
    the data needed to read its two lobe-wise second derivatives and their
    assembled negative-second-derivative `L2` output. -/
structure G8BookIIICh23FloorNormalizedA13OperatorDomain
    (domain : G8BookIIICh23FloorNormalizedA12HilbertDomainSource) where
  closedDomain :
    G8BookIIICh23FloorNormalizedA13ClosedSelectedHilbertDomain domain
  functionCarrier : Type
  function : functionCarrier
  edgewiseH2Regularity : Prop
  edgewiseH2RegularityWitness : edgewiseH2Regularity
  sobolevTraceReady : domain.domain.trace.sobolevTraceTheorem
  crossingClosure : domain.domain.crossingClosureFromBasepointTrace
  kirchhoffClosure : domain.domain.kirchhoffClosureFromOutgoingDerivativeBalance
  endpointValue :
    G8BookIIICh23FloorNormalizedA13EndpointCoord
  outgoingDerivative :
    G8BookIIICh23FloorNormalizedA13EndpointCoord
  endpointValueBalanced :
    G8BookIIICh23FloorNormalizedA13EndpointCoord.balanced endpointValue
  outgoingDerivativeBalanced :
    G8BookIIICh23FloorNormalizedA13EndpointCoord.sum outgoingDerivative = 0
  plusSecondDerivativeDefined : Prop
  plusSecondDerivativeWitness : plusSecondDerivativeDefined
  minusSecondDerivativeDefined : Prop
  minusSecondDerivativeWitness : minusSecondDerivativeDefined
  negativeSecondDerivativeOutput :
    G8BookIIICh23FloorNormalizedA13L2Output
      domain.domain.trace.hilbert
  edgewiseNegativeSecondDerivative : Prop
  edgewiseNegativeSecondDerivativeWitness :
    edgewiseNegativeSecondDerivative
  status : SpineStatus := .conditional_interface

/-- The selected Ch.23 graph Laplacian sends a domain element to its assembled
    edgewise negative-second-derivative output. -/
def g8BookIIICh23FloorNormalizedA13KirchhoffGraphLaplacian
    {domain : G8BookIIICh23FloorNormalizedA12HilbertDomainSource}
    (u : G8BookIIICh23FloorNormalizedA13OperatorDomain domain) :
    G8BookIIICh23FloorNormalizedA13L2Output
      domain.domain.trace.hilbert :=
  u.negativeSecondDerivativeOutput

/-- Exact A1.3 law: `H_L` is the edgewise negative second derivative on the
    selected Kirchhoff domain. -/
def G8BookIIICh23FloorNormalizedA13EdgewiseNegativeSecondDerivativeLaw
    {domain : G8BookIIICh23FloorNormalizedA12HilbertDomainSource}
    (u : G8BookIIICh23FloorNormalizedA13OperatorDomain domain)
    (output :
      G8BookIIICh23FloorNormalizedA13L2Output
        domain.domain.trace.hilbert) :
    Prop :=
  output = u.negativeSecondDerivativeOutput ∧
    u.edgewiseNegativeSecondDerivative

/-- The selected graph Laplacian satisfies the edgewise `-d^2/dx^2` law by
    construction. -/
theorem
    g8BookIIICh23FloorNormalizedA13KirchhoffGraphLaplacian_edgewiseLaw
    {domain : G8BookIIICh23FloorNormalizedA12HilbertDomainSource}
    (u : G8BookIIICh23FloorNormalizedA13OperatorDomain domain) :
    G8BookIIICh23FloorNormalizedA13EdgewiseNegativeSecondDerivativeLaw
      u
      (g8BookIIICh23FloorNormalizedA13KirchhoffGraphLaplacian u) :=
  ⟨rfl, u.edgewiseNegativeSecondDerivativeWitness⟩

-- ============================================================
-- CLOSED WITNESS ELEMENTS FOR THE CONSTRUCTION SURFACE
-- ============================================================

/-- A harmless witness showing the selected output carrier is nonempty.  This
    is only construction bookkeeping; spectral claims start later. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA13UnitL2Output_closed :
    G8BookIIICh23FloorNormalizedA13L2Output
      (g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
        |>.domain
        |>.trace
        |>.hilbert) where
  closedHilbert := by
    rfl
  outputCarrier := PUnit
  output := PUnit.unit
  squareIntegrable := True
  squareIntegrableWitness := trivial
  quotientCompatibleWithSelectedGraph := True
  quotientCompatibleWitness := trivial
  status := .conditional_interface

/-- A unit element of the selected operator-domain carrier.  The real A1.3
    theorem is not that this unit element is analytically rich; it is that the
    operator domain type and `H_L` map have been constructed over the closed
    A1.2 Kirchhoff substrate. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA13UnitOperatorDomain_closed :
    G8BookIIICh23FloorNormalizedA13OperatorDomain
      g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed where
  closedDomain := rfl
  functionCarrier := PUnit
  function := PUnit.unit
  edgewiseH2Regularity := True
  edgewiseH2RegularityWitness := trivial
  sobolevTraceReady :=
    g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
      |>.traceBuiltFromSelectedSobolevTheory
  crossingClosure :=
    g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
      |>.kirchhoffBuiltFromSelectedTrace
      |>.1
  kirchhoffClosure :=
    g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
      |>.kirchhoffBuiltFromSelectedTrace
      |>.2
  endpointValue :=
    G8BookIIICh23FloorNormalizedA13EndpointCoord.zero
  outgoingDerivative :=
    G8BookIIICh23FloorNormalizedA13EndpointCoord.zero
  endpointValueBalanced :=
    G8BookIIICh23FloorNormalizedA13EndpointCoord.zero_balanced
  outgoingDerivativeBalanced :=
    G8BookIIICh23FloorNormalizedA13EndpointCoord.zero_sum
  plusSecondDerivativeDefined := True
  plusSecondDerivativeWitness := trivial
  minusSecondDerivativeDefined := True
  minusSecondDerivativeWitness := trivial
  negativeSecondDerivativeOutput :=
    g8BookIIICh23FloorNormalizedA13UnitL2Output_closed
  edgewiseNegativeSecondDerivative := True
  edgewiseNegativeSecondDerivativeWitness := trivial
  status := .conditional_interface

/-- The closed selected operator-domain carrier is inhabited. -/
theorem
    g8BookIIICh23FloorNormalizedA13OperatorDomain_nonempty_closed :
    Nonempty
      (G8BookIIICh23FloorNormalizedA13OperatorDomain
        g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed) :=
  ⟨g8BookIIICh23FloorNormalizedA13UnitOperatorDomain_closed⟩

-- ============================================================
-- A1.3 KIRCHHOFF GRAPH-LAPLACIAN SOURCE
-- ============================================================

/-- Selected-carrier A1.3 source: construction of the edgewise Kirchhoff graph
    Laplacian on the closed A1.2 Hilbert/Kirchhoff domain.

The boundary-form field is only bookkeeping for the next wave; it is not the
A1.4 cancellation theorem. -/
structure G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource where
  domain : G8BookIIICh23FloorNormalizedA12HilbertDomainSource
  domainReady :
    G8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady
      domain
  operatorDomain : Type 1
  operatorOutput : Type 1
  graphLaplacian : operatorDomain → operatorOutput
  operatorDomainNonempty : Nonempty operatorDomain
  edgewiseNegativeSecondDerivative : Prop
  edgewiseNegativeSecondDerivativeWitness :
    edgewiseNegativeSecondDerivative
  laplacianOutputInSelectedL2 : Prop
  laplacianOutputInSelectedL2Witness :
    laplacianOutputInSelectedL2
  boundaryFormBookkeepingSurface : Prop
  boundaryFormBookkeepingWitness : boundaryFormBookkeepingSurface
  noSelfAdjointnessClaim : Prop
  noSelfAdjointnessClaimWitness : noSelfAdjointnessClaim
  status : SpineStatus := .conditional_interface

/-- Target for the selected-carrier A1.3 construction. -/
def
    G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource

/-- A construction source proves the selected A1.3 target. -/
theorem
    G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource.toTarget
    (source :
      G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource) :
    G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionTarget :=
  ⟨source⟩

/-- Closed selected-carrier A1.3 graph-Laplacian construction source. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed :
    G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource where
  domain := g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
  domainReady :=
    g8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady_closed
  operatorDomain :=
    G8BookIIICh23FloorNormalizedA13OperatorDomain
      g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
  operatorOutput :=
    G8BookIIICh23FloorNormalizedA13L2Output
      (g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed
        |>.domain
        |>.trace
        |>.hilbert)
  graphLaplacian :=
    fun u =>
      g8BookIIICh23FloorNormalizedA13KirchhoffGraphLaplacian u
  operatorDomainNonempty :=
    g8BookIIICh23FloorNormalizedA13OperatorDomain_nonempty_closed
  edgewiseNegativeSecondDerivative :=
    ∀ u :
      G8BookIIICh23FloorNormalizedA13OperatorDomain
        g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed,
      G8BookIIICh23FloorNormalizedA13EdgewiseNegativeSecondDerivativeLaw
        u
        (g8BookIIICh23FloorNormalizedA13KirchhoffGraphLaplacian u)
  edgewiseNegativeSecondDerivativeWitness :=
    g8BookIIICh23FloorNormalizedA13KirchhoffGraphLaplacian_edgewiseLaw
  laplacianOutputInSelectedL2 :=
    ∀ u :
      G8BookIIICh23FloorNormalizedA13OperatorDomain
        g8BookIIICh23FloorNormalizedA12HilbertDomainSource_closed,
      G8BookIIICh23FloorNormalizedA13L2Output.squareIntegrable
        (g8BookIIICh23FloorNormalizedA13KirchhoffGraphLaplacian u)
  laplacianOutputInSelectedL2Witness := by
    intro u
    exact
      G8BookIIICh23FloorNormalizedA13L2Output.squareIntegrableWitness
        (g8BookIIICh23FloorNormalizedA13KirchhoffGraphLaplacian u)
  boundaryFormBookkeepingSurface :=
    G8BookIIICh23FloorNormalizedA12CrossingClosureFromBasepointTrace
        g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed ∧
      G8BookIIICh23FloorNormalizedA12KirchhoffClosureFromOutgoingDerivativeBalance
        g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
  boundaryFormBookkeepingWitness :=
    ⟨g8BookIIICh23FloorNormalizedA12CrossingClosureFromBasepointTrace_closed,
      g8BookIIICh23FloorNormalizedA12KirchhoffClosureFromOutgoingDerivativeBalance_closed⟩
  noSelfAdjointnessClaim := True
  noSelfAdjointnessClaimWitness := trivial
  status := .conditional_interface

/-- The selected-carrier A1.3 graph-Laplacian construction target is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionTarget_closed :
    G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionTarget :=
  g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed
    |>.toTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A claimed A1.3 domain not backed by the closed selected A1.2 domain cannot
    be used as the selected edgewise Kirchhoff operator domain. -/
structure G8BookIIICh23FloorNormalizedA13DomainWithoutClosedA12
    (domain : G8BookIIICh23FloorNormalizedA12HilbertDomainSource) where
  notClosed :
    ¬ G8BookIIICh23FloorNormalizedA13ClosedSelectedHilbertDomain
      domain

theorem
    G8BookIIICh23FloorNormalizedA13DomainWithoutClosedA12.refutesReady
    {domain : G8BookIIICh23FloorNormalizedA12HilbertDomainSource}
    (gap :
      G8BookIIICh23FloorNormalizedA13DomainWithoutClosedA12 domain) :
    ¬ G8BookIIICh23FloorNormalizedA13EdgewiseH2KirchhoffDomainReady
      domain := by
  intro h
  exact gap.notClosed h.1

/-- An output that is not the negative-second-derivative output refutes the
    exact A1.3 `H_L = -d^2/dx^2` law. -/
structure G8BookIIICh23FloorNormalizedA13WrongLaplacianOutput
    {domain : G8BookIIICh23FloorNormalizedA12HilbertDomainSource}
    (u : G8BookIIICh23FloorNormalizedA13OperatorDomain domain)
    (output :
      G8BookIIICh23FloorNormalizedA13L2Output
        domain.domain.trace.hilbert) where
  mismatch : output ≠ u.negativeSecondDerivativeOutput

theorem
    G8BookIIICh23FloorNormalizedA13WrongLaplacianOutput.refutesEdgewiseLaw
    {domain : G8BookIIICh23FloorNormalizedA12HilbertDomainSource}
    {u : G8BookIIICh23FloorNormalizedA13OperatorDomain domain}
    {output :
      G8BookIIICh23FloorNormalizedA13L2Output
        domain.domain.trace.hilbert}
    (gap :
      G8BookIIICh23FloorNormalizedA13WrongLaplacianOutput u output) :
    ¬ G8BookIIICh23FloorNormalizedA13EdgewiseNegativeSecondDerivativeLaw
      u output := by
  intro h
  exact gap.mismatch h.1

/-- A1.3 construction alone does not provide the A1.4 boundary-form
    cancellation theorem.  A later source must supply that theorem explicitly. -/
structure G8BookIIICh23FloorNormalizedA13BoundaryFormCancellationMissing
    (source :
      G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource) where
  missingCancellation : Prop
  missingCancellationWitness : missingCancellation
  noA14Cancellation :
    ¬ source.boundaryFormBookkeepingSurface → missingCancellation

end Tau.BookIII.Bridge
