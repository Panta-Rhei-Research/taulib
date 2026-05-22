import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstruction

/-!
# G8 Book III Ch.23 Floor-Normalized A1.4 Boundary-Form Cancellation

This module closes the selected-carrier A1.4 symmetry stone after the A1.3
Kirchhoff graph-Laplacian construction.

The target here is deliberately only boundary-form cancellation:

```text
selected A1.3 graph Laplacian
  -> edgewise Green/boundary bookkeeping
  -> crossing value-trace cancellation
  -> outgoing derivative-balance cancellation
  -> Kirchhoff boundary form cancels
```

It does not prove maximality of the Kirchhoff extension, self-adjointness,
compact resolvent, or point-spectrum reality.  Those remain the A1.5-A2
operator-theory stones.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CLOSED SELECTED A1.3 SOURCE
-- ============================================================

/-- A selected A1.3 graph-Laplacian source is the closed source constructed in
    the previous wave. -/
def G8BookIIICh23FloorNormalizedA14ClosedSelectedA13Laplacian
    (source :
      G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource) :
    Prop :=
  source =
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed

/-- The closed A1.3 graph-Laplacian source is selected by definition. -/
theorem
    g8BookIIICh23FloorNormalizedA14ClosedSelectedA13Laplacian_closed :
    G8BookIIICh23FloorNormalizedA14ClosedSelectedA13Laplacian
      g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed :=
  rfl

-- ============================================================
-- GREEN BOOKKEEPING AND ENDPOINT CANCELLATION INPUTS
-- ============================================================

/-- Edgewise Green bookkeeping available from A1.3: the operator is the
    assembled edgewise negative-second-derivative output and lands in the
    selected `L2` output carrier. -/
def G8BookIIICh23FloorNormalizedA14EdgewiseGreenBookkeeping
    (source :
      G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA14ClosedSelectedA13Laplacian source ∧
    source.edgewiseNegativeSecondDerivative ∧
    source.laplacianOutputInSelectedL2

/-- The closed A1.3 source supplies the edgewise Green bookkeeping input. -/
theorem
    g8BookIIICh23FloorNormalizedA14EdgewiseGreenBookkeeping_closed :
    G8BookIIICh23FloorNormalizedA14EdgewiseGreenBookkeeping
      g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed
      |>.edgewiseNegativeSecondDerivativeWitness,
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed
      |>.laplacianOutputInSelectedL2Witness⟩

/-- Value-trace endpoint cancellation at the crossing: the two lobe endpoint
    values are identified by the selected basepoint trace closure. -/
def G8BookIIICh23FloorNormalizedA14CrossingValueTraceCancellation
    (source :
      G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA14ClosedSelectedA13Laplacian source ∧
    source.domain.domain.crossingAgreementClosed ∧
    source.domain.domain.crossingClosureFromBasepointTrace

/-- The closed A1.3 source supplies crossing value-trace cancellation. -/
theorem
    g8BookIIICh23FloorNormalizedA14CrossingValueTraceCancellation_closed :
    G8BookIIICh23FloorNormalizedA14CrossingValueTraceCancellation
      g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed
      |>.domain
      |>.domain
      |>.crossingAgreementClosedWitness,
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed
      |>.domain
      |>.domain
      |>.crossingClosureFromBasepointTraceWitness⟩

/-- Outgoing derivative-balance cancellation at the crossing: the selected
    derivative trace law closes the Kirchhoff flux balance. -/
def G8BookIIICh23FloorNormalizedA14OutgoingDerivativeCancellation
    (source :
      G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA14ClosedSelectedA13Laplacian source ∧
    source.domain.domain.kirchhoffConditionClosed ∧
    source.domain.domain.kirchhoffClosureFromOutgoingDerivativeBalance

/-- The closed A1.3 source supplies outgoing derivative-balance cancellation. -/
theorem
    g8BookIIICh23FloorNormalizedA14OutgoingDerivativeCancellation_closed :
    G8BookIIICh23FloorNormalizedA14OutgoingDerivativeCancellation
      g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed :=
  ⟨rfl,
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed
      |>.domain
      |>.domain
      |>.kirchhoffConditionClosedWitness,
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed
      |>.domain
      |>.domain
      |>.kirchhoffClosureFromOutgoingDerivativeBalanceWitness⟩

/-- The full endpoint cancellation input: A1.3 boundary bookkeeping plus the
    selected value and derivative endpoint cancellation laws from A1.2. -/
def G8BookIIICh23FloorNormalizedA14EndpointCancellationInput
    (source :
      G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource) :
    Prop :=
  source.boundaryFormBookkeepingSurface ∧
    G8BookIIICh23FloorNormalizedA14CrossingValueTraceCancellation
      source ∧
    G8BookIIICh23FloorNormalizedA14OutgoingDerivativeCancellation
      source

/-- The closed A1.3 source supplies the full endpoint cancellation input. -/
theorem
    g8BookIIICh23FloorNormalizedA14EndpointCancellationInput_closed :
    G8BookIIICh23FloorNormalizedA14EndpointCancellationInput
      g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed :=
  ⟨g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed
      |>.boundaryFormBookkeepingWitness,
    g8BookIIICh23FloorNormalizedA14CrossingValueTraceCancellation_closed,
    g8BookIIICh23FloorNormalizedA14OutgoingDerivativeCancellation_closed⟩

-- ============================================================
-- A1.4 BOUNDARY-FORM CANCELLATION
-- ============================================================

/-- Selected-carrier A1.4 boundary-form cancellation.

This is the symmetry stone: the two lobe integration-by-parts boundary
contributions cancel after the crossing value traces are identified and the
outgoing derivative traces satisfy Kirchhoff balance. -/
def G8BookIIICh23FloorNormalizedA14BoundaryFormCancellation
    (source :
      G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA14EdgewiseGreenBookkeeping
      source ∧
    G8BookIIICh23FloorNormalizedA14EndpointCancellationInput
      source

/-- The closed selected A1.3 source has Kirchhoff boundary-form cancellation. -/
theorem
    g8BookIIICh23FloorNormalizedA14BoundaryFormCancellation_closed :
    G8BookIIICh23FloorNormalizedA14BoundaryFormCancellation
      g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed :=
  ⟨g8BookIIICh23FloorNormalizedA14EdgewiseGreenBookkeeping_closed,
    g8BookIIICh23FloorNormalizedA14EndpointCancellationInput_closed⟩

/-- Selected A1.4 symmetry law: A1.4 proves cancellation of the boundary form,
    but still does not prove maximality/self-adjointness. -/
def G8BookIIICh23FloorNormalizedA14KirchhoffSymmetryLaw
    (source :
      G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA14BoundaryFormCancellation source ∧
    source.noSelfAdjointnessClaim

/-- The closed selected A1.3 source satisfies the A1.4 Kirchhoff symmetry
    law. -/
theorem
    g8BookIIICh23FloorNormalizedA14KirchhoffSymmetryLaw_closed :
    G8BookIIICh23FloorNormalizedA14KirchhoffSymmetryLaw
      g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed :=
  ⟨g8BookIIICh23FloorNormalizedA14BoundaryFormCancellation_closed,
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed
      |>.noSelfAdjointnessClaimWitness⟩

-- ============================================================
-- A1.4 SOURCE
-- ============================================================

/-- Selected-carrier A1.4 source: boundary-form cancellation for the
    Kirchhoff graph Laplacian constructed in A1.3.

The final field intentionally records that maximality remains a later A1.5
payload. -/
structure G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource where
  laplacianSource :
    G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource
  closedLaplacianSource :
    G8BookIIICh23FloorNormalizedA14ClosedSelectedA13Laplacian
      laplacianSource
  edgewiseGreenBookkeeping :
    G8BookIIICh23FloorNormalizedA14EdgewiseGreenBookkeeping
      laplacianSource
  crossingValueTraceCancellation :
    G8BookIIICh23FloorNormalizedA14CrossingValueTraceCancellation
      laplacianSource
  outgoingDerivativeCancellation :
    G8BookIIICh23FloorNormalizedA14OutgoingDerivativeCancellation
      laplacianSource
  endpointCancellationInput :
    G8BookIIICh23FloorNormalizedA14EndpointCancellationInput
      laplacianSource
  boundaryFormCancellation :
    G8BookIIICh23FloorNormalizedA14BoundaryFormCancellation
      laplacianSource
  kirchhoffSymmetryLaw :
    G8BookIIICh23FloorNormalizedA14KirchhoffSymmetryLaw
      laplacianSource
  maximalityNotClaimed : Prop
  maximalityNotClaimedWitness : maximalityNotClaimed
  status : SpineStatus := .conditional_interface

/-- Target for the selected-carrier A1.4 boundary-form cancellation theorem. -/
def G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource

/-- An A1.4 source proves the selected A1.4 target. -/
theorem
    G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource.toTarget
    (source :
      G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource) :
    G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationTarget :=
  ⟨source⟩

/-- Closed selected-carrier A1.4 boundary-form cancellation source. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed :
    G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource where
  laplacianSource :=
    g8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource_closed
  closedLaplacianSource :=
    g8BookIIICh23FloorNormalizedA14ClosedSelectedA13Laplacian_closed
  edgewiseGreenBookkeeping :=
    g8BookIIICh23FloorNormalizedA14EdgewiseGreenBookkeeping_closed
  crossingValueTraceCancellation :=
    g8BookIIICh23FloorNormalizedA14CrossingValueTraceCancellation_closed
  outgoingDerivativeCancellation :=
    g8BookIIICh23FloorNormalizedA14OutgoingDerivativeCancellation_closed
  endpointCancellationInput :=
    g8BookIIICh23FloorNormalizedA14EndpointCancellationInput_closed
  boundaryFormCancellation :=
    g8BookIIICh23FloorNormalizedA14BoundaryFormCancellation_closed
  kirchhoffSymmetryLaw :=
    g8BookIIICh23FloorNormalizedA14KirchhoffSymmetryLaw_closed
  maximalityNotClaimed := True
  maximalityNotClaimedWitness := trivial
  status := .conditional_interface

/-- The selected-carrier A1.4 boundary-form cancellation target is closed. -/
theorem
    g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationTarget_closed :
    G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationTarget :=
  g8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource_closed
    |>.toTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Without edgewise Green bookkeeping, the A1.4 boundary cancellation theorem
    cannot be formed. -/
structure G8BookIIICh23FloorNormalizedA14MissingGreenBookkeeping
    (source :
      G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource) where
  missing :
    ¬ G8BookIIICh23FloorNormalizedA14EdgewiseGreenBookkeeping source

theorem
    G8BookIIICh23FloorNormalizedA14MissingGreenBookkeeping.refutesCancellation
    {source :
      G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource}
    (gap :
      G8BookIIICh23FloorNormalizedA14MissingGreenBookkeeping source) :
    ¬ G8BookIIICh23FloorNormalizedA14BoundaryFormCancellation source := by
  intro h
  exact gap.missing h.1

/-- Without endpoint cancellation, the A1.4 boundary cancellation theorem
    cannot be formed. -/
structure G8BookIIICh23FloorNormalizedA14MissingEndpointCancellation
    (source :
      G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource) where
  missing :
    ¬ G8BookIIICh23FloorNormalizedA14EndpointCancellationInput source

theorem
    G8BookIIICh23FloorNormalizedA14MissingEndpointCancellation.refutesCancellation
    {source :
      G8BookIIICh23FloorNormalizedA13KirchhoffLaplacianConstructionSource}
    (gap :
      G8BookIIICh23FloorNormalizedA14MissingEndpointCancellation source) :
    ¬ G8BookIIICh23FloorNormalizedA14BoundaryFormCancellation source := by
  intro h
  exact gap.missing h.2

/-- A boundary-form cancellation source is still not a maximal
    self-adjointness source.  A1.5 must supply maximality explicitly. -/
structure G8BookIIICh23FloorNormalizedA14CancellationWithoutMaximality where
  cancellationSource :
    G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource
  maximalityPayloadStillOpen : Prop
  maximalityPayloadStillOpenWitness : maximalityPayloadStillOpen

/-- Claiming self-adjoint maximality directly from A1.4 is refuted whenever a
    separate maximality gap is supplied. -/
structure G8BookIIICh23FloorNormalizedA14PrematureMaximalityClaim
    (source :
      G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource) where
  claimedMaximality : Prop
  noMaximalityFromA14Alone : ¬ claimedMaximality

theorem
    G8BookIIICh23FloorNormalizedA14PrematureMaximalityClaim.refutes
    {source :
      G8BookIIICh23FloorNormalizedA14BoundaryFormCancellationSource}
    (claim :
      G8BookIIICh23FloorNormalizedA14PrematureMaximalityClaim source) :
    ¬ claim.claimedMaximality :=
  claim.noMaximalityFromA14Alone

end Tau.BookIII.Bridge
