import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationConstruction
import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRoute

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Adjoint-Domain Exhaustion Payload Construction

This module pushes the remaining A1.5 payload one step lower.

The selected Ch.23 boundary calculus already supplies theorem-backed trace,
Green, crossing, and Kirchhoff facts on the closed selected Kirchhoff domain.
Those facts are recorded here as a closed selected boundary-forcing kernel.

The full A1.5 reverse-inclusion theorem still needs an adjoint-domain lift:

```text
selected boundary kernel
  -> adjoint trace/annihilator route
  -> adjoint crossing/Kirchhoff boundary-forcing route
  -> maximal Kirchhoff boundary + reverse inclusion
  -> adjoint-domain exhaustion payload route
```

The module does not identify selected Kirchhoff facts with arbitrary adjoint
domain facts.  It makes that lift explicit and keeps maximal boundary plus
reverse inclusion as load-bearing proof fields.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CLOSED SELECTED BOUNDARY-FORCING KERNEL
-- ============================================================

/-- The theorem-backed selected boundary calculus available before the actual
    adjoint-domain lift.

This is deliberately a selected-domain kernel, not the full reverse-inclusion
route.  It records the facts already obtained from A1.2/A1.4/A1.5 selected
representatives. -/
structure
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryForcingKernel where
  selectedTraceReadiness :
    G8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint
  selectedBoundaryTracesExist :
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryTracesExist
  selectedGreenBookkeeping :
    G8BookIIICh23FloorNormalizedA15SelectedGreenBookkeepingForAdjoint
  selectedBoundaryFormEqualsAdjointDefect :
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryFormEqualsAdjointDefect
  selectedAdjointDefectPairingVanishes :
    G8BookIIICh23FloorNormalizedA15SelectedAdjointDefectPairingVanishes
  selectedAnnihilatesBoundaryForm :
    G8BookIIICh23FloorNormalizedA15SelectedAnnihilatesBoundaryForm
  selectedCrossingClosure :
    G8BookIIICh23FloorNormalizedA12CrossingClosureFromBasepointTrace
      g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
  selectedKirchhoffClosure :
    G8BookIIICh23FloorNormalizedA12KirchhoffClosureFromOutgoingDerivativeBalance
      g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
  selectedPresentationRoute :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget
  status : SpineStatus := .conditional_interface

/-- The selected boundary-forcing kernel is closed from the already-built
    selected A1.2/A1.4/A1.5 facts. -/
def
    g8BookIIICh23FloorNormalizedA15SelectedBoundaryForcingKernel_closed :
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryForcingKernel where
  selectedTraceReadiness :=
    g8BookIIICh23FloorNormalizedA15SelectedTraceReadinessForAdjoint_closed
  selectedBoundaryTracesExist :=
    g8BookIIICh23FloorNormalizedA15SelectedBoundaryTracesExist_closed
  selectedGreenBookkeeping :=
    g8BookIIICh23FloorNormalizedA15SelectedGreenBookkeepingForAdjoint_closed
  selectedBoundaryFormEqualsAdjointDefect :=
    g8BookIIICh23FloorNormalizedA15SelectedBoundaryFormEqualsAdjointDefect_closed
  selectedAdjointDefectPairingVanishes :=
    g8BookIIICh23FloorNormalizedA15SelectedAdjointDefectPairingVanishes_closed
  selectedAnnihilatesBoundaryForm :=
    g8BookIIICh23FloorNormalizedA15SelectedAnnihilatesBoundaryForm_closed
  selectedCrossingClosure :=
    g8BookIIICh23FloorNormalizedA12CrossingClosureFromBasepointTrace_closed
  selectedKirchhoffClosure :=
    g8BookIIICh23FloorNormalizedA12KirchhoffClosureFromOutgoingDerivativeBalance_closed
  selectedPresentationRoute :=
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget_closed
  status := .conditional_interface

/-- Target form for the selected boundary-forcing kernel. -/
def
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryForcingKernelTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryForcingKernel

/-- The selected boundary-forcing kernel target is theorem-backed. -/
theorem
    g8BookIIICh23FloorNormalizedA15SelectedBoundaryForcingKernelTarget_closed :
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryForcingKernelTarget :=
  ⟨g8BookIIICh23FloorNormalizedA15SelectedBoundaryForcingKernel_closed⟩

-- ============================================================
-- ADJOINT LIFT OF THE SELECTED KERNEL
-- ============================================================

/-- Proof-carrying lift from the selected boundary kernel to the actual
    adjoint-domain trace/annihilator and boundary-forcing route stages.

The lift is the part that must not be hidden: it says the selected boundary
calculus has been promoted to the adjoint-domain route, not merely checked on
the selected Kirchhoff representatives. -/
structure
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftSource where
  selectedKernel :
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryForcingKernel
  traceAnnihilator :
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource
  boundaryForcing :
    G8BookIIICh23FloorNormalizedA15BoundaryForcingPayloadRouteSource
  boundaryForcingUsesTraceAnnihilator :
    boundaryForcing.traceAnnihilator = traceAnnihilator
  traceAnnihilatorLiftsSelectedKernel : Prop
  traceAnnihilatorLiftsSelectedKernelWitness :
    traceAnnihilatorLiftsSelectedKernel
  boundaryForcingLiftsSelectedKernel : Prop
  boundaryForcingLiftsSelectedKernelWitness :
    boundaryForcingLiftsSelectedKernel
  noSelectedOnlyShortcut : Prop
  noSelectedOnlyShortcutWitness :
    noSelectedOnlyShortcut
  status : SpineStatus := .conditional_interface

/-- Target for lifting the selected boundary kernel into the adjoint-domain
    trace/annihilator and boundary-forcing route stages. -/
def
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftSource

/-- A selected-kernel lift supplies the trace/annihilator route target. -/
theorem
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftSource.toTraceAnnihilatorRouteTarget
    (source :
      G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftSource) :
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteTarget :=
  ⟨source.traceAnnihilator⟩

/-- A selected-kernel lift supplies the boundary-forcing route target. -/
theorem
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftSource.toBoundaryForcingRouteTarget
    (source :
      G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftSource) :
    G8BookIIICh23FloorNormalizedA15BoundaryForcingPayloadRouteTarget :=
  ⟨source.boundaryForcing⟩

-- ============================================================
-- MAXIMAL BOUNDARY AND REVERSE-INCLUSION SOURCE
-- ============================================================

/-- The remaining A1.5 payload after the selected Type-1 presentation and
    selected boundary kernel are closed.

This is intentionally narrow: it requires the adjoint lift, maximal isotropic
Kirchhoff boundary evidence, and the reverse adjoint-domain inclusion aligned
with the boundary-forcing route. -/
structure
    G8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionSource where
  lift :
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftSource
  maximalBoundary :
    G8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundarySource
  reverseInclusion :
    G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource
  reverseUsesCrossing :
    reverseInclusion.crossingSource = lift.boundaryForcing.crossingAgreement
  reverseUsesKirchhoff :
    reverseInclusion.kirchhoffSource = lift.boundaryForcing.kirchhoffBalance
  graphH2RecoveryComesFromAdjointEquation : Prop
  graphH2RecoveryComesFromAdjointEquationWitness :
    graphH2RecoveryComesFromAdjointEquation
  maximalBoundaryUsedForNoLargerSymmetricExtension : Prop
  maximalBoundaryUsedForNoLargerSymmetricExtensionWitness :
    maximalBoundaryUsedForNoLargerSymmetricExtension
  status : SpineStatus := .conditional_interface

/-- Target for the residual maximal-boundary plus reverse-inclusion payload. -/
def
    G8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionSource

/-- The residual maximal-boundary/reverse-inclusion source assembles the
    already-defined full adjoint-domain exhaustion payload route. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionSource.toPayloadRouteSource
    (source :
      G8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteSource where
  boundaryForcing := source.lift.boundaryForcing
  maximalBoundary := source.maximalBoundary
  reverseInclusion := source.reverseInclusion
  reverseUsesCrossing := source.reverseUsesCrossing
  reverseUsesKirchhoff := source.reverseUsesKirchhoff
  graphH2RecoveryComesFromAdjointEquation :=
    source.graphH2RecoveryComesFromAdjointEquation
  graphH2RecoveryComesFromAdjointEquationWitness :=
    source.graphH2RecoveryComesFromAdjointEquationWitness
  maximalBoundaryUsedForNoLargerSymmetricExtension :=
    source.maximalBoundaryUsedForNoLargerSymmetricExtension
  maximalBoundaryUsedForNoLargerSymmetricExtensionWitness :=
    source.maximalBoundaryUsedForNoLargerSymmetricExtensionWitness
  status := .conditional_interface

/-- The residual maximal-boundary/reverse-inclusion target supplies the full
    A1.5 adjoint-domain exhaustion payload route target. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget_ofMaximalBoundaryReverseInclusion
    (target :
      G8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget :=
  target.elim fun source => ⟨source.toPayloadRouteSource⟩

/-- With the selected Type-1 presentation already closed, the residual
    maximal-boundary/reverse-inclusion target is sufficient for the A1.5
    adjoint-domain Type-1 presentation target. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofMaximalBoundaryReverseInclusion
    (target :
      G8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofRemainingPayloadRoutes
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget_closed
    (g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget_ofMaximalBoundaryReverseInclusion
      target)

/-- With the selected Type-1 presentation already closed, the residual
    maximal-boundary/reverse-inclusion target is sufficient for the concrete
    A1.5 adjoint-calculus engine target. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofMaximalBoundaryReverseInclusion
    (target :
      G8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofRemainingPayloadRoutes
    g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget_closed
    (g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget_ofMaximalBoundaryReverseInclusion
      target)

/-- The residual maximal-boundary/reverse-inclusion target is sufficient for
    the selected-carrier maximal Kirchhoff self-adjoint extension target. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofMaximalBoundaryReverseInclusion
    (target :
      G8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  target.elim fun source =>
    source.toPayloadRouteSource.toProofStoneSource
      |>.toMaximalKirchhoffSelfAdjointExtensionTarget

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A selected boundary kernel by itself is not an adjoint-domain lift. -/
structure
    G8BookIIICh23FloorNormalizedA15SelectedKernelWithoutAdjointLift where
  kernel :
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryForcingKernel
  missingLift :
    ¬ G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftTarget

theorem
    G8BookIIICh23FloorNormalizedA15SelectedKernelWithoutAdjointLift.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15SelectedKernelWithoutAdjointLift)
    (lift :
      G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftSource) :
    False :=
  gap.missingLift ⟨lift⟩

/-- The boundary-forcing route used by the residual source must be the one
    aligned with the lifted trace/annihilator route. -/
structure
    G8BookIIICh23FloorNormalizedA15BoundaryLiftAlignmentGap where
  source :
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftSource
  boundaryForcingNotAligned :
    source.boundaryForcing.traceAnnihilator ≠ source.traceAnnihilator

theorem
    G8BookIIICh23FloorNormalizedA15BoundaryLiftAlignmentGap.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15BoundaryLiftAlignmentGap) :
    False :=
  gap.boundaryForcingNotAligned
    gap.source.boundaryForcingUsesTraceAnnihilator

/-- Reverse inclusion without maximal-boundary evidence is still not the full
    A1.5 maximal self-adjoint extension payload. -/
structure
    G8BookIIICh23FloorNormalizedA15ReverseInclusionWithoutMaximalBoundary where
  reverseInclusion :
    G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource
  missingMaximalBoundary :
    ¬ G8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionTarget

theorem
    G8BookIIICh23FloorNormalizedA15ReverseInclusionWithoutMaximalBoundary.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15ReverseInclusionWithoutMaximalBoundary)
    (source :
      G8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionSource) :
    False :=
  gap.missingMaximalBoundary ⟨source⟩

end Tau.BookIII.Bridge
