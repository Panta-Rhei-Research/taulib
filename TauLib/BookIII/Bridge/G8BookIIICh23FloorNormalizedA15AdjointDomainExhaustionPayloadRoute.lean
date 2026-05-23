import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRoute

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Adjoint-Domain Exhaustion Payload Route

This module is the second of the two remaining A1.5 payload routes.

The previous route isolates the small `Type 1` presentation of the selected
Kirchhoff domain.  This route isolates the compact-graph reverse-inclusion
payload:

```text
adjoint trace existence
  -> boundary-form annihilator classification
  -> crossing trace agreement and Kirchhoff derivative balance
  -> reverse adjoint-domain inclusion with graph-H2 recovery
  -> maximal isotropic Kirchhoff boundary condition
  -> proof-stone source
```

The file adds a line-by-line proof-map route and adapters into the already
existing `G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource`.
It does not prove the analytic graph-operator theorems themselves; it makes the
remaining payload exact and composable.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- STAGE 1: TRACE EXISTENCE AND ANNIHILATOR CLASSIFICATION
-- ============================================================

/-- First reverse-inclusion route stage: adjoint boundary traces exist and the
    boundary-form annihilator is classified against all Kirchhoff tests. -/
structure
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource where
  traceExistence :
    G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource
  annihilatorClassification :
    G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationSource
  traceSourceAligned :
    annihilatorClassification.traceSource = traceExistence
  noFiniteDiagnosticTestSubset : Prop
  noFiniteDiagnosticTestSubsetWitness :
    noFiniteDiagnosticTestSubset
  status : SpineStatus := .conditional_interface

/-- Target for the trace/annihilator route stage. -/
def
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource

/-- A trace/annihilator route source supplies adjoint trace existence. -/
theorem
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource.toTraceExistenceTarget
    (source :
      G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource) :
    Nonempty
      G8BookIIICh23FloorNormalizedA15AdjointBoundaryTraceExistenceSource :=
  ⟨source.traceExistence⟩

/-- A trace/annihilator route source supplies annihilator classification. -/
theorem
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource.toAnnihilatorTarget
    (source :
      G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource) :
    Nonempty
      G8BookIIICh23FloorNormalizedA15BoundaryFormAnnihilatorClassificationSource :=
  ⟨source.annihilatorClassification⟩

-- ============================================================
-- STAGE 2: CROSSING AGREEMENT AND KIRCHHOFF BALANCE
-- ============================================================

/-- Second reverse-inclusion route stage: the annihilator classification forces
    crossing value agreement and Kirchhoff derivative balance. -/
structure
    G8BookIIICh23FloorNormalizedA15BoundaryForcingPayloadRouteSource where
  traceAnnihilator :
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource
  crossingAgreement :
    G8BookIIICh23FloorNormalizedA15AdjointCrossingTraceAgreementSource
  kirchhoffBalance :
    G8BookIIICh23FloorNormalizedA15AdjointKirchhoffBalanceSource
  crossingUsesAnnihilator :
    crossingAgreement.annihilatorSource =
      traceAnnihilator.annihilatorClassification
  kirchhoffUsesAnnihilator :
    kirchhoffBalance.annihilatorSource =
      traceAnnihilator.annihilatorClassification
  valueAndDerivativeTracesUseSelectedA12Closures : Prop
  valueAndDerivativeTracesUseSelectedA12ClosuresWitness :
    valueAndDerivativeTracesUseSelectedA12Closures
  status : SpineStatus := .conditional_interface

/-- Target for the boundary-forcing route stage. -/
def
    G8BookIIICh23FloorNormalizedA15BoundaryForcingPayloadRouteTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15BoundaryForcingPayloadRouteSource

/-- A boundary-forcing source supplies crossing agreement. -/
theorem
    G8BookIIICh23FloorNormalizedA15BoundaryForcingPayloadRouteSource.toCrossingAgreementTarget
    (source :
      G8BookIIICh23FloorNormalizedA15BoundaryForcingPayloadRouteSource) :
    Nonempty
      G8BookIIICh23FloorNormalizedA15AdjointCrossingTraceAgreementSource :=
  ⟨source.crossingAgreement⟩

/-- A boundary-forcing source supplies Kirchhoff derivative balance. -/
theorem
    G8BookIIICh23FloorNormalizedA15BoundaryForcingPayloadRouteSource.toKirchhoffBalanceTarget
    (source :
      G8BookIIICh23FloorNormalizedA15BoundaryForcingPayloadRouteSource) :
    Nonempty
      G8BookIIICh23FloorNormalizedA15AdjointKirchhoffBalanceSource :=
  ⟨source.kirchhoffBalance⟩

-- ============================================================
-- STAGE 3: REVERSE INCLUSION AND MAXIMAL BOUNDARY
-- ============================================================

/-- Full reverse-inclusion payload route: the boundary-forcing route gives the
    crossing and Kirchhoff sources used by reverse inclusion, and maximal
    isotropic Kirchhoff boundary evidence blocks larger symmetric extensions. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteSource where
  boundaryForcing :
    G8BookIIICh23FloorNormalizedA15BoundaryForcingPayloadRouteSource
  maximalBoundary :
    G8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundarySource
  reverseInclusion :
    G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource
  reverseUsesCrossing :
    reverseInclusion.crossingSource = boundaryForcing.crossingAgreement
  reverseUsesKirchhoff :
    reverseInclusion.kirchhoffSource = boundaryForcing.kirchhoffBalance
  graphH2RecoveryComesFromAdjointEquation : Prop
  graphH2RecoveryComesFromAdjointEquationWitness :
    graphH2RecoveryComesFromAdjointEquation
  maximalBoundaryUsedForNoLargerSymmetricExtension : Prop
  maximalBoundaryUsedForNoLargerSymmetricExtensionWitness :
    maximalBoundaryUsedForNoLargerSymmetricExtension
  status : SpineStatus := .conditional_interface

/-- Target for the full reverse-inclusion payload route. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteSource

/-- The full route source assembles the existing proof-stone source. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteSource.toProofStoneSource
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource where
  traceExistence :=
    source.boundaryForcing.traceAnnihilator.traceExistence
  annihilatorClassification :=
    source.boundaryForcing.traceAnnihilator.annihilatorClassification
  crossingAgreement :=
    source.boundaryForcing.crossingAgreement
  kirchhoffBalance :=
    source.boundaryForcing.kirchhoffBalance
  maximalBoundary :=
    source.maximalBoundary
  reverseInclusion :=
    source.reverseInclusion
  traceSourceAligned :=
    source.boundaryForcing.traceAnnihilator.traceSourceAligned
  crossingUsesAnnihilator :=
    source.boundaryForcing.crossingUsesAnnihilator
  kirchhoffUsesAnnihilator :=
    source.boundaryForcing.kirchhoffUsesAnnihilator
  reverseUsesCrossing :=
    source.reverseUsesCrossing
  reverseUsesKirchhoff :=
    source.reverseUsesKirchhoff
  status := .conditional_interface

/-- A full route source proves the existing proof-stone target. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteSource.toProofStoneTarget
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget :=
  ⟨source.toProofStoneSource⟩

/-- Target-level adapter from the full route to the existing proof-stone
    target. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget_ofPayloadRoute
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget :=
  target.elim fun source => source.toProofStoneTarget

-- ============================================================
-- TWO-ROUTE ASSEMBLY BACK INTO THE A1.5 ENGINE
-- ============================================================

/-- The two remaining payload routes together assemble the adjoint-domain
    Type-1 presentation target. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofRemainingPayloadRoutes
    (presentationRoute :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget)
    (exhaustionRoute :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofSelectedRouteAndProofStones
    presentationRoute
    (g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget_ofPayloadRoute
      exhaustionRoute)

/-- The two remaining payload routes together feed the concrete A1.5 engine. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofRemainingPayloadRoutes
    (presentationRoute :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget)
    (exhaustionRoute :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofType1Presentation
    (g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofRemainingPayloadRoutes
      presentationRoute
      exhaustionRoute)

/-- The two remaining payload routes are enough for the two analytic law
    targets already consumed by the reverse-inclusion path. -/
theorem
    g8BookIIICh23FloorNormalizedA15TwoAnalyticLawTargets_ofRemainingPayloadRoutes
    (presentationRoute :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteTarget)
    (exhaustionRoute :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget) :
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquationTarget ∧
      G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTestsTarget :=
  g8BookIIICh23FloorNormalizedA15TwoAnalyticLawTargets_ofType1Presentation
    (g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofRemainingPayloadRoutes
      presentationRoute
      exhaustionRoute)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- An annihilator classification not aligned with the trace source cannot be
    used as the line-by-line trace/annihilator route. -/
structure
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorRouteAlignmentGap
    where
  source :
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource
  notAligned :
    source.annihilatorClassification.traceSource ≠ source.traceExistence

theorem
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorRouteAlignmentGap.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15TraceAnnihilatorRouteAlignmentGap) :
    False :=
  gap.notAligned gap.source.traceSourceAligned

/-- Crossing agreement and Kirchhoff balance must be derived from the same
    annihilator classification. -/
structure
    G8BookIIICh23FloorNormalizedA15BoundaryForcingRouteAlignmentGap
    where
  source :
    G8BookIIICh23FloorNormalizedA15BoundaryForcingPayloadRouteSource
  crossingNotAligned :
    source.crossingAgreement.annihilatorSource ≠
      source.traceAnnihilator.annihilatorClassification

theorem
    G8BookIIICh23FloorNormalizedA15BoundaryForcingRouteAlignmentGap.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15BoundaryForcingRouteAlignmentGap) :
    False :=
  gap.crossingNotAligned gap.source.crossingUsesAnnihilator

/-- Reverse inclusion must use the crossing and Kirchhoff sources supplied by
    the boundary-forcing route. -/
structure
    G8BookIIICh23FloorNormalizedA15ReverseInclusionRouteAlignmentGap
    where
  source :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteSource
  reverseCrossingNotAligned :
    source.reverseInclusion.crossingSource ≠
      source.boundaryForcing.crossingAgreement

theorem
    G8BookIIICh23FloorNormalizedA15ReverseInclusionRouteAlignmentGap.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15ReverseInclusionRouteAlignmentGap) :
    False :=
  gap.reverseCrossingNotAligned gap.source.reverseUsesCrossing

/-- Maximal-boundary evidence is still required: reverse inclusion alone is
    not the full maximal self-adjoint extension proof-stone package. -/
structure
    G8BookIIICh23FloorNormalizedA15ExhaustionRouteWithoutMaximalBoundary
    where
  source :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteSource
  missingMaximalBoundary :
    ¬ source.maximalBoundary.maximalIsotropicKirchhoffBoundaryCondition

theorem
    G8BookIIICh23FloorNormalizedA15ExhaustionRouteWithoutMaximalBoundary.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15ExhaustionRouteWithoutMaximalBoundary) :
    False :=
  gap.missingMaximalBoundary
    gap.source.maximalBoundary.maximalIsotropicKirchhoffBoundaryConditionWitness

end Tau.BookIII.Bridge
