import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusion

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Adjoint Candidate Finite Trace Representation

This module connects the compact-graph reverse-inclusion proof stones to the
finite boundary trace model introduced after the boundary-linear-algebra
calculation.

The previous finite trace module proved the local algebraic implication:

```text
finite boundary trace annihilates all Kirchhoff tests
  -> finite boundary trace satisfies Kirchhoff
```

This file proves the next adapter:

```text
adjoint-domain exhaustion proof stones
  -> adjoint-candidate finite trace representation
  -> finite trace lift plus graph-H2 reverse inclusion
```

The proof stones remain the real compact-graph analytic payload.  This module
does not construct them; it proves that once they are supplied, the new finite
trace route is inhabited without any additional hidden assumption.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- ROUTE SOURCES EXTRACTED FROM PROOF STONES
-- ============================================================

/-- The trace/annihilator payload route extracted from the full
    adjoint-domain exhaustion proof stones. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toTraceAnnihilatorPayloadRouteSource
    (proofStones :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource) :
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource where
  traceExistence := proofStones.traceExistence
  annihilatorClassification := proofStones.annihilatorClassification
  traceSourceAligned := proofStones.traceSourceAligned
  noFiniteDiagnosticTestSubset :=
    proofStones.annihilatorClassification.testsAllKirchhoffDomainElements
  noFiniteDiagnosticTestSubsetWitness :=
    proofStones.annihilatorClassification.testsAllKirchhoffDomainElementsWitness
  status := .conditional_interface

/-- The boundary-forcing payload route extracted from the full proof stones. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toBoundaryForcingPayloadRouteSource
    (proofStones :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource) :
    G8BookIIICh23FloorNormalizedA15BoundaryForcingPayloadRouteSource where
  traceAnnihilator :=
    proofStones.toTraceAnnihilatorPayloadRouteSource
  crossingAgreement := proofStones.crossingAgreement
  kirchhoffBalance := proofStones.kirchhoffBalance
  crossingUsesAnnihilator := by
    simpa [
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toTraceAnnihilatorPayloadRouteSource
    ] using proofStones.crossingUsesAnnihilator
  kirchhoffUsesAnnihilator := by
    simpa [
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toTraceAnnihilatorPayloadRouteSource
    ] using proofStones.kirchhoffUsesAnnihilator
  valueAndDerivativeTracesUseSelectedA12Closures :=
    proofStones.crossingAgreement.valueTraceUsesA12CrossingClosure ∧
      proofStones.kirchhoffBalance.derivativeTraceUsesA12KirchhoffClosure
  valueAndDerivativeTracesUseSelectedA12ClosuresWitness :=
    ⟨proofStones.crossingAgreement.valueTraceUsesA12CrossingClosureWitness,
      proofStones.kirchhoffBalance.derivativeTraceUsesA12KirchhoffClosureWitness⟩
  status := .conditional_interface

/-- The selected-kernel adjoint lift extracted from full proof stones.

This is not a new analytic theorem: the load-bearing trace/annihilator and
boundary-forcing data are exactly the proof-stone fields, now packaged in the
route expected by the finite trace layer. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toSelectedBoundaryKernelAdjointLiftSource
    (proofStones :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource) :
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftSource where
  selectedKernel :=
    g8BookIIICh23FloorNormalizedA15SelectedBoundaryForcingKernel_closed
  traceAnnihilator :=
    proofStones.toTraceAnnihilatorPayloadRouteSource
  boundaryForcing :=
    proofStones.toBoundaryForcingPayloadRouteSource
  boundaryForcingUsesTraceAnnihilator := rfl
  traceAnnihilatorLiftsSelectedKernel :=
    proofStones.traceExistence.traceCompatibleWithSelectedA12SobolevTheory ∧
      proofStones.annihilatorClassification.annihilatorClassifiedByGreenForm
  traceAnnihilatorLiftsSelectedKernelWitness :=
    ⟨proofStones.traceExistence.traceCompatibleWitness,
      proofStones.annihilatorClassification.annihilatorClassifiedWitness⟩
  boundaryForcingLiftsSelectedKernel :=
    proofStones.crossingAgreement.crossingTraceAgreement ∧
      proofStones.kirchhoffBalance.kirchhoffDerivativeBalance
  boundaryForcingLiftsSelectedKernelWitness :=
    ⟨proofStones.crossingAgreement.crossingTraceAgreementWitness,
      proofStones.kirchhoffBalance.kirchhoffDerivativeBalanceWitness⟩
  noSelectedOnlyShortcut :=
    proofStones.reverseInclusion.adjointDomainContainedInKirchhoffDomain ∧
      proofStones.reverseInclusion.graphH2RegularityRecoveredFromAdjointEquation
  noSelectedOnlyShortcutWitness :=
    ⟨proofStones.reverseInclusion.adjointDomainContainedInKirchhoffDomainWitness,
      proofStones.reverseInclusion.graphH2RegularityRecoveredWitness⟩
  status := .conditional_interface

-- ============================================================
-- FINITE TRACE REPRESENTATION OF ADJOINT CANDIDATES
-- ============================================================

/-- The finite boundary-trace image used for adjoint candidates once the
    annihilator classification has been supplied.

This is the exact finite model used by the closed boundary algebra: traces in
the annihilator of all Kirchhoff tests. -/
abbrev
    G8BookIIICh23FloorNormalizedA15AdjointAnnihilatorTraceImage :
    Type :=
  { trace : G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace //
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
        trace }

/-- The finite trace image is nonempty: the zero Kirchhoff trace is in its own
    annihilator. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointAnnihilatorTraceImage_nonempty :
    Nonempty
      G8BookIIICh23FloorNormalizedA15AdjointAnnihilatorTraceImage :=
  ⟨⟨G8BookIIICh23FloorNormalizedA15BoundaryTrace.zero,
      G8BookIIICh23FloorNormalizedA15BoundaryTrace.annihilatesKirchhoff_of_kirchhoff
        G8BookIIICh23FloorNormalizedA15BoundaryTrace.zero_kirchhoff⟩⟩

/-- Proof-carrying source connecting proof stones to a concrete finite trace
    representation of adjoint candidates. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentationSource
    where
  proofStones :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource
  traceCarrier : Type 1
  traceCarrierNonempty : Nonempty traceCarrier
  boundaryTrace :
    traceCarrier ->
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace
  traceAnnihilatesKirchhoff :
    ∀ candidate : traceCarrier,
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
        (boundaryTrace candidate)
  representsAllAdjointBoundaryTraces : Prop
  representsAllAdjointBoundaryTracesWitness :
    representsAllAdjointBoundaryTraces
  traceRepresentationComesFromAdjointTraceExistence : Prop
  traceRepresentationComesFromAdjointTraceExistenceWitness :
    traceRepresentationComesFromAdjointTraceExistence
  traceRepresentationUsesGreenAnnihilatorClassification : Prop
  traceRepresentationUsesGreenAnnihilatorClassificationWitness :
    traceRepresentationUsesGreenAnnihilatorClassification
  graphH2ReverseInclusionCarriedByProofStones : Prop
  graphH2ReverseInclusionCarriedByProofStonesWitness :
    graphH2ReverseInclusionCarriedByProofStones
  status : SpineStatus := .conditional_interface

/-- Closed finite trace representation source extracted from full proof
    stones.  The carrier is the annihilator trace image. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toFiniteTraceRepresentationSource
    (proofStones :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentationSource where
  proofStones := proofStones
  traceCarrier :=
    ULift G8BookIIICh23FloorNormalizedA15AdjointAnnihilatorTraceImage
  traceCarrierNonempty :=
    g8BookIIICh23FloorNormalizedA15AdjointAnnihilatorTraceImage_nonempty.map
      ULift.up
  boundaryTrace := fun candidate => candidate.down.1
  traceAnnihilatesKirchhoff := fun candidate => candidate.down.2
  representsAllAdjointBoundaryTraces :=
    proofStones.traceExistence.traceExists ∧
      proofStones.annihilatorClassification.annihilatorClassifiedByGreenForm
  representsAllAdjointBoundaryTracesWitness :=
    ⟨proofStones.traceExistence.traceExistsWitness,
      proofStones.annihilatorClassification.annihilatorClassifiedWitness⟩
  traceRepresentationComesFromAdjointTraceExistence :=
    proofStones.traceExistence.traceCompatibleWithSelectedA12SobolevTheory
  traceRepresentationComesFromAdjointTraceExistenceWitness :=
    proofStones.traceExistence.traceCompatibleWitness
  traceRepresentationUsesGreenAnnihilatorClassification :=
    proofStones.annihilatorClassification.testsAllKirchhoffDomainElements
  traceRepresentationUsesGreenAnnihilatorClassificationWitness :=
    proofStones.annihilatorClassification.testsAllKirchhoffDomainElementsWitness
  graphH2ReverseInclusionCarriedByProofStones :=
    proofStones.reverseInclusion.graphH2RegularityRecoveredFromAdjointEquation ∧
      proofStones.reverseInclusion.adjointDomainContainedInKirchhoffDomain
  graphH2ReverseInclusionCarriedByProofStonesWitness :=
    ⟨proofStones.reverseInclusion.graphH2RegularityRecoveredWitness,
      proofStones.reverseInclusion.adjointDomainContainedInKirchhoffDomainWitness⟩
  status := .conditional_interface

/-- A finite trace representation source supplies the finite trace adjoint
    candidate model consumed by the previous module. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentationSource.toFiniteTraceAdjointCandidateModel
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidateModel where
  lift :=
    source.proofStones.toSelectedBoundaryKernelAdjointLiftSource
  adjointCandidateCarrier := source.traceCarrier
  adjointCandidateNonempty := source.traceCarrierNonempty
  boundaryTrace := source.boundaryTrace
  representsAllAdjointBoundaryTraces :=
    source.representsAllAdjointBoundaryTraces
  representsAllAdjointBoundaryTracesWitness :=
    source.representsAllAdjointBoundaryTracesWitness
  tracesComeFromLiftedTraceExistence :=
    source.traceRepresentationComesFromAdjointTraceExistence
  tracesComeFromLiftedTraceExistenceWitness :=
    source.traceRepresentationComesFromAdjointTraceExistenceWitness
  traceAnnihilatesKirchhoff :=
    source.traceAnnihilatesKirchhoff
  traceAnnihilatorUsesLift :=
    (source.proofStones.toSelectedBoundaryKernelAdjointLiftSource)
      |>.traceAnnihilatorLiftsSelectedKernelWitness
  boundaryForcingUsesLift :=
    (source.proofStones.toSelectedBoundaryKernelAdjointLiftSource)
      |>.boundaryForcingLiftsSelectedKernelWitness
  status := .conditional_interface

/-- A finite trace representation source supplies the finite-trace lift plus
    reverse-inclusion source. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentationSource.toFiniteTraceLiftReverseInclusionSource
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionSource where
  finiteTraceModel :=
    source.toFiniteTraceAdjointCandidateModel
  reverseInclusion :=
    source.proofStones.reverseInclusion
  reverseUsesCrossing := by
    simpa [
      G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentationSource.toFiniteTraceAdjointCandidateModel,
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toSelectedBoundaryKernelAdjointLiftSource,
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toBoundaryForcingPayloadRouteSource
    ] using source.proofStones.reverseUsesCrossing
  reverseUsesKirchhoff := by
    simpa [
      G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentationSource.toFiniteTraceAdjointCandidateModel,
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toSelectedBoundaryKernelAdjointLiftSource,
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toBoundaryForcingPayloadRouteSource
    ] using source.proofStones.reverseUsesKirchhoff
  reverseUsesFiniteTraceKirchhoff :=
    G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidatesAreKirchhoff
      source.toFiniteTraceAdjointCandidateModel
  reverseUsesFiniteTraceKirchhoffWitness :=
    g8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidatesAreKirchhoff
      source.toFiniteTraceAdjointCandidateModel
  graphH2RecoveryComesFromAdjointEquation :=
    source.proofStones.reverseInclusion.graphH2RegularityRecoveredFromAdjointEquation
  graphH2RecoveryComesFromAdjointEquationWitness :=
    source.proofStones.reverseInclusion.graphH2RegularityRecoveredWitness
  finiteTraceLiftSuppliesAdjointDomainExhaustion :=
    source.graphH2ReverseInclusionCarriedByProofStones ∧
      source.representsAllAdjointBoundaryTraces
  finiteTraceLiftSuppliesAdjointDomainExhaustionWitness :=
    ⟨source.graphH2ReverseInclusionCarriedByProofStonesWitness,
      source.representsAllAdjointBoundaryTracesWitness⟩
  status := .conditional_interface

-- ============================================================
-- TARGETS AND ADAPTERS
-- ============================================================

/-- Target for the finite trace representation plus graph-H2 reverse-inclusion
    constructor. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentationTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentationSource

/-- A proof-stone source supplies the finite trace representation target. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toFiniteTraceRepresentationTarget
    (proofStones :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentationTarget :=
  ⟨proofStones.toFiniteTraceRepresentationSource⟩

/-- A finite trace representation target supplies the finite-trace
    lift/reverse-inclusion target. -/
theorem
    g8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget_ofFiniteTraceRepresentation
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentationTarget) :
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget :=
  target.elim fun source =>
    ⟨source.toFiniteTraceLiftReverseInclusionSource⟩

/-- Full proof stones supply the finite-trace lift/reverse-inclusion target. -/
theorem
    g8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget_ofProofStones
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget) :
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget :=
  target.elim fun proofStones =>
    ⟨proofStones.toFiniteTraceRepresentationSource
      |>.toFiniteTraceLiftReverseInclusionSource⟩

/-- Full proof stones therefore supply the post-boundary-linear-algebra
    residual adjoint-lift/reverse-inclusion target. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionTarget_ofProofStones
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionTarget_ofFiniteTraceLift
    (g8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget_ofProofStones
      target)

/-- Full proof stones also supply the full A1.5 adjoint-domain exhaustion
    payload route through the finite-trace bridge. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget_ofProofStones_viaFiniteTrace
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget_ofFiniteTraceLift
    (g8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget_ofProofStones
      target)

/-- Full proof stones supply the selected-carrier maximal Kirchhoff
    self-adjoint extension target through the finite-trace bridge. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofProofStones_viaFiniteTrace
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofFiniteTraceLift
    (g8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget_ofProofStones
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Proof stones without a finite-trace realization cannot feed the new
    finite-trace route. -/
structure
    G8BookIIICh23FloorNormalizedA15ProofStonesWithoutFiniteTraceRepresentation
    where
  proofStones :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource
  missingFiniteTraceRepresentation :
    ¬ G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentationTarget

theorem
    G8BookIIICh23FloorNormalizedA15ProofStonesWithoutFiniteTraceRepresentation.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15ProofStonesWithoutFiniteTraceRepresentation) :
    False :=
  gap.missingFiniteTraceRepresentation
    gap.proofStones.toFiniteTraceRepresentationTarget

/-- A finite trace representation with no graph-H2 reverse inclusion cannot
    construct the finite-trace lift/reverse-inclusion source. -/
structure
    G8BookIIICh23FloorNormalizedA15FiniteTraceRepresentationWithoutGraphH2Reverse
    where
  source :
    G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentationSource
  missingGraphH2Reverse :
    ¬ source.graphH2ReverseInclusionCarriedByProofStones

theorem
    G8BookIIICh23FloorNormalizedA15FiniteTraceRepresentationWithoutGraphH2Reverse.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15FiniteTraceRepresentationWithoutGraphH2Reverse) :
    False :=
  gap.missingGraphH2Reverse
    gap.source.graphH2ReverseInclusionCarriedByProofStonesWitness

/-- A trace image outside the annihilator cannot be used as an adjoint
    finite-trace candidate in this route. -/
structure
    G8BookIIICh23FloorNormalizedA15TraceImageWithoutAnnihilatorMembership
    where
  trace :
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace
  notAnnihilator :
    ¬ G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
      trace

theorem
    G8BookIIICh23FloorNormalizedA15TraceImageWithoutAnnihilatorMembership.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15TraceImageWithoutAnnihilatorMembership)
    (candidate :
      G8BookIIICh23FloorNormalizedA15AdjointAnnihilatorTraceImage)
    (hCandidateTrace : candidate.1 = gap.trace) :
    False := by
  apply gap.notAnnihilator
  simpa [← hCandidateTrace] using candidate.2

end Tau.BookIII.Bridge
