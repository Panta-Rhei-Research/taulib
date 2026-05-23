import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15AdjointCandidateFiniteTraceRepresentation

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Finite Trace Boundary Forcing Construction

This module removes one more opaque A1.5 reverse-inclusion field.

The finite boundary-linear-algebra theorem already proves:

```text
finite boundary trace annihilates every Kirchhoff test trace
  -> finite boundary trace is Kirchhoff
```

The previous finite-trace representation module still extracted the finite
trace model from full proof stones.  Here we state the direct, non-circular
route instead:

```text
raw finite trace representation of adjoint candidates
  + trace/annihilator route
  -> crossing agreement and Kirchhoff derivative balance
  -> reverse-inclusion source
  -> A1.5 proof-stone target
```

The remaining load-bearing theorem is now the raw finite trace representation
of arbitrary adjoint candidates.  This file proves the boundary-forcing and
reverse-inclusion consequences from that representation; it does not fake the
analytic trace representation itself.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- RAW FINITE TRACE REPRESENTATION
-- ============================================================

/-- Raw finite boundary-trace representation for actual adjoint candidates.

This is the direct source we want from compact-graph adjoint calculus:
adjoint candidates have finite boundary traces, those traces annihilate all
Kirchhoff tests by the Green/adjoint pairing law, and the representation is
global rather than a finite diagnostic subset.
-/
structure
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource
    where
  traceAnnihilator :
    G8BookIIICh23FloorNormalizedA15TraceAnnihilatorPayloadRouteSource
  adjointCandidateCarrier : Type 1
  adjointCandidateNonempty :
    Nonempty adjointCandidateCarrier
  boundaryTrace :
    adjointCandidateCarrier ->
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace
  traceAnnihilatesKirchhoff :
    ∀ candidate : adjointCandidateCarrier,
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
        (boundaryTrace candidate)
  representsAllAdjointBoundaryTraces : Prop
  representsAllAdjointBoundaryTracesWitness :
    representsAllAdjointBoundaryTraces
  tracesComeFromAdjointTraceExistence : Prop
  tracesComeFromAdjointTraceExistenceWitness :
    tracesComeFromAdjointTraceExistence
  traceRepresentationUsesGreenAnnihilatorClassification : Prop
  traceRepresentationUsesGreenAnnihilatorClassificationWitness :
    traceRepresentationUsesGreenAnnihilatorClassification
  graphH2RegularityRecoveredFromAdjointEquation : Prop
  graphH2RegularityRecoveredWitness :
    graphH2RegularityRecoveredFromAdjointEquation
  finiteTraceRepresentationIsGlobal : Prop
  finiteTraceRepresentationIsGlobalWitness :
    finiteTraceRepresentationIsGlobal
  status : SpineStatus := .conditional_interface

/-- Target for the direct finite-trace representation source. -/
def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource

-- ============================================================
-- BOUNDARY FORCING FROM FINITE TRACE ANNIHILATION
-- ============================================================

/-- Crossing agreement read from the finite trace coordinates. -/
def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceCrossingAgreement
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    Prop :=
  ∀ candidate : source.adjointCandidateCarrier,
    G8BookIIICh23FloorNormalizedA15BoundaryTrace.Coord.balanced
      (source.boundaryTrace candidate).value

/-- Kirchhoff derivative balance read from the finite trace coordinates. -/
def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceKirchhoffDerivativeBalance
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    Prop :=
  ∀ candidate : source.adjointCandidateCarrier,
    G8BookIIICh23FloorNormalizedA15BoundaryTrace.Coord.sum
      (source.boundaryTrace candidate).deriv = 0

/-- The closed finite boundary algebra forces crossing agreement from
    annihilator membership. -/
theorem
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.crossingAgreement
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceCrossingAgreement
      source := by
  intro candidate
  exact
    G8BookIIICh23FloorNormalizedA15BoundaryTrace.balanced_of_annihilatesKirchhoff
      (source.traceAnnihilatesKirchhoff candidate)

/-- The closed finite boundary algebra forces derivative balance from
    annihilator membership. -/
theorem
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.kirchhoffDerivativeBalance
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceKirchhoffDerivativeBalance
      source := by
  intro candidate
  exact
    G8BookIIICh23FloorNormalizedA15BoundaryTrace.derivative_sum_eq_zero_of_annihilatesKirchhoff
      (source.traceAnnihilatesKirchhoff candidate)

/-- The raw finite trace representation constructs the crossing-agreement
    proof stone. -/
def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toCrossingAgreementSource
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointCrossingTraceAgreementSource where
  annihilatorSource :=
    source.traceAnnihilator.annihilatorClassification
  crossingTraceAgreement :=
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceCrossingAgreement
      source
  crossingTraceAgreementWitness :=
    source.crossingAgreement
  valueTraceUsesA12CrossingClosure :=
    source.tracesComeFromAdjointTraceExistence ∧
      G8BookIIICh23FloorNormalizedA12CrossingClosureFromBasepointTrace
        g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
  valueTraceUsesA12CrossingClosureWitness :=
    ⟨source.tracesComeFromAdjointTraceExistenceWitness,
      g8BookIIICh23FloorNormalizedA12CrossingClosureFromBasepointTrace_closed⟩
  status := .conditional_interface

/-- The raw finite trace representation constructs the Kirchhoff-balance
    proof stone. -/
def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toKirchhoffBalanceSource
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointKirchhoffBalanceSource where
  annihilatorSource :=
    source.traceAnnihilator.annihilatorClassification
  kirchhoffDerivativeBalance :=
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceKirchhoffDerivativeBalance
      source
  kirchhoffDerivativeBalanceWitness :=
    source.kirchhoffDerivativeBalance
  derivativeTraceUsesA12KirchhoffClosure :=
    source.tracesComeFromAdjointTraceExistence ∧
      G8BookIIICh23FloorNormalizedA12KirchhoffClosureFromOutgoingDerivativeBalance
        g8BookIIICh23FloorNormalizedA12TraceReadinessSource_closed
  derivativeTraceUsesA12KirchhoffClosureWitness :=
    ⟨source.tracesComeFromAdjointTraceExistenceWitness,
      g8BookIIICh23FloorNormalizedA12KirchhoffClosureFromOutgoingDerivativeBalance_closed⟩
  status := .conditional_interface

/-- The raw finite trace representation constructs the boundary-forcing route
    stage directly from the closed finite boundary algebra. -/
def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toBoundaryForcingPayloadRouteSource
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15BoundaryForcingPayloadRouteSource where
  traceAnnihilator := source.traceAnnihilator
  crossingAgreement := source.toCrossingAgreementSource
  kirchhoffBalance := source.toKirchhoffBalanceSource
  crossingUsesAnnihilator := rfl
  kirchhoffUsesAnnihilator := rfl
  valueAndDerivativeTracesUseSelectedA12Closures :=
    (source.toCrossingAgreementSource).valueTraceUsesA12CrossingClosure ∧
      (source.toKirchhoffBalanceSource).derivativeTraceUsesA12KirchhoffClosure
  valueAndDerivativeTracesUseSelectedA12ClosuresWitness :=
    ⟨(source.toCrossingAgreementSource).valueTraceUsesA12CrossingClosureWitness,
      (source.toKirchhoffBalanceSource).derivativeTraceUsesA12KirchhoffClosureWitness⟩
  status := .conditional_interface

-- ============================================================
-- ADJOINT LIFT AND FINITE TRACE MODEL
-- ============================================================

/-- The raw finite trace representation supplies the selected-kernel adjoint
    lift without assuming a pre-existing reverse-inclusion proof stone. -/
def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toSelectedBoundaryKernelAdjointLiftSource
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftSource where
  selectedKernel :=
    g8BookIIICh23FloorNormalizedA15SelectedBoundaryForcingKernel_closed
  traceAnnihilator :=
    source.traceAnnihilator
  boundaryForcing :=
    source.toBoundaryForcingPayloadRouteSource
  boundaryForcingUsesTraceAnnihilator := rfl
  traceAnnihilatorLiftsSelectedKernel :=
    source.tracesComeFromAdjointTraceExistence ∧
      source.traceRepresentationUsesGreenAnnihilatorClassification
  traceAnnihilatorLiftsSelectedKernelWitness :=
    ⟨source.tracesComeFromAdjointTraceExistenceWitness,
      source.traceRepresentationUsesGreenAnnihilatorClassificationWitness⟩
  boundaryForcingLiftsSelectedKernel :=
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceCrossingAgreement
        source ∧
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceKirchhoffDerivativeBalance
        source
  boundaryForcingLiftsSelectedKernelWitness :=
    ⟨source.crossingAgreement, source.kirchhoffDerivativeBalance⟩
  noSelectedOnlyShortcut :=
    source.representsAllAdjointBoundaryTraces ∧
      source.graphH2RegularityRecoveredFromAdjointEquation
  noSelectedOnlyShortcutWitness :=
    ⟨source.representsAllAdjointBoundaryTracesWitness,
      source.graphH2RegularityRecoveredWitness⟩
  status := .conditional_interface

/-- The raw finite trace representation gives the finite trace model consumed
    by the closed boundary-linear-algebra theorem. -/
def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toFiniteTraceAdjointCandidateModel
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidateModel where
  lift :=
    source.toSelectedBoundaryKernelAdjointLiftSource
  adjointCandidateCarrier := source.adjointCandidateCarrier
  adjointCandidateNonempty := source.adjointCandidateNonempty
  boundaryTrace := source.boundaryTrace
  representsAllAdjointBoundaryTraces :=
    source.representsAllAdjointBoundaryTraces
  representsAllAdjointBoundaryTracesWitness :=
    source.representsAllAdjointBoundaryTracesWitness
  tracesComeFromLiftedTraceExistence :=
    source.tracesComeFromAdjointTraceExistence
  tracesComeFromLiftedTraceExistenceWitness :=
    source.tracesComeFromAdjointTraceExistenceWitness
  traceAnnihilatesKirchhoff :=
    source.traceAnnihilatesKirchhoff
  traceAnnihilatorUsesLift :=
    (source.toSelectedBoundaryKernelAdjointLiftSource)
      |>.traceAnnihilatorLiftsSelectedKernelWitness
  boundaryForcingUsesLift :=
    (source.toSelectedBoundaryKernelAdjointLiftSource)
      |>.boundaryForcingLiftsSelectedKernelWitness
  status := .conditional_interface

-- ============================================================
-- REVERSE INCLUSION FROM FINITE TRACE KIRCHHOFF FORCING
-- ============================================================

/-- Reverse inclusion as a theorem-backed consequence of finite trace
    Kirchhoff forcing plus graph-H2 recovery. -/
def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceReverseInclusion
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidatesAreKirchhoff
      source.toFiniteTraceAdjointCandidateModel ∧
    source.representsAllAdjointBoundaryTraces ∧
      source.graphH2RegularityRecoveredFromAdjointEquation

/-- The raw finite trace representation proves the reverse-inclusion source
    expected by A1.5. -/
def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toReverseInclusionSource
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource where
  crossingSource :=
    source.toCrossingAgreementSource
  kirchhoffSource :=
    source.toKirchhoffBalanceSource
  adjointDomainContainedInKirchhoffDomain :=
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceReverseInclusion
      source
  adjointDomainContainedInKirchhoffDomainWitness :=
    ⟨g8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidatesAreKirchhoff
        source.toFiniteTraceAdjointCandidateModel,
      source.representsAllAdjointBoundaryTracesWitness,
      source.graphH2RegularityRecoveredWitness⟩
  graphH2RegularityRecoveredFromAdjointEquation :=
    source.graphH2RegularityRecoveredFromAdjointEquation
  graphH2RegularityRecoveredWitness :=
    source.graphH2RegularityRecoveredWitness
  status := .conditional_interface

/-- The raw finite trace representation directly constructs the finite-trace
    lift/reverse-inclusion source. -/
def
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toFiniteTraceLiftReverseInclusionSource
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionSource where
  finiteTraceModel :=
    source.toFiniteTraceAdjointCandidateModel
  reverseInclusion :=
    source.toReverseInclusionSource
  reverseUsesCrossing := rfl
  reverseUsesKirchhoff := rfl
  reverseUsesFiniteTraceKirchhoff :=
    G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidatesAreKirchhoff
      source.toFiniteTraceAdjointCandidateModel
  reverseUsesFiniteTraceKirchhoffWitness :=
    g8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidatesAreKirchhoff
      source.toFiniteTraceAdjointCandidateModel
  graphH2RecoveryComesFromAdjointEquation :=
    source.graphH2RegularityRecoveredFromAdjointEquation
  graphH2RecoveryComesFromAdjointEquationWitness :=
    source.graphH2RegularityRecoveredWitness
  finiteTraceLiftSuppliesAdjointDomainExhaustion :=
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceReverseInclusion
      source
  finiteTraceLiftSuppliesAdjointDomainExhaustionWitness :=
    source.toReverseInclusionSource.adjointDomainContainedInKirchhoffDomainWitness
  status := .conditional_interface

-- ============================================================
-- TARGET-LEVEL A1.5 ADAPTERS
-- ============================================================

/-- A raw finite trace representation discharges the finite-trace
    lift/reverse-inclusion target without using full proof stones. -/
theorem
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource.toFiniteTraceLiftReverseInclusionTarget
    (source :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource) :
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget :=
  ⟨source.toFiniteTraceLiftReverseInclusionSource⟩

/-- Target-level adapter from raw finite trace representation to the
    finite-trace lift/reverse-inclusion target. -/
theorem
    g8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget_ofRawFiniteTraceRepresentation
    (target :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget) :
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget :=
  target.elim fun source => source.toFiniteTraceLiftReverseInclusionTarget

/-- Target-level adapter from raw finite trace representation to the full
    A1.5 adjoint-domain exhaustion payload route. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget_ofRawFiniteTraceRepresentation
    (target :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget_ofFiniteTraceLift
    (g8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget_ofRawFiniteTraceRepresentation
      target)

/-- Target-level adapter from raw finite trace representation to the proof
    stones themselves.  This is the current narrowest non-circular route into
    the A1.5 maximality theorem. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget_ofRawFiniteTraceRepresentation
    (target :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget_ofPayloadRoute
    (g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget_ofRawFiniteTraceRepresentation
      target)

/-- Target-level adapter from raw finite trace representation to the selected
    A1.5 maximal Kirchhoff self-adjoint extension target. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofRawFiniteTraceRepresentation
    (target :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofFiniteTraceLift
    (g8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget_ofRawFiniteTraceRepresentation
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A raw finite trace representation without annihilator membership cannot
    produce boundary forcing. -/
structure
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceWithoutAnnihilatorMembership
    where
  source :
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource
  missingAnnihilatorMembership :
    ¬ (∀ candidate : source.adjointCandidateCarrier,
        G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
          (source.boundaryTrace candidate))

theorem
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceWithoutAnnihilatorMembership.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceWithoutAnnihilatorMembership) :
    False :=
  gap.missingAnnihilatorMembership gap.source.traceAnnihilatesKirchhoff

/-- If finite trace Kirchhoff forcing is absent, the raw representation cannot
    supply reverse inclusion. -/
structure
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceWithoutReverseInclusion
    where
  source :
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource
  missingReverseInclusion :
    ¬ G8BookIIICh23FloorNormalizedA15RawFiniteTraceReverseInclusion source

theorem
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceWithoutReverseInclusion.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceWithoutReverseInclusion) :
    False :=
  gap.missingReverseInclusion
    ((gap.source.toReverseInclusionSource)
      |>.adjointDomainContainedInKirchhoffDomainWitness)

/-- A finite diagnostic trace family is not enough for the raw representation
    route unless it proves global adjoint-domain coverage. -/
structure
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceDiagnosticOnly
    where
  source :
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceAdjointRepresentationSource
  diagnosticOnly :
    ¬ source.finiteTraceRepresentationIsGlobal

theorem
    G8BookIIICh23FloorNormalizedA15RawFiniteTraceDiagnosticOnly.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15RawFiniteTraceDiagnosticOnly) :
    False :=
  gap.diagnosticOnly gap.source.finiteTraceRepresentationIsGlobalWitness

end Tau.BookIII.Bridge
