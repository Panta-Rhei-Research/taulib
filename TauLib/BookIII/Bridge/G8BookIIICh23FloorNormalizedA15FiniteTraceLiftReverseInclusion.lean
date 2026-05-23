import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15BoundaryLinearAlgebra

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Finite Trace Lift Reverse Inclusion

This module is the next post-boundary-linear-algebra A1.5 step.

The finite four-coordinate boundary calculation has already proved that every
boundary trace annihilating all Kirchhoff traces is itself Kirchhoff.  What
remains for the compact-graph adjoint calculus is to lift actual adjoint
candidates into that finite trace model and then use the resulting Kirchhoff
trace to prove the reverse adjoint-domain inclusion.

This file records that route as a narrow proof-carrying source.  It proves the
finite trace forcing theorem and wires it into the existing residual A1.5
target, without pretending that the analytic adjoint-candidate lift has already
been constructed.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

abbrev G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace :=
  G8BookIIICh23FloorNormalizedA15BoundaryTrace

namespace G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace

export G8BookIIICh23FloorNormalizedA15BoundaryTrace
  (Kirchhoff annihilatesKirchhoff kirchhoff_of_annihilatesKirchhoff)

end G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace

-- ============================================================
-- FINITE TRACE MODEL FOR ADJOINT CANDIDATES
-- ============================================================

/-- A proof-carrying finite boundary-trace model for the actual adjoint
    candidates produced by the selected-kernel adjoint lift.

The load-bearing field is `traceAnnihilatesKirchhoff`: once an adjoint
candidate has been represented by a finite boundary trace and Green's identity
shows that trace annihilates every Kirchhoff test trace, the closed boundary
linear algebra forces the trace to satisfy the Kirchhoff condition. -/
structure
    G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidateModel where
  lift :
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftSource
  adjointCandidateCarrier : Type 1
  adjointCandidateNonempty :
    Nonempty adjointCandidateCarrier
  boundaryTrace :
    adjointCandidateCarrier ->
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace
  representsAllAdjointBoundaryTraces : Prop
  representsAllAdjointBoundaryTracesWitness :
    representsAllAdjointBoundaryTraces
  tracesComeFromLiftedTraceExistence : Prop
  tracesComeFromLiftedTraceExistenceWitness :
    tracesComeFromLiftedTraceExistence
  traceAnnihilatesKirchhoff :
    ∀ candidate : adjointCandidateCarrier,
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
        (boundaryTrace candidate)
  traceAnnihilatorUsesLift :
    lift.traceAnnihilatorLiftsSelectedKernel
  boundaryForcingUsesLift :
    lift.boundaryForcingLiftsSelectedKernel
  status : SpineStatus := .conditional_interface

/-- The theorem-backed finite-trace consequence: every represented adjoint
    candidate trace is Kirchhoff once it annihilates all Kirchhoff tests. -/
def
    G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidatesAreKirchhoff
    (model :
      G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidateModel) :
    Prop :=
  ∀ candidate : model.adjointCandidateCarrier,
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.Kirchhoff
      (model.boundaryTrace candidate)

/-- Boundary-linear algebra closes the finite trace forcing law. -/
theorem
    g8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidatesAreKirchhoff
    (model :
      G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidateModel) :
    G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidatesAreKirchhoff
      model := by
  intro candidate
  exact
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.kirchhoff_of_annihilatesKirchhoff
      (model.traceAnnihilatesKirchhoff candidate)

/-- Pointwise selector for the Kirchhoff trace forced by the finite boundary
    annihilator classification. -/
theorem
    G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidateModel.boundaryTraceKirchhoff
    (model :
      G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidateModel)
    (candidate : model.adjointCandidateCarrier) :
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.Kirchhoff
      (model.boundaryTrace candidate) :=
  g8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidatesAreKirchhoff
    model candidate

-- ============================================================
-- FINITE TRACE LIFT PLUS REVERSE INCLUSION
-- ============================================================

/-- The next residual A1.5 source after finite boundary algebra.

It says that the actual adjoint-domain lift has been represented in the finite
trace model, that those traces have been forced to be Kirchhoff by the closed
boundary calculation, and that this is the boundary input used by the reverse
adjoint-domain inclusion.  The analytic reverse inclusion itself remains an
explicit proof field. -/
structure
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionSource
    where
  finiteTraceModel :
    G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidateModel
  reverseInclusion :
    G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource
  reverseUsesCrossing :
    reverseInclusion.crossingSource =
      finiteTraceModel.lift.boundaryForcing.crossingAgreement
  reverseUsesKirchhoff :
    reverseInclusion.kirchhoffSource =
      finiteTraceModel.lift.boundaryForcing.kirchhoffBalance
  reverseUsesFiniteTraceKirchhoff : Prop
  reverseUsesFiniteTraceKirchhoffWitness :
    reverseUsesFiniteTraceKirchhoff
  graphH2RecoveryComesFromAdjointEquation : Prop
  graphH2RecoveryComesFromAdjointEquationWitness :
    graphH2RecoveryComesFromAdjointEquation
  finiteTraceLiftSuppliesAdjointDomainExhaustion : Prop
  finiteTraceLiftSuppliesAdjointDomainExhaustionWitness :
    finiteTraceLiftSuppliesAdjointDomainExhaustion
  status : SpineStatus := .conditional_interface

/-- Target form for the finite trace lift plus reverse-inclusion source. -/
def
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionSource

/-- The finite trace lift source supplies the previous residual
    adjoint-lift/reverse-inclusion source by inserting the closed finite trace
    Kirchhoff forcing theorem. -/
def
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionSource.toAdjointLiftReverseInclusionSource
    (source :
      G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionSource) :
    G8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionSource where
  lift := source.finiteTraceModel.lift
  reverseInclusion := source.reverseInclusion
  reverseUsesCrossing := source.reverseUsesCrossing
  reverseUsesKirchhoff := source.reverseUsesKirchhoff
  graphH2RecoveryComesFromAdjointEquation :=
    source.graphH2RecoveryComesFromAdjointEquation
  graphH2RecoveryComesFromAdjointEquationWitness :=
    source.graphH2RecoveryComesFromAdjointEquationWitness
  reverseInclusionUsesBoundaryLinearAlgebra :=
    G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidatesAreKirchhoff
      source.finiteTraceModel ∧
      source.reverseUsesFiniteTraceKirchhoff ∧
        source.finiteTraceLiftSuppliesAdjointDomainExhaustion
  reverseInclusionUsesBoundaryLinearAlgebraWitness :=
    ⟨g8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidatesAreKirchhoff
        source.finiteTraceModel,
      source.reverseUsesFiniteTraceKirchhoffWitness,
      source.finiteTraceLiftSuppliesAdjointDomainExhaustionWitness⟩
  status := .conditional_interface

/-- Target-level adapter from the finite trace lift route to the previous
    residual adjoint-lift/reverse-inclusion target. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionTarget_ofFiniteTraceLift
    (target :
      G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionTarget :=
  target.elim fun source =>
    ⟨source.toAdjointLiftReverseInclusionSource⟩

/-- The finite trace lift route is sufficient for the full A1.5
    adjoint-domain exhaustion payload route. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget_ofFiniteTraceLift
    (target :
      G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget_ofAdjointLiftReverseInclusion
    (g8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionTarget_ofFiniteTraceLift
      target)

/-- The finite trace lift route is sufficient for the selected-carrier maximal
    Kirchhoff self-adjoint extension target. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofFiniteTraceLift
    (target :
      G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofAdjointLiftReverseInclusion
    (g8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionTarget_ofFiniteTraceLift
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A finite trace representation without the annihilator law does not supply
    Kirchhoff boundary forcing. -/
structure
    G8BookIIICh23FloorNormalizedA15FiniteTraceWithoutAnnihilatorLaw where
  candidateCarrier : Type 1
  boundaryTrace :
    candidateCarrier ->
      G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace
  missingAnnihilatorLaw :
    ¬ (∀ candidate : candidateCarrier,
        G8BookIIICh23FloorNormalizedA15FiniteBoundaryTrace.annihilatesKirchhoff
          (boundaryTrace candidate))

/-- A finite trace lift without reverse inclusion is not the A1.5 residual
    target. -/
structure
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftWithoutReverseInclusion
    where
  finiteTraceModel :
    G8BookIIICh23FloorNormalizedA15FiniteTraceAdjointCandidateModel
  missingReverseInclusion :
    ¬ G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionTarget

theorem
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftWithoutReverseInclusion.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15FiniteTraceLiftWithoutReverseInclusion)
    (source :
      G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionSource) :
    False :=
  gap.missingReverseInclusion ⟨source⟩

/-- The reverse inclusion used by the finite trace route must be aligned with
    the crossing and Kirchhoff sources of the lifted boundary forcing. -/
structure
    G8BookIIICh23FloorNormalizedA15FiniteTraceReverseInclusionAlignmentGap
    where
  source :
    G8BookIIICh23FloorNormalizedA15FiniteTraceLiftReverseInclusionSource
  crossingMisaligned :
    source.reverseInclusion.crossingSource ≠
      source.finiteTraceModel.lift.boundaryForcing.crossingAgreement
  kirchhoffMisaligned :
    source.reverseInclusion.kirchhoffSource ≠
      source.finiteTraceModel.lift.boundaryForcing.kirchhoffBalance

theorem
    G8BookIIICh23FloorNormalizedA15FiniteTraceReverseInclusionAlignmentGap.refutesCrossing
    (gap :
      G8BookIIICh23FloorNormalizedA15FiniteTraceReverseInclusionAlignmentGap) :
    False :=
  gap.crossingMisaligned gap.source.reverseUsesCrossing

theorem
    G8BookIIICh23FloorNormalizedA15FiniteTraceReverseInclusionAlignmentGap.refutesKirchhoff
    (gap :
      G8BookIIICh23FloorNormalizedA15FiniteTraceReverseInclusionAlignmentGap) :
    False :=
  gap.kirchhoffMisaligned gap.source.reverseUsesKirchhoff

end Tau.BookIII.Bridge
