import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrier
import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15SelectedEndpointTraceReadout

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Genuine Adjoint Carrier Instantiation

This module instantiates the option-1 genuine adjoint-domain carrier from the
exact compact-graph adjoint-domain realization theorem.

The source theorem is intentionally narrow:

```text
actual Hilbert-adjoint graph carrier
  -> selected Kirchhoff representative
  -> distributional adjoint equation
  -> graph-H2 trace recovery
  -> Green pairing against every Kirchhoff test
  -> boundary annihilator forcing
  -> reverse inclusion into the selected Kirchhoff domain
```

The closed selected Kirchhoff Type-1 presentation supplies the test universe.
The selected A1.3-A1.4 facts supply pointwise selected regularity and Green
selectors once an adjoint candidate has been mapped to its selected
representative.

No final/RH-facing, spectral, O3, determinant, divisor, or completion source
is used here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CLOSED TEST PRESENTATION
-- ============================================================

/-- The closed exhaustive Kirchhoff-test presentation used by the genuine
    adjoint-domain carrier. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation :
    G8BookIIICh23FloorNormalizedA15KirchhoffTestPresentation :=
  g8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationRouteSource_closed
    |>.toPresentation
    |>.toKirchhoffTestPresentation

/-- The closed Kirchhoff-test presentation is exhaustive. -/
theorem
    g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation_exhaustive :
    g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
      |>.exhaustsSelectedKirchhoffDomain :=
  g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
    |>.exhaustsSelectedKirchhoffDomainWitness

-- ============================================================
-- COMPACT-GRAPH ADJOINT-DOMAIN REALIZATION SOURCE
-- ============================================================

/-- The exact compact-graph theorem needed to instantiate the genuine
    adjoint-domain carrier.

This is the next load-bearing A1.5 mathematical source: it says the actual
Hilbert adjoint graph has a global carrier, every carrier point has a selected
Kirchhoff representative, and the analytic regularity/Green/boundary forcing
route proves reverse inclusion. -/
structure
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource
    where
  adjoint : Type 1
  adjointNonempty : Nonempty adjoint
  toSelected :
    adjoint →
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffOperatorDomain
  representsHilbertAdjointGraph : Prop
  representsHilbertAdjointGraphWitness :
    representsHilbertAdjointGraph
  distributionalAdjointEquation : Prop
  distributionalAdjointEquationWitness :
    distributionalAdjointEquation
  graphH2TraceRecoveryFromAdjointEquation : Prop
  graphH2TraceRecoveryWitness :
    graphH2TraceRecoveryFromAdjointEquation
  greenPairingAgainstAllKirchhoffTests : Prop
  greenPairingAgainstAllKirchhoffTestsWitness :
    greenPairingAgainstAllKirchhoffTests
  boundaryTraceAnnihilatorClassification : Prop
  boundaryTraceAnnihilatorClassificationWitness :
    boundaryTraceAnnihilatorClassification
  boundaryTraceForcesKirchhoffConditions : Prop
  boundaryTraceForcesKirchhoffConditionsWitness :
    boundaryTraceForcesKirchhoffConditions
  reverseInclusionIntoSelectedKirchhoffDomain : Prop
  reverseInclusionWitness :
    reverseInclusionIntoSelectedKirchhoffDomain
  noSelectedDomainShortcut : Prop
  noSelectedDomainShortcutWitness :
    noSelectedDomainShortcut
  noFiniteDiagnosticSubstitute : Prop
  noFiniteDiagnosticSubstituteWitness :
    noFiniteDiagnosticSubstitute
  status : SpineStatus := .conditional_interface

/-- Target for the compact-graph adjoint-domain realization theorem. -/
def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource

-- ============================================================
-- INSTANTIATION OF THE GENUINE CARRIER
-- ============================================================

/-- A compact-graph adjoint-domain realization source instantiates the
    genuine adjoint-domain carrier. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource.toGenuineAdjointDomainCarrierSource
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource) :
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierSource where
  adjoint := source.adjoint
  adjointNonempty := source.adjointNonempty
  toSelected := source.toSelected
  tests := g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
  representsHilbertAdjointGraph :=
    source.representsHilbertAdjointGraph
  representsHilbertAdjointGraphWitness :=
    source.representsHilbertAdjointGraphWitness
  distributionalAdjointEquation :=
    source.distributionalAdjointEquation
  distributionalAdjointEquationWitness :=
    source.distributionalAdjointEquationWitness
  graphH2TraceRecoveryFromAdjointEquation :=
    source.graphH2TraceRecoveryFromAdjointEquation
  graphH2TraceRecoveryWitness :=
    source.graphH2TraceRecoveryWitness
  greenPairingAgainstAllKirchhoffTests :=
    source.greenPairingAgainstAllKirchhoffTests
  greenPairingAgainstAllKirchhoffTestsWitness :=
    source.greenPairingAgainstAllKirchhoffTestsWitness
  boundaryTraceAnnihilatorClassification :=
    source.boundaryTraceAnnihilatorClassification
  boundaryTraceAnnihilatorClassificationWitness :=
    source.boundaryTraceAnnihilatorClassificationWitness
  boundaryTraceForcesKirchhoffConditions :=
    source.boundaryTraceForcesKirchhoffConditions
  boundaryTraceForcesKirchhoffConditionsWitness :=
    source.boundaryTraceForcesKirchhoffConditionsWitness
  reverseInclusionIntoSelectedKirchhoffDomain :=
    source.reverseInclusionIntoSelectedKirchhoffDomain
  reverseInclusionWitness :=
    source.reverseInclusionWitness
  noSelectedDomainShortcut :=
    source.noSelectedDomainShortcut
  noSelectedDomainShortcutWitness :=
    source.noSelectedDomainShortcutWitness
  noFiniteDiagnosticSubstitute :=
    source.noFiniteDiagnosticSubstitute
  noFiniteDiagnosticSubstituteWitness :=
    source.noFiniteDiagnosticSubstituteWitness
  adjointEquationInSelectedL2 :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15SelectedAdjointEquationInL2
        (source.toSelected u)
  adjointEquationWitness :=
    fun u =>
      g8BookIIICh23FloorNormalizedA15SelectedAdjointEquationInL2_closed
        (source.toSelected u)
  adjointDistributionalSecondDerivativeInSelectedL2 :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15SelectedDistributionalSecondDerivativeInL2
        (source.toSelected u)
  adjointDistributionalSecondDerivativeWitness :=
    fun u =>
      g8BookIIICh23FloorNormalizedA15SelectedDistributionalSecondDerivativeInL2_closed
        (source.toSelected u)
  graphH2RegularityFromAdjointEquation :=
    fun u =>
      G8BookIIICh23FloorNormalizedA15SelectedGraphH2Regularity
        (source.toSelected u)
  graphH2RegularityWitness :=
    fun u =>
      g8BookIIICh23FloorNormalizedA15SelectedGraphH2Regularity_closed
        (source.toSelected u)
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
        (source.toSelected u)
  traceRecoveryWitness :=
    fun u =>
      g8BookIIICh23FloorNormalizedA15SelectedTraceRecovery_closed
        (source.toSelected u)
  valueAndDerivativeBoundaryTracesExist :=
    fun _ => G8BookIIICh23FloorNormalizedA15SelectedBoundaryTracesExist
  valueAndDerivativeBoundaryTracesExistWitness :=
    fun _ =>
      g8BookIIICh23FloorNormalizedA15SelectedBoundaryTracesExist_closed
  adjointPairingIdentityAgainstKirchhoffTests :=
    fun u v =>
      G8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity
        (source.toSelected u)
        (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
          |>.realize v)
  adjointPairingIdentityWitness :=
    fun u v =>
      g8BookIIICh23FloorNormalizedA15SelectedAdjointPairingIdentity_closed
        (source.toSelected u)
        (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
          |>.realize v)
  edgewiseGreenIdentityAgainstKirchhoffTests :=
    fun u v =>
      G8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenIdentity
        (source.toSelected u)
        (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
          |>.realize v)
  edgewiseGreenIdentityWitness :=
    fun u v =>
      g8BookIIICh23FloorNormalizedA15SelectedEdgewiseGreenIdentity_closed
        (source.toSelected u)
        (g8BookIIICh23FloorNormalizedA15ClosedKirchhoffTestPresentation
          |>.realize v)
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

/-- A compact-graph adjoint-domain realization source instantiates the
    genuine carrier target. -/
theorem
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource.toGenuineAdjointDomainCarrierTarget
    (source :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource) :
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierTarget :=
  ⟨source.toGenuineAdjointDomainCarrierSource⟩

/-- Target-level adapter from the compact-graph adjoint-domain realization
    theorem to the genuine carrier target. -/
theorem
    g8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierTarget_ofCompactGraphAdjointDomainRealization
    (target :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget) :
    G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierTarget :=
  target.elim fun source => source.toGenuineAdjointDomainCarrierTarget

-- ============================================================
-- DOWNSTREAM A1.5 CONSEQUENCES
-- ============================================================

/-- The genuine adjoint-domain carrier target now feeds the endpoint-trace
    route to selected-carrier A1.5 maximal Kirchhoff self-adjointness. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofGenuineAdjointDomainCarrier
    (target :
      G8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofEngine_viaEndpointTrace
    (g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofGenuineAdjointDomainCarrier
      target)

/-- Compact-graph adjoint-domain realization is sufficient for the selected
    A1.5 maximality target. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofCompactGraphAdjointDomainRealization
    (target :
      G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofGenuineAdjointDomainCarrier
    (g8BookIIICh23FloorNormalizedA15GenuineAdjointDomainCarrierTarget_ofCompactGraphAdjointDomainRealization
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A compact-graph realization without reverse inclusion cannot instantiate
    the genuine carrier. -/
structure
    G8BookIIICh23FloorNormalizedA15CompactGraphRealizationWithoutReverseInclusion
    where
  source :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource
  missingReverseInclusion :
    ¬ source.reverseInclusionIntoSelectedKirchhoffDomain

theorem
    G8BookIIICh23FloorNormalizedA15CompactGraphRealizationWithoutReverseInclusion.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15CompactGraphRealizationWithoutReverseInclusion) :
    False :=
  gap.missingReverseInclusion gap.source.reverseInclusionWitness

/-- A realization source without all-test Green pairing is not sufficient for
    the genuine distributional/pairing route. -/
structure
    G8BookIIICh23FloorNormalizedA15CompactGraphRealizationWithoutAllTestGreen
    where
  source :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource
  missingAllTestGreen :
    ¬ source.greenPairingAgainstAllKirchhoffTests

theorem
    G8BookIIICh23FloorNormalizedA15CompactGraphRealizationWithoutAllTestGreen.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15CompactGraphRealizationWithoutAllTestGreen) :
    False :=
  gap.missingAllTestGreen
    gap.source.greenPairingAgainstAllKirchhoffTestsWitness

/-- A source that only reuses the selected domain without proving genuine
    adjoint-domain coverage is rejected by the no-shortcut field. -/
structure
    G8BookIIICh23FloorNormalizedA15CompactGraphRealizationSelectedShortcutOnly
    where
  source :
    G8BookIIICh23FloorNormalizedA15CompactGraphAdjointDomainRealizationSource
  selectedShortcutOnly :
    ¬ source.noSelectedDomainShortcut

theorem
    G8BookIIICh23FloorNormalizedA15CompactGraphRealizationSelectedShortcutOnly.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15CompactGraphRealizationSelectedShortcutOnly) :
    False :=
  gap.selectedShortcutOnly gap.source.noSelectedDomainShortcutWitness

end Tau.BookIII.Bridge
