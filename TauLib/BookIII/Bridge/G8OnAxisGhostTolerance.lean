import TauLib.BookIII.Bridge.G8OffAxisChartGuard

/-!
# TauLib.BookIII.Bridge.G8OnAxisGhostTolerance

On-axis ghost tolerance for the G8 localization route.

The off-axis ghost corridor deliberately does not classify every
receiving-side divisor point.  For RH localization, possible extra or
unclassified receiving-side artifacts on the declared critical axis are outside
the local off-critical exclusion burden.  This module records that tolerance
as a guardrail and splits divisor-difference pressure into on-axis and
off-axis cases.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- ON-AXIS TOLERANCE
-- ============================================================

/-- Localization tolerance for on-axis receiving-side artifacts.

The fields are guard labels, not existence claims.  They state that local
off-critical exclusion does not require classifying on-axis extra zeros,
on-axis multiplicity artifacts, or full receiving-divisor equality. -/
structure G8OnAxisGhostTolerance where
  onAxisExtraReceivingZerosToleratedForLocalization : True := trivial
  onAxisMultiplicityArtifactsToleratedForLocalization : True := trivial
  toleranceIsNotDivisorClassification : True := trivial
  toleranceDoesNotAssertGhostExistence : True := trivial

/-- Default on-axis tolerance guardrail. -/
def defaultG8OnAxisGhostTolerance : G8OnAxisGhostTolerance where
  onAxisExtraReceivingZerosToleratedForLocalization := trivial
  onAxisMultiplicityArtifactsToleratedForLocalization := trivial
  toleranceIsNotDivisorClassification := trivial
  toleranceDoesNotAssertGhostExistence := trivial

/-- The default tolerance record is inhabited in all components. -/
theorem defaultG8OnAxisGhostTolerance_components :
    True ∧ True ∧ True ∧ True :=
  ⟨trivial, trivial, trivial, trivial⟩

-- ============================================================
-- DIVISOR-DIFFERENCE SPLIT
-- ============================================================

/-- Harmless-for-localization on-axis divisor difference.

This records a receiving-side divisor difference whose inspected points for
both candidates remain on the declared critical axis.  It is not a theorem that
the difference is globally harmless; it is a local localization classification. -/
structure G8OnAxisDivisorDifferenceForLocalization
    {ctx : G8cCompletionUniquenessContext}
    (data : G8ReceivingDivisorData ctx) where
  left : ctx.candidateType
  right : ctx.candidateType
  leftPoint : data.divisorCarrier left
  rightPoint : data.divisorCarrier right
  differentData : data.differentDivisorData left right
  leftOnAxis : data.onCriticalAxis left leftPoint
  rightOnAxis : data.onCriticalAxis right rightPoint

/-- Fatal-for-localization off-axis divisor difference.

An off-axis point in the receiving-side divisor data is exactly the pressure
that matters for the one-sided off-critical route. -/
structure G8FatalOffAxisDivisorDifferenceForLocalization
    {ctx : G8cCompletionUniquenessContext}
    (data : G8ReceivingDivisorData ctx) where
  candidate : ctx.candidateType
  point : data.divisorCarrier candidate
  offAxis : ¬ data.onCriticalAxis candidate point

/-- Data-level on-axis divisor differences still project to the base divisor
    difference. -/
theorem g8OnAxisDivisorDifference_to_base
    {ctx : G8cCompletionUniquenessContext}
    {data : G8ReceivingDivisorData ctx}
    (w : G8OnAxisDivisorDifferenceForLocalization data) :
    ctx.differentReceivingDivisor w.left w.right :=
  data.differentDivisorData_to_base w.left w.right w.differentData

/-- A fatal off-axis difference at the selected corridor candidate is the same
    local witness shape used by the one-sided corridor. -/
def g8FatalOffAxisDifference_to_corridorWitness
    {ctx : G8MasterSwitchContext}
    (corridor : G8OneSidedDivisorPullbackCorridor ctx)
    (point :
      corridor.readiness.divisorData.divisorCarrier corridor.candidate)
    (offAxis :
      ¬ corridor.readiness.divisorData.onCriticalAxis
        corridor.candidate point) :
    G8OffAxisReceivingDivisorWitness corridor where
  point := point
  offAxis := offAxis

/-- A fatal off-axis difference at the selected corridor candidate is ruled out
    by the existing one-sided corridor. -/
theorem g8FatalOffAxisDifference_refutes_corridor
    {ctx : G8MasterSwitchContext}
    (corridor : G8OneSidedDivisorPullbackCorridor ctx)
    (point :
      corridor.readiness.divisorData.divisorCarrier corridor.candidate)
    (offAxis :
      ¬ corridor.readiness.divisorData.onCriticalAxis
        corridor.candidate point) :
    False :=
  g8OneSidedCorridor_rulesOut_offAxisDivisor corridor
    ⟨g8FatalOffAxisDifference_to_corridorWitness corridor point offAxis⟩

/-- The on-axis tolerance record exposes that it is not a divisor
    classification theorem. -/
theorem g8OnAxisTolerance_notDivisorClassification
    (tol : G8OnAxisGhostTolerance) :
    True :=
  tol.toleranceIsNotDivisorClassification

end Tau.BookIII.Bridge
