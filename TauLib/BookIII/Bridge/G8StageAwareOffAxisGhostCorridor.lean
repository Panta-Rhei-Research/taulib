import TauLib.BookIII.Bridge.G8OffAxisGhostExclusionCorridor
import TauLib.BookIII.Bridge.G8StageAwarePullbackAudit

/-!
# TauLib.BookIII.Bridge.G8StageAwareOffAxisGhostCorridor

Stage-aware off-axis ghost exclusion corridor.

The previous off-axis corridor records the refined localization shape: an
orthodox off-critical zero is excluded once it would have to pull back to a
tau-native imbalance witness.  This module attaches the theorem-backed G8a
finite support and finite-only G8b determinant substrate to that weaker route
without reintroducing full receiving-side zero-divisor equivalence.

Everything here is packaging and projection.  It does not prove analytic
completion uniqueness, same-xi-divisor transfer, no-lost/no-spurious transfer,
multiplicity preservation, O3, or any global receiving-side theorem.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- STAGE-AWARE OFF-AXIS CORRIDOR
-- ============================================================

/-- Stage-aware off-axis ghost exclusion corridor.

This is the weak off-axis corridor plus a finite stage-support capsule.  The
finite stage support supplies primorial visibility, projection compatibility,
finite determinant conventions, and finite-only guardrails.  It is substrate
for the route, not a zero-divisor transfer theorem. -/
structure G8StageAwareOffAxisGhostExclusionCorridor where
  corridor : G8OffAxisGhostExclusionCorridor
  stageSupport : G8PullbackStageSupport

/-- Build a stage-aware off-axis corridor from a weak corridor and a chosen
    finite stage/factor family. -/
def g8StageAwareOffAxisGhostExclusionCorridor
    (corridor : G8OffAxisGhostExclusionCorridor)
    (stage : Nat) (factor : Nat → Nat) :
    G8StageAwareOffAxisGhostExclusionCorridor where
  corridor := corridor
  stageSupport := g8PullbackStageSupport stage factor

-- ============================================================
-- LOCAL EXCLUSION SELECTORS
-- ============================================================

/-- The stage-aware corridor exposes its underlying weak corridor. -/
def g8StageAwareOffAxisCorridor_weakCorridor
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    G8OffAxisGhostExclusionCorridor :=
  stageCorridor.corridor

/-- The stage-aware corridor yields the same local no-off-critical-zero
    conclusion as the weak off-axis corridor. -/
theorem g8StageAwareOffAxisCorridor_noOffCriticalZeros
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    G8eNoOrthodoxOffCriticalZeros
      stageCorridor.corridor.weakTest.test.base :=
  g8OffAxisGhostCorridor_noOffCriticalZeros stageCorridor.corridor

/-- The stage-aware corridor exposes the off-axis chart guard. -/
theorem g8StageAwareOffAxisCorridor_noOffAxisGhost
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    NoChartOnlyOffCriticalZerosOutsideAxis
      stageCorridor.corridor.weakTest.test :=
  g8OffAxisGhostCorridor_noOffAxisGhost stageCorridor.corridor

/-- The stage-aware corridor exposes the derived chart-only guard. -/
theorem g8StageAwareOffAxisCorridor_noChartOnly
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    G8e1NoChartOnlyOffCriticalZero
      stageCorridor.corridor.weakTest.test :=
  g8OffAxisGhostCorridor_noChartOnly stageCorridor.corridor

/-- An off-axis chart-only ghost is fatal for the stage-aware corridor. -/
theorem g8StageAwareOffAxisCorridor_refutes_offAxisGhost
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor)
    (w : G8OffAxisChartOnlyGhostWitness
      stageCorridor.corridor.weakTest.test) :
    False :=
  g8OffAxisGhostCorridor_refutes_offAxisGhost
    stageCorridor.corridor w

-- ============================================================
-- STAGE SUBSTRATE SELECTORS
-- ============================================================

/-- The stage-aware off-axis corridor exposes its finite stage support. -/
def g8StageAwareOffAxisCorridor_stageSupport
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    G8PullbackStageSupport :=
  stageCorridor.stageSupport

/-- The finite stage is visible at its primorial stage. -/
theorem g8StageAwareOffAxisCorridor_stageVisible
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    G8aFiniteSupportVisibleAt
      stageCorridor.stageSupport.approximant.support.modulus
      stageCorridor.stageSupport.approximant.support.stage :=
  g8StageSupport_visibleAtStage stageCorridor.stageSupport

/-- The finite stage carries projection compatibility. -/
theorem g8StageAwareOffAxisCorridor_stageProjectionCompatible
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor)
    (x : Nat) :
    stageCorridor.stageSupport.approximant.support.residue
      (PrimorialStageProjection x
        stageCorridor.stageSupport.approximant.support.stage) =
      stageCorridor.stageSupport.approximant.support.residue x :=
  g8StageSupport_projectionCompatible stageCorridor.stageSupport x

/-- The finite stage uses the primary finite determinant role. -/
theorem g8StageAwareOffAxisCorridor_primaryFiniteDeterminant
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    stageCorridor.stageSupport.approximant.conventions.role =
      .primaryFiniteDeterminant :=
  g8StageSupport_primaryFiniteDeterminant stageCorridor.stageSupport

/-- The finite stage uses the finite determinant class. -/
theorem g8StageAwareOffAxisCorridor_finiteDeterminantClass
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    stageCorridor.stageSupport.approximant.conventions.determinantClass =
      .finite :=
  g8StageSupport_finiteDeterminantClass stageCorridor.stageSupport

/-- The finite stage excludes the zero mode. -/
theorem g8StageAwareOffAxisCorridor_zeroModeExcluded
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    stageCorridor.stageSupport.approximant.conventions.zeroModePolicy =
      .excluded :=
  g8StageSupport_zeroModeExcluded stageCorridor.stageSupport

/-- The finite stage carries the finite-only G8b guardrails. -/
theorem g8StageAwareOffAxisCorridor_finiteOnlyGuardrails
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    G8bFiniteOnlyGuardrails finiteG8bContext :=
  g8StageSupport_finiteOnlyGuardrails stageCorridor.stageSupport

/-- The finite stage is finite-only. -/
theorem g8StageAwareOffAxisCorridor_finiteOnly
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    finiteG8bContext.finiteOnly :=
  g8StageSupport_finiteOnly stageCorridor.stageSupport

/-- The finite stage carries no xi-divisor claim. -/
theorem g8StageAwareOffAxisCorridor_noXiDivisorClaim
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    finiteG8bContext.noXiDivisorClaim :=
  g8StageSupport_noXiDivisorClaim stageCorridor.stageSupport

/-- The finite stage carries no analytic-completion claim. -/
theorem g8StageAwareOffAxisCorridor_noAnalyticCompletionClaim
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8StageSupport_noAnalyticCompletionClaim stageCorridor.stageSupport

-- ============================================================
-- ON-AXIS TOLERANCE SELECTORS
-- ============================================================

/-- The stage-aware corridor preserves that on-axis tolerance is not a divisor
    classification theorem. -/
theorem g8StageAwareOffAxisCorridor_tolerance_notDivisorClassification
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    True :=
  g8OffAxisGhostCorridor_tolerance_notDivisorClassification
    stageCorridor.corridor

/-- The stage-aware corridor preserves that on-axis tolerance does not assert
    ghost existence. -/
theorem g8StageAwareOffAxisCorridor_tolerance_noGhostExistenceClaim
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    True :=
  g8OffAxisGhostCorridor_tolerance_noGhostExistenceClaim
    stageCorridor.corridor

end Tau.BookIII.Bridge
