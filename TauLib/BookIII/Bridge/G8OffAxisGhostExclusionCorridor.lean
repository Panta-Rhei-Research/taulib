import TauLib.BookIII.Bridge.G8OnAxisGhostTolerance

/-!
# TauLib.BookIII.Bridge.G8OffAxisGhostExclusionCorridor

Packaged off-axis ghost exclusion corridor.

This module is the handoff object for the refined G8 route: off-critical
localization is obtained from an off-axis chart guard, a weak one-sided
pullback test, and tau-side purity.  On-axis receiving-side artifacts remain
tolerated for this local purpose.

The package is intentionally conditional.  It does not classify the full
receiving-side divisor, does not prove analytic completion uniqueness, and does
not assert a global classical result.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- CORRIDOR PACKAGE
-- ============================================================

/-- Off-axis ghost exclusion corridor.

The corridor carries exactly the weak route needed for local off-critical
exclusion:

* a weak pullback-test context;
* off-axis guarded weak subobligations;
* tau-side purity;
* on-axis ghost tolerance guardrails.
-/
structure G8OffAxisGhostExclusionCorridor where
  weakTest : G8WeakOffCriticalPullbackTestContext
  obligations : G8OffAxisGuardedWeakSubobligations weakTest
  tauPurity : G8eTauPurityExcludesOffCritical weakTest.test.base
  onAxisTolerance : G8OnAxisGhostTolerance :=
    defaultG8OnAxisGhostTolerance

/-- The corridor exposes its weak subobligations. -/
def g8OffAxisGhostCorridor_weakSubobligations
    (corridor : G8OffAxisGhostExclusionCorridor) :
    G8WeakOffCriticalPullbackSubobligations corridor.weakTest :=
  g8OffAxisGuarded_to_weakSubobligations
    corridor.weakTest corridor.obligations

/-- The corridor exposes its weak exclusion-transfer context. -/
def g8OffAxisGhostCorridor_exclusionTransferContext
    (corridor : G8OffAxisGhostExclusionCorridor) :
    G8OffCriticalExclusionTransferContext :=
  g8WeakOffCritical_to_exclusionTransferContext
    corridor.weakTest
    (g8OffAxisGhostCorridor_weakSubobligations corridor)
    corridor.tauPurity

/-- The corridor's exclusion-transfer context is admissible. -/
theorem g8OffAxisGhostCorridor_exclusionTransferAdmissible
    (corridor : G8OffAxisGhostExclusionCorridor) :
    G8OffCriticalExclusionTransferAdmissible
      (g8OffAxisGhostCorridor_exclusionTransferContext corridor) :=
  g8WeakOffCritical_exclusionTransferAdmissible
    corridor.weakTest
    (g8OffAxisGhostCorridor_weakSubobligations corridor)
    corridor.tauPurity

/-- The corridor yields the local no-off-critical-zero conclusion. -/
theorem g8OffAxisGhostCorridor_noOffCriticalZeros
    (corridor : G8OffAxisGhostExclusionCorridor) :
    G8eNoOrthodoxOffCriticalZeros corridor.weakTest.test.base :=
  g8OffCriticalExclusion_noOffCriticalZeros
    (g8OffAxisGhostCorridor_exclusionTransferContext corridor)
    (g8OffAxisGhostCorridor_exclusionTransferAdmissible corridor)

-- ============================================================
-- GUARDRAIL SELECTORS
-- ============================================================

/-- The corridor exposes the off-axis chart guard. -/
theorem g8OffAxisGhostCorridor_noOffAxisGhost
    (corridor : G8OffAxisGhostExclusionCorridor) :
    NoChartOnlyOffCriticalZerosOutsideAxis corridor.weakTest.test :=
  corridor.obligations.offAxisGuard

/-- The corridor exposes the derived chart-only guard. -/
theorem g8OffAxisGhostCorridor_noChartOnly
    (corridor : G8OffAxisGhostExclusionCorridor) :
    G8e1NoChartOnlyOffCriticalZero corridor.weakTest.test :=
  g8OffAxisGuard_noChartOnly
    corridor.weakTest.test
    corridor.obligations.localFold
    corridor.obligations.offAxisGuard

/-- An off-axis chart-only ghost is fatal for the corridor. -/
theorem g8OffAxisGhostCorridor_refutes_offAxisGhost
    (corridor : G8OffAxisGhostExclusionCorridor)
    (w : G8OffAxisChartOnlyGhostWitness corridor.weakTest.test) :
    False :=
  corridor.obligations.offAxisGuard ⟨w⟩

/-- The corridor keeps finite-stage support below orthodox zero-divisor
    claims. -/
theorem g8OffAxisGhostCorridor_noXiDivisorClaim_from_finiteStage
    (corridor : G8OffAxisGhostExclusionCorridor) :
    finiteG8bContext.noXiDivisorClaim :=
  g8WeakOffCritical_noXiDivisorClaim_from_finiteStage corridor.weakTest

/-- The corridor keeps finite-stage support below analytic-completion claims. -/
theorem g8OffAxisGhostCorridor_noAnalyticCompletionClaim_from_finiteStage
    (corridor : G8OffAxisGhostExclusionCorridor) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8WeakOffCritical_noAnalyticCompletionClaim_from_finiteStage
    corridor.weakTest

/-- The corridor exposes that on-axis tolerance is not a divisor
    classification theorem. -/
theorem g8OffAxisGhostCorridor_tolerance_notDivisorClassification
    (corridor : G8OffAxisGhostExclusionCorridor) :
    True :=
  g8OnAxisTolerance_notDivisorClassification corridor.onAxisTolerance

/-- The corridor's on-axis tolerance does not assert ghost existence. -/
theorem g8OffAxisGhostCorridor_tolerance_noGhostExistenceClaim
    (corridor : G8OffAxisGhostExclusionCorridor) :
    True :=
  corridor.onAxisTolerance.toleranceDoesNotAssertGhostExistence

end Tau.BookIII.Bridge
