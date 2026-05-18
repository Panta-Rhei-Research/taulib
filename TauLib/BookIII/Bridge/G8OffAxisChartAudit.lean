import TauLib.BookIII.Bridge.G8OffAxisChartObject

/-!
# TauLib.BookIII.Bridge.G8OffAxisChartAudit

Audit surface for the explicit G8 off-axis chart corridor.

`G8OffAxisChartObject` introduced the centered chart object and its
faithfulness interface.  This module makes that object convenient for the next
proof wave by packaging the exact selectors a downstream theorem should
consume:

* centered chart and relation fields;
* local fold readability and chart faithfulness;
* finite-stage G8a/G8b substrate guardrails;
* on-axis tolerance versus fatal off-axis pressure;
* direct refutations of the no-preimage, balanced-preimage, chart-only, and
  stage-indexed off-axis ghost falsifiers.

The audit remains an interface.  It does not prove analytic-completion
uniqueness, full zero-divisor transfer, O3, or the classical RH target.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- AUDIT PACKAGE
-- ============================================================

/-- Compact audit object for the explicit off-axis chart corridor. -/
structure G8OffAxisChartAudit where
  stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor
  corridor : G8StageAwareOffAxisChartCorridor stageCorridor

/-- The weak off-axis pullback test audited by this package. -/
def g8OffAxisChartAudit_weakTest
    (audit : G8OffAxisChartAudit) :
    G8WeakOffCriticalPullbackTestContext :=
  audit.stageCorridor.corridor.weakTest

/-- The finite/tower completion lab audited by this package. -/
def g8OffAxisChartAudit_lab
    (audit : G8OffAxisChartAudit) :
    G8WeakOffAxisCompletionContext audit.stageCorridor :=
  audit.corridor.lab

/-- The explicit centered chart object audited by this package. -/
def g8OffAxisChartAudit_chart
    (audit : G8OffAxisChartAudit) :
    G8OffAxisChartObject audit.stageCorridor.corridor.weakTest :=
  audit.corridor.chart

/-- The explicit chart-faithfulness proof-field object audited here. -/
def g8OffAxisChartAudit_faithfulness
    (audit : G8OffAxisChartAudit) :
    G8OffAxisChartFaithfulnessObject audit.corridor.chart :=
  audit.corridor.faithfulness

/-- The chart relation between receiving shadows and tau-side witnesses. -/
def g8OffAxisChartAudit_shadowTauRelated
    (audit : G8OffAxisChartAudit) :
    audit.stageCorridor.corridor.weakTest.test.base.orthodoxZero →
      audit.stageCorridor.corridor.weakTest.test.base.tauWitness → Prop :=
  audit.corridor.faithfulness.shadowTauRelated

-- ============================================================
-- CHART AND FAITHFULNESS SELECTORS
-- ============================================================

/-- The audit exposes local fold readability. -/
theorem g8OffAxisChartAudit_localFold
    (audit : G8OffAxisChartAudit) :
    G8e1LocalFoldReadable
      audit.stageCorridor.corridor.weakTest.test :=
  g8OffAxisChartObject_localFold
    audit.stageCorridor.corridor.weakTest
    audit.corridor.chart

/-- The audit exposes the chart-faithfulness predicate consumed by the weak
    pullback route. -/
theorem g8OffAxisChartAudit_chartFaithful
    (audit : G8OffAxisChartAudit) :
    G8e1ChartFaithfulToTauImbalance
      audit.stageCorridor.corridor.weakTest.test :=
  g8WeakOffAxisRealization_chartFaithful
    audit.stageCorridor.corridor.weakTest
    (g8OffAxisChartFaithfulnessObject_to_realization
      audit.stageCorridor.corridor.weakTest
      audit.corridor.chart
      audit.corridor.faithfulness)

/-- Off-axis chart data gives a related tau preimage. -/
theorem g8OffAxisChartAudit_offAxisHasTauPreimage
    (audit : G8OffAxisChartAudit)
    (z : audit.stageCorridor.corridor.weakTest.test.base.orthodoxZero)
    (hOffAxis : G8ChartOffAxis audit.corridor.chart z) :
    ∃ w : audit.stageCorridor.corridor.weakTest.test.base.tauWitness,
      audit.corridor.faithfulness.shadowTauRelated z w :=
  audit.corridor.faithfulness.offAxisHasTauPreimage z hOffAxis

/-- Related off-axis tau preimages carry B-C imbalance. -/
theorem g8OffAxisChartAudit_relatedPreimageCarriesBCImbalance
    (audit : G8OffAxisChartAudit)
    (z : audit.stageCorridor.corridor.weakTest.test.base.orthodoxZero)
    (w : audit.stageCorridor.corridor.weakTest.test.base.tauWitness)
    (hOffAxis : G8ChartOffAxis audit.corridor.chart z)
    (hRel : audit.corridor.faithfulness.shadowTauRelated z w) :
    TauBCImbalance
      (audit.stageCorridor.corridor.weakTest.test.tauNormalForm w) :=
  audit.corridor.faithfulness.relatedPreimageCarriesBCImbalance
    z w hOffAxis hRel

/-- Related off-axis tau preimages also carry the corridor's tau-critical
    imbalance form. -/
theorem g8OffAxisChartAudit_relatedPreimageCarriesTauImbalance
    (audit : G8OffAxisChartAudit)
    (z : audit.stageCorridor.corridor.weakTest.test.base.orthodoxZero)
    (w : audit.stageCorridor.corridor.weakTest.test.base.tauWitness)
    (hOffAxis : G8ChartOffAxis audit.corridor.chart z)
    (hRel : audit.corridor.faithfulness.shadowTauRelated z w) :
    TauCriticalImbalance
      (audit.stageCorridor.corridor.weakTest.test.tauNormalForm w) :=
  (tauCriticalImbalance_iff_bcImbalance
    (audit.stageCorridor.corridor.weakTest.test.tauNormalForm w)).mpr
    (g8OffAxisChartAudit_relatedPreimageCarriesBCImbalance
      audit z w hOffAxis hRel)

/-- The audit exposes the one-sided pullback conclusion. -/
theorem g8OffAxisChartAudit_yields_pullback
    (audit : G8OffAxisChartAudit) :
    G8eOffCriticalPullback
      audit.stageCorridor.corridor.weakTest.test.base :=
  g8OffAxisChartFaithfulnessObject_yields_pullback
    audit.stageCorridor.corridor.weakTest
    audit.corridor.chart
    audit.corridor.faithfulness

/-- The audit exposes the local no-off-critical-zero conclusion already
    guarded by the stage corridor's tau purity. -/
theorem g8OffAxisChartAudit_noOffCriticalZeros
    (audit : G8OffAxisChartAudit) :
    G8eNoOrthodoxOffCriticalZeros
      audit.stageCorridor.corridor.weakTest.test.base :=
  g8StageAwareOffAxisChartCorridor_noOffCriticalZeros
    audit.corridor

-- ============================================================
-- FINITE-STAGE GUARDRAILS
-- ============================================================

/-- The audit exposes its finite stage support. -/
def g8OffAxisChartAudit_stageSupport
    (audit : G8OffAxisChartAudit) :
    G8PullbackStageSupport :=
  g8StageAwareOffAxisChartCorridor_stageSupport audit.corridor

/-- Finite stages remain finite-only substrate. -/
theorem g8OffAxisChartAudit_finiteOnly
    (audit : G8OffAxisChartAudit) :
    finiteG8bContext.finiteOnly :=
  g8StageAwareOffAxisChartCorridor_finiteOnly audit.corridor

/-- Finite stages carry no xi-divisor claim. -/
theorem g8OffAxisChartAudit_noXiDivisorClaim
    (audit : G8OffAxisChartAudit) :
    finiteG8bContext.noXiDivisorClaim :=
  g8StageAwareOffAxisChartCorridor_noXiDivisorClaim audit.corridor

/-- Finite stages carry no analytic-completion claim. -/
theorem g8OffAxisChartAudit_noAnalyticCompletionClaim
    (audit : G8OffAxisChartAudit) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8StageAwareOffAxisChartCorridor_noAnalyticCompletionClaim audit.corridor

/-- The finite stage is visible at its primorial support. -/
theorem g8OffAxisChartAudit_stageVisible
    (audit : G8OffAxisChartAudit) :
    G8aFiniteSupportVisibleAt
      audit.corridor.lab.stageSupport.approximant.support.modulus
      audit.corridor.lab.stageSupport.approximant.support.stage :=
  g8WeakOffAxisCompletionLab_stageVisible audit.corridor.lab

/-- The finite stage projection is compatible with the declared support. -/
theorem g8OffAxisChartAudit_stageProjectionCompatible
    (audit : G8OffAxisChartAudit)
    (x : Nat) :
    audit.corridor.lab.stageSupport.approximant.support.residue
      (PrimorialStageProjection x
        audit.corridor.lab.stageSupport.approximant.support.stage) =
      audit.corridor.lab.stageSupport.approximant.support.residue x :=
  g8WeakOffAxisCompletionLab_stageProjectionCompatible
    audit.corridor.lab x

/-- The audit exposes that the primary finite approximant is the finite
    determinant scaffold. -/
theorem g8OffAxisChartAudit_primaryFiniteDeterminant
    (audit : G8OffAxisChartAudit) :
    audit.corridor.lab.stageSupport.approximant.conventions.role =
      .primaryFiniteDeterminant :=
  g8WeakOffAxisCompletionLab_primaryFiniteDeterminant audit.corridor.lab

/-- The audit exposes the finite determinant class. -/
theorem g8OffAxisChartAudit_finiteDeterminantClass
    (audit : G8OffAxisChartAudit) :
    audit.corridor.lab.stageSupport.approximant.conventions.determinantClass =
      .finite :=
  g8WeakOffAxisCompletionLab_finiteDeterminantClass audit.corridor.lab

/-- The audit exposes finite zero-mode exclusion. -/
theorem g8OffAxisChartAudit_zeroModeExcluded
    (audit : G8OffAxisChartAudit) :
    audit.corridor.lab.stageSupport.approximant.conventions.zeroModePolicy =
      .excluded :=
  g8WeakOffAxisCompletionLab_zeroModeExcluded audit.corridor.lab

/-- Compact guardrail selector: finite stages carry neither xi-divisor nor
    analytic-completion claims. -/
theorem g8OffAxisChartAudit_noFiniteDivisorOrCompletionClaim
    (audit : G8OffAxisChartAudit) :
    finiteG8bContext.noXiDivisorClaim ∧
      finiteG8bContext.noAnalyticCompletionClaim :=
  ⟨
    g8OffAxisChartAudit_noXiDivisorClaim audit,
    g8OffAxisChartAudit_noAnalyticCompletionClaim audit
  ⟩

-- ============================================================
-- ON-AXIS / OFF-AXIS SPLIT
-- ============================================================

/-- On-axis candidates remain tolerated only for localization bookkeeping. -/
theorem g8OffAxisChartAudit_onAxisCandidateTolerated
    (audit : G8OffAxisChartAudit)
    (w : G8StageIndexedOnAxisGhostCandidate audit.corridor.lab) :
    True :=
  g8StageIndexedOnAxisCandidate_toleratedForLocalization w

/-- On-axis tolerance is not a divisor-classification theorem. -/
theorem g8OffAxisChartAudit_onAxisCandidate_notDivisorClassification
    (audit : G8OffAxisChartAudit)
    (w : G8StageIndexedOnAxisGhostCandidate audit.corridor.lab) :
    True :=
  g8StageIndexedOnAxisCandidate_notDivisorClassification w

/-- On-axis tolerance does not assert ghost existence. -/
theorem g8OffAxisChartAudit_onAxisCandidate_noGhostExistenceClaim
    (audit : G8OffAxisChartAudit)
    (w : G8StageIndexedOnAxisGhostCandidate audit.corridor.lab) :
    True :=
  g8StageIndexedOnAxisCandidate_noGhostExistenceClaim w

/-- Explicit off-axis chart data for the same point refutes an on-axis
    tolerance candidate. -/
theorem g8OffAxisChartAudit_offAxis_refutes_onAxisCandidate
    (audit : G8OffAxisChartAudit)
    (w : G8StageIndexedOnAxisGhostCandidate audit.corridor.lab)
    (hOffAxis : G8ChartOffAxis audit.corridor.chart w.z) :
    False :=
  g8ChartOffAxis_refutes_stageIndexedOnAxisCandidate
    audit.corridor.chart w hOffAxis

-- ============================================================
-- FALSIFIER REFUTATIONS
-- ============================================================

/-- An unreadable off-critical shadow refutes the audit. -/
theorem g8OffAxisChartAudit_refutes_unreadableShadow
    (audit : G8OffAxisChartAudit)
    (w :
      G8UnreadableOffCriticalShadowWitness
        audit.stageCorridor.corridor.weakTest) :
    False :=
  (g8UnreadableOffCriticalShadow_refutes_core
    audit.stageCorridor.corridor.weakTest w)
    ⟨g8OffAxisChartFaithfulnessObject_to_core
      audit.stageCorridor.corridor.weakTest
      audit.corridor.chart
      audit.corridor.faithfulness⟩

/-- A no-related-preimage witness refutes the audit. -/
theorem g8OffAxisChartAudit_refutes_noPreimage
    (audit : G8OffAxisChartAudit)
    (w :
      G8NoTauPreimageForOffAxisShadowWitness
        audit.stageCorridor.corridor.weakTest
        audit.corridor.faithfulness.shadowTauRelated) :
    False :=
  g8NoTauPreimageForOffAxisShadow_refutes_core
    audit.stageCorridor.corridor.weakTest
    (g8OffAxisChartFaithfulnessObject_to_core
      audit.stageCorridor.corridor.weakTest
      audit.corridor.chart
      audit.corridor.faithfulness)
    w

/-- A B-C-balanced related preimage refutes the audit. -/
theorem g8OffAxisChartAudit_refutes_balancedRelatedPreimage
    (audit : G8OffAxisChartAudit)
    (w :
      G8OffAxisRelatedPreimageBCBalancedWitness
        audit.stageCorridor.corridor.weakTest
        audit.corridor.faithfulness.shadowTauRelated) :
    False :=
  g8OffAxisBCBalanced_refutes_core
    audit.stageCorridor.corridor.weakTest
    (g8OffAxisChartFaithfulnessObject_to_core
      audit.stageCorridor.corridor.weakTest
      audit.corridor.chart
      audit.corridor.faithfulness)
    w

/-- A chart-only off-axis ghost refutes the audit. -/
theorem g8OffAxisChartAudit_refutes_chartOnlyGhost
    (audit : G8OffAxisChartAudit)
    (w :
      G8OffAxisChartOnlyGhostWitness
        audit.stageCorridor.corridor.weakTest.test) :
    False :=
  g8OffAxisChartOnlyGhost_refutes_core
    audit.stageCorridor.corridor.weakTest
    (g8OffAxisChartFaithfulnessObject_to_core
      audit.stageCorridor.corridor.weakTest
      audit.corridor.chart
      audit.corridor.faithfulness)
    w

/-- The weak completion lab's stage-indexed off-axis ghost refutes the audit. -/
theorem g8OffAxisChartAudit_refutes_stageIndexedOffAxisGhost
    (audit : G8OffAxisChartAudit)
    (w : G8StageIndexedOffAxisGhostWitness audit.corridor.lab) :
    False :=
  g8StageIndexedOffAxisGhost_refutes_chartCorridor w

/-- The relation-level chart-faithfulness failure refutes the audit. -/
theorem g8OffAxisChartAudit_refutes_chartFaithfulnessFailure
    (audit : G8OffAxisChartAudit)
    (w :
      G8StageIndexedOffAxisChartFaithfulnessFailure audit.corridor) :
    False :=
  g8StageIndexedChartFaithfulnessFailure_refutes_corridor w

end Tau.BookIII.Bridge
