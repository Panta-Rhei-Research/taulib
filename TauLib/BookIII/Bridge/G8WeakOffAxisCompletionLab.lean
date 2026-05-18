import TauLib.BookIII.Bridge.G8StageAwareOffAxisGhostCorridor

/-!
# TauLib.BookIII.Bridge.G8WeakOffAxisCompletionLab

Stage-indexed completion pressure lab for the weak off-axis G8 corridor.

The stage-aware off-axis corridor deliberately avoids full receiving-side
zero-divisor equivalence.  This module therefore sharpens the matching
red-team falsifier: a finite-stage-compatible off-axis receiving shadow with no
tau-native imbalance preimage.

On-axis receiving-side artifacts are recorded only as localization-tolerated
candidates.  They are not asserted to exist, classified, or used as divisor
data.  Finite stage support remains substrate only and carries no xi-divisor or
analytic-completion claim.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- WEAK STAGE-INDEXED COMPLETION CONTEXT
-- ============================================================

/-- Stage-indexed weak completion context for the off-axis corridor.

The context is intentionally weaker than `G8StageIndexedCompletionContext`.
It tracks finite-stage admissibility and same-substrate predicates for the
receiving shadow used by the weak corridor, without requiring full same-xi
divisor, no-lost/no-spurious, or multiplicity transfer data. -/
structure G8WeakOffAxisCompletionContext
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) where
  stageSupport : G8PullbackStageSupport := stageCorridor.stageSupport
  stageAdmissible :
    stageCorridor.corridor.weakTest.test.base.orthodoxZero → Prop
  sameTauTowerSubstrate :
    stageCorridor.corridor.weakTest.test.base.orthodoxZero → Prop
  sameFiniteApproximantSubstrate :
    stageCorridor.corridor.weakTest.test.base.orthodoxZero → Prop
  receivingShadowAdmissible :
    stageCorridor.corridor.weakTest.test.base.orthodoxZero → Prop

/-- Stage admissibility for a weak off-axis completion candidate. -/
def G8WeakOffAxisStageAdmissible
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor)
    (z : stageCorridor.corridor.weakTest.test.base.orthodoxZero) : Prop :=
  lab.stageAdmissible z

/-- The candidate uses the same tau tower substrate at the declared stage. -/
def G8WeakOffAxisSameTauTowerSubstrate
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor)
    (z : stageCorridor.corridor.weakTest.test.base.orthodoxZero) : Prop :=
  lab.sameTauTowerSubstrate z

/-- The candidate uses the same finite approximant substrate at the declared
    stage. -/
def G8WeakOffAxisSameFiniteSubstrate
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor)
    (z : stageCorridor.corridor.weakTest.test.base.orthodoxZero) : Prop :=
  lab.sameFiniteApproximantSubstrate z

/-- The receiving-side shadow is admissible for this weak stage lab. -/
def G8WeakOffAxisReceivingShadowAdmissible
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor)
    (z : stageCorridor.corridor.weakTest.test.base.orthodoxZero) : Prop :=
  lab.receivingShadowAdmissible z

-- ============================================================
-- FATAL OFF-AXIS WITNESS
-- ============================================================

/-- Fatal stage-indexed off-axis ghost witness.

This is the weak-corridor countermodel shape: the candidate is compatible with
the declared finite-stage substrate, presents an orthodox off-critical
receiving shadow, and has no tau-native off-critical preimage. -/
structure G8StageIndexedOffAxisGhostWitness
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor) where
  z : stageCorridor.corridor.weakTest.test.base.orthodoxZero
  stageAdmissible : G8WeakOffAxisStageAdmissible lab z
  sameTauTower : G8WeakOffAxisSameTauTowerSubstrate lab z
  sameFinite : G8WeakOffAxisSameFiniteSubstrate lab z
  shadowAdmissible : G8WeakOffAxisReceivingShadowAdmissible lab z
  offCritical :
    ClassicalOffCriticalZero
      stageCorridor.corridor.weakTest.test.base z
  offAxis :
    ShadowOffAxis
      (stageCorridor.corridor.weakTest.test.orthodoxShadow z)
  noTauImbalancePreimage :
    ∀ w : stageCorridor.corridor.weakTest.test.base.tauWitness,
      ¬ TauOffCriticalWitness
        stageCorridor.corridor.weakTest.test.base w

/-- Convert the stage-indexed witness to the corridor's off-axis chart-only
    ghost witness. -/
def g8StageIndexedOffAxisGhost_to_offAxisChartGhost
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    {lab : G8WeakOffAxisCompletionContext stageCorridor}
    (w : G8StageIndexedOffAxisGhostWitness lab) :
    G8OffAxisChartOnlyGhostWitness
      stageCorridor.corridor.weakTest.test where
  z := w.z
  offCritical := w.offCritical
  offAxis := w.offAxis
  noTauPreimage := w.noTauImbalancePreimage

/-- A fatal stage-indexed off-axis ghost refutes the stage-aware off-axis
    corridor. -/
theorem g8StageIndexedOffAxisGhost_refutes_stageAwareCorridor
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    {lab : G8WeakOffAxisCompletionContext stageCorridor}
    (w : G8StageIndexedOffAxisGhostWitness lab) :
    False :=
  g8StageAwareOffAxisCorridor_refutes_offAxisGhost
    stageCorridor
    (g8StageIndexedOffAxisGhost_to_offAxisChartGhost w)

/-- Existence of a fatal off-axis witness is incompatible with the
    stage-aware corridor. -/
theorem g8StageIndexedOffAxisGhostPressure_refutes_stageAwareCorridor
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    {lab : G8WeakOffAxisCompletionContext stageCorridor}
    (p : Nonempty (G8StageIndexedOffAxisGhostWitness lab)) :
    False := by
  rcases p with ⟨w⟩
  exact g8StageIndexedOffAxisGhost_refutes_stageAwareCorridor w

-- ============================================================
-- ON-AXIS TOLERANCE CANDIDATES
-- ============================================================

/-- Stage-indexed on-axis receiving candidate.

This records the shape of an on-axis receiving-side artifact for localization
bookkeeping only.  It is not a divisor-classification theorem and does not
assert that any such artifact is present in the orthodox object. -/
structure G8StageIndexedOnAxisGhostCandidate
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor) where
  z : stageCorridor.corridor.weakTest.test.base.orthodoxZero
  stageAdmissible : G8WeakOffAxisStageAdmissible lab z
  sameTauTower : G8WeakOffAxisSameTauTowerSubstrate lab z
  sameFinite : G8WeakOffAxisSameFiniteSubstrate lab z
  shadowAdmissible : G8WeakOffAxisReceivingShadowAdmissible lab z
  onAxis :
    OnCriticalAxis
      (stageCorridor.corridor.weakTest.test.orthodoxShadow z)

/-- On-axis candidates are tolerated for the local off-axis localization
    burden. -/
theorem g8StageIndexedOnAxisCandidate_toleratedForLocalization
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    {lab : G8WeakOffAxisCompletionContext stageCorridor}
    (_w : G8StageIndexedOnAxisGhostCandidate lab) :
    True :=
  stageCorridor.corridor.onAxisTolerance.onAxisExtraReceivingZerosToleratedForLocalization

/-- On-axis tolerance is not a receiving-side divisor classification. -/
theorem g8StageIndexedOnAxisCandidate_notDivisorClassification
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    {lab : G8WeakOffAxisCompletionContext stageCorridor}
    (_w : G8StageIndexedOnAxisGhostCandidate lab) :
    True :=
  g8StageAwareOffAxisCorridor_tolerance_notDivisorClassification
    stageCorridor

/-- On-axis tolerance does not assert ghost existence. -/
theorem g8StageIndexedOnAxisCandidate_noGhostExistenceClaim
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    {lab : G8WeakOffAxisCompletionContext stageCorridor}
    (_w : G8StageIndexedOnAxisGhostCandidate lab) :
    True :=
  g8StageAwareOffAxisCorridor_tolerance_noGhostExistenceClaim
    stageCorridor

-- ============================================================
-- FINITE-ONLY GUARDRAILS
-- ============================================================

/-- The weak off-axis lab exposes its finite stage support. -/
def g8WeakOffAxisCompletionLab_stageSupport
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor) :
    G8PullbackStageSupport :=
  lab.stageSupport

/-- The weak off-axis lab's stage support is finite-only substrate. -/
theorem g8WeakOffAxisCompletionLab_finiteOnly
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor) :
    finiteG8bContext.finiteOnly :=
  g8StageSupport_finiteOnly lab.stageSupport

/-- The weak off-axis lab's finite support carries no xi-divisor claim. -/
theorem g8WeakOffAxisCompletionLab_noXiDivisorClaim
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor) :
    finiteG8bContext.noXiDivisorClaim :=
  g8StageSupport_noXiDivisorClaim lab.stageSupport

/-- The weak off-axis lab's finite support carries no analytic-completion
    claim. -/
theorem g8WeakOffAxisCompletionLab_noAnalyticCompletionClaim
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8StageSupport_noAnalyticCompletionClaim lab.stageSupport

/-- The weak off-axis lab's finite stage is visible at its primorial support. -/
theorem g8WeakOffAxisCompletionLab_stageVisible
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor) :
    G8aFiniteSupportVisibleAt
      lab.stageSupport.approximant.support.modulus
      lab.stageSupport.approximant.support.stage :=
  g8StageSupport_visibleAtStage lab.stageSupport

/-- The weak off-axis lab's finite stage carries projection compatibility. -/
theorem g8WeakOffAxisCompletionLab_stageProjectionCompatible
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor)
    (x : Nat) :
    lab.stageSupport.approximant.support.residue
      (PrimorialStageProjection x
        lab.stageSupport.approximant.support.stage) =
      lab.stageSupport.approximant.support.residue x :=
  g8StageSupport_projectionCompatible lab.stageSupport x

/-- The weak off-axis lab exposes the primary finite determinant role. -/
theorem g8WeakOffAxisCompletionLab_primaryFiniteDeterminant
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor) :
    lab.stageSupport.approximant.conventions.role =
      .primaryFiniteDeterminant :=
  g8StageSupport_primaryFiniteDeterminant lab.stageSupport

/-- The weak off-axis lab exposes the finite determinant class. -/
theorem g8WeakOffAxisCompletionLab_finiteDeterminantClass
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor) :
    lab.stageSupport.approximant.conventions.determinantClass =
      .finite :=
  g8StageSupport_finiteDeterminantClass lab.stageSupport

/-- The weak off-axis lab exposes zero-mode exclusion. -/
theorem g8WeakOffAxisCompletionLab_zeroModeExcluded
    {stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor}
    (lab : G8WeakOffAxisCompletionContext stageCorridor) :
    lab.stageSupport.approximant.conventions.zeroModePolicy =
      .excluded :=
  g8StageSupport_zeroModeExcluded lab.stageSupport

/-- The stage-aware corridor itself still exposes finite-only guardrails. -/
theorem g8WeakOffAxisCompletionLab_corridor_finiteOnlyGuardrails
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    G8bFiniteOnlyGuardrails finiteG8bContext :=
  g8StageAwareOffAxisCorridor_finiteOnlyGuardrails stageCorridor

/-- The stage-aware corridor itself carries no xi-divisor claim from finite
    stages. -/
theorem g8WeakOffAxisCompletionLab_corridor_noXiDivisorClaim
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    finiteG8bContext.noXiDivisorClaim :=
  g8StageAwareOffAxisCorridor_noXiDivisorClaim stageCorridor

/-- The stage-aware corridor itself carries no analytic-completion claim from
    finite stages. -/
theorem g8WeakOffAxisCompletionLab_corridor_noAnalyticCompletionClaim
    (stageCorridor : G8StageAwareOffAxisGhostExclusionCorridor) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8StageAwareOffAxisCorridor_noAnalyticCompletionClaim stageCorridor

end Tau.BookIII.Bridge
