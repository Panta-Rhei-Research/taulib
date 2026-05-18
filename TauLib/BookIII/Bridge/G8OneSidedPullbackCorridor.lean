import TauLib.BookIII.Bridge.G8CompletionAdmissibilityLadder

/-!
# TauLib.BookIII.Bridge.G8OneSidedPullbackCorridor

One-sided G8 pullback corridor from receiving-side divisor data to the local
off-critical-zero target.

The admissibility ladder makes clear that finite/tower agreement is not enough
to transport an orthodox zero divisor.  This module adds the next handoff
shape: a stage-aware target, ladder-admissible completion candidate, receiving
divisor data, and an explicit map from off-axis divisor points into the local
orthodox off-critical-zero object.

All conclusions remain conditional on the already-carried G3/G4/G5/G6/G8
obligations.  The module proves only projection and refutation facts.  It does
not construct the analytic chart, does not prove completion uniqueness, and
does not close any global zero-divisor problem.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- ONE-SIDED DIVISOR PULLBACK CORRIDOR
-- ============================================================

/-- One-sided divisor pullback corridor.

The corridor is the exact local target for a future indirect argument: a
receiving-side divisor point for a ladder-admissible candidate is mapped into
the local orthodox-zero object of the stage-aware pullback target.  If that
divisor point is off the critical axis, the supplied map must produce a local
orthodox off-critical zero.

This does not prove such a map exists.  It records the interface a future
bridge theorem must supply. -/
structure G8OneSidedDivisorPullbackCorridor
    (ctx : G8MasterSwitchContext) where
  readiness : G8OneSidedPullbackReadiness ctx
  candidate : (g8e4CompletionContext ctx).candidateType
  candidateAdmissible :
    G8CompletionLadderAdmissible readiness.admissibility candidate
  divisorToOrthodoxZero :
    readiness.divisorData.divisorCarrier candidate →
      ctx.chart.faithfulness.test.base.orthodoxZero
  offAxisDivisor_to_classicalOffCritical :
    ∀ point : readiness.divisorData.divisorCarrier candidate,
      ¬ readiness.divisorData.onCriticalAxis candidate point →
        ClassicalOffCriticalZero ctx.chart.faithfulness.test.base
          (divisorToOrthodoxZero point)

/-- The corridor exposes its stage-aware target. -/
def g8OneSidedCorridor_target
    (ctx : G8MasterSwitchContext)
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) :
    G8StageAwareConditionalPullbackTarget ctx :=
  corridor.readiness.target

/-- The corridor exposes its admissibility ladder. -/
def g8OneSidedCorridor_admissibility
    (ctx : G8MasterSwitchContext)
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) :
    G8CompletionAdmissibilityLadder (g8e4CompletionContext ctx) :=
  corridor.readiness.admissibility

/-- The corridor exposes its same-tower relation ladder. -/
def g8OneSidedCorridor_relations
    (ctx : G8MasterSwitchContext)
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) :
    G8SameTowerRelationLadder (g8e4CompletionContext ctx) :=
  corridor.readiness.relations

/-- The corridor exposes its receiving divisor data. -/
def g8OneSidedCorridor_divisorData
    (ctx : G8MasterSwitchContext)
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) :
    G8ReceivingDivisorData (g8e4CompletionContext ctx) :=
  corridor.readiness.divisorData

/-- The corridor's candidate is admissible in the base G8c context. -/
theorem g8OneSidedCorridor_candidateAdmissible_to_base
    (ctx : G8MasterSwitchContext)
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) :
    (g8e4CompletionContext ctx).candidateAdmissible
      corridor.candidate :=
  g8CompletionLadderAdmissible_to_base corridor.candidateAdmissible

-- ============================================================
-- DEPENDENCY EXPOSURE
-- ============================================================

/-- The corridor still exposes analytic-completion uniqueness as a target
    dependency. -/
theorem g8OneSidedCorridor_requires_completionUnique
    (ctx : G8MasterSwitchContext)
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) :
    tauTower_analyticCompletion_unique (g8e4ZetaChartContext ctx) :=
  g8OneSidedReadiness_requires_completionUnique ctx corridor.readiness

/-- The corridor still exposes the same-xi-divisor dependency. -/
theorem g8OneSidedCorridor_requires_sameXiDivisor
    (ctx : G8MasterSwitchContext)
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) :
    (g8e4ZetaChartContext ctx).sameXiDivisor :=
  g8OneSidedReadiness_requires_sameXiDivisor ctx corridor.readiness

/-- The corridor still exposes no-lost-zero transfer. -/
theorem g8OneSidedCorridor_requires_noLost
    (ctx : G8MasterSwitchContext)
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) :
    (g8e4TransferContext ctx).noLostZeros :=
  g8OneSidedReadiness_requires_noLost ctx corridor.readiness

/-- The corridor still exposes no-spurious-zero transfer. -/
theorem g8OneSidedCorridor_requires_noSpurious
    (ctx : G8MasterSwitchContext)
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) :
    (g8e4TransferContext ctx).noSpuriousZeros :=
  g8OneSidedReadiness_requires_noSpurious ctx corridor.readiness

/-- The corridor still exposes multiplicity preservation. -/
theorem g8OneSidedCorridor_requires_multiplicityPreserved
    (ctx : G8MasterSwitchContext)
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) :
    (g8e4TransferContext ctx).multiplicityPreserved :=
  g8OneSidedReadiness_requires_multiplicityPreserved ctx corridor.readiness

/-- The corridor keeps finite-stage support below xi-divisor claims. -/
theorem g8OneSidedCorridor_noXiDivisorClaim_from_finiteStage
    (ctx : G8MasterSwitchContext)
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) :
    finiteG8bContext.noXiDivisorClaim :=
  g8OneSidedReadiness_noXiDivisorClaim_from_finiteStage
    ctx corridor.readiness

/-- The corridor keeps finite-stage support below analytic-completion
    claims. -/
theorem g8OneSidedCorridor_noAnalyticCompletionClaim_from_finiteStage
    (ctx : G8MasterSwitchContext)
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8OneSidedReadiness_noAnalyticCompletionClaim_from_finiteStage
    ctx corridor.readiness

-- ============================================================
-- OFF-AXIS DIVISOR PRESSURE
-- ============================================================

/-- A receiving-side divisor point declared off the critical axis inside a
    one-sided corridor. -/
structure G8OffAxisReceivingDivisorWitness
    {ctx : G8MasterSwitchContext}
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) where
  point :
    corridor.readiness.divisorData.divisorCarrier corridor.candidate
  offAxis :
    ¬ corridor.readiness.divisorData.onCriticalAxis
      corridor.candidate point

/-- Any off-axis receiving divisor point maps to the local orthodox
    off-critical-zero predicate. -/
theorem g8OffAxisDivisor_to_classicalOffCritical
    {ctx : G8MasterSwitchContext}
    (corridor : G8OneSidedDivisorPullbackCorridor ctx)
    (w : G8OffAxisReceivingDivisorWitness corridor) :
    ClassicalOffCriticalZero ctx.chart.faithfulness.test.base
      (corridor.divisorToOrthodoxZero w.point) :=
  corridor.offAxisDivisor_to_classicalOffCritical w.point w.offAxis

/-- A one-sided corridor rules out off-axis receiving divisor witnesses
    through the local no-off-critical-zero conclusion already carried by its
    stage-aware target. -/
theorem g8OneSidedCorridor_rulesOut_offAxisDivisor
    {ctx : G8MasterSwitchContext}
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) :
    ¬ Nonempty (G8OffAxisReceivingDivisorWitness corridor) := by
  intro h
  rcases h with ⟨w⟩
  have hNoOff :
      G8eNoOrthodoxOffCriticalZeros
        ctx.chart.faithfulness.test.base :=
    g8StageAwareTarget_noOffCriticalZeros ctx corridor.readiness.target
  exact hNoOff (corridor.divisorToOrthodoxZero w.point)
    (g8OffAxisDivisor_to_classicalOffCritical corridor w)

/-- In a one-sided corridor, every receiving divisor point for the selected
    candidate is on the declared critical axis.  This is a local conditional
    consequence of the corridor, not a global divisor theorem. -/
theorem g8OneSidedCorridor_divisorPoint_onCriticalAxis
    {ctx : G8MasterSwitchContext}
    (corridor : G8OneSidedDivisorPullbackCorridor ctx)
    (point :
      corridor.readiness.divisorData.divisorCarrier corridor.candidate) :
    corridor.readiness.divisorData.onCriticalAxis
      corridor.candidate point := by
  by_contra hOff
  exact g8OneSidedCorridor_rulesOut_offAxisDivisor corridor
    ⟨{ point := point, offAxis := hOff }⟩

-- ============================================================
-- COUNTERMODEL PRESSURE AGAINST THE CORRIDOR
-- ============================================================

/-- A full ladder countermodel refutes the one-sided corridor's target. -/
theorem g8LadderCountermodel_refutes_oneSidedCorridor
    {ctx : G8MasterSwitchContext}
    (corridor : G8OneSidedDivisorPullbackCorridor ctx)
    (w : G8LadderCountermodelWitness
      corridor.readiness.admissibility
      corridor.readiness.relations) :
    False :=
  (g8LadderCountermodel_refutes_stageAwareTarget w)
    ⟨corridor.readiness.target⟩

/-- Full ladder countermodel pressure refutes the one-sided corridor's
    target. -/
theorem g8LadderCountermodelPressure_refutes_oneSidedCorridor
    {ctx : G8MasterSwitchContext}
    (corridor : G8OneSidedDivisorPullbackCorridor ctx)
    (p : G8LadderCountermodelPressure
      corridor.readiness.admissibility
      corridor.readiness.relations) :
    False := by
  rcases p with ⟨w⟩
  exact g8LadderCountermodel_refutes_oneSidedCorridor corridor w

/-- A weak same-tower/different-divisor witness exposes finite-stage
    agreement at the base G8c layer. -/
theorem g8WeakWitness_sameFinite_to_base
    {ctx : G8cCompletionUniquenessContext}
    {relations : G8SameTowerRelationLadder ctx}
    (w : G8WeakSameTowerDifferentDivisorWitness relations) :
    ctx.sameFiniteApproximants w.left w.right :=
  g8SameFiniteStageSubstrate_to_base relations w.sameFiniteStage

/-- A weak same-tower/different-divisor witness exposes tau-tower agreement at
    the base G8c layer. -/
theorem g8WeakWitness_sameTower_to_base
    {ctx : G8cCompletionUniquenessContext}
    {relations : G8SameTowerRelationLadder ctx}
    (w : G8WeakSameTowerDifferentDivisorWitness relations) :
    ctx.sameTauTower w.left w.right :=
  g8SamePrimorialTower_to_base relations w.samePrimorialTower

/-- A weak same-tower/different-divisor witness exposes the base divisor
    difference, while still lacking the ladder admissibility needed to become
    a full G8c non-uniqueness witness. -/
theorem g8WeakWitness_differentDivisor
    {ctx : G8cCompletionUniquenessContext}
    {relations : G8SameTowerRelationLadder ctx}
    (w : G8WeakSameTowerDifferentDivisorWitness relations) :
    ctx.differentReceivingDivisor w.left w.right :=
  w.differentDivisor

end Tau.BookIII.Bridge
