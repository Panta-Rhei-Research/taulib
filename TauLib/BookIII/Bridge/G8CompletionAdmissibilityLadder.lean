import TauLib.BookIII.Bridge.G8StageCompletionLab

/-!
# TauLib.BookIII.Bridge.G8CompletionAdmissibilityLadder

Stage-aware G8c admissibility ladder and countermodel harness for the RH
bridge proof program.

The previous stage-completion lab makes the same-stage, same-tower,
different-divisor falsifier target-facing.  This module sharpens the next
question: which compatibility layer blocks that falsifier?

The ladder separates finite-stage agreement from tower agreement, chart
agreement, functional-equation agreement, determinant compatibility, and
receiving-divisor compatibility.  The countermodel harness proves only
refutation and projection facts.  It does not prove analytic-completion
uniqueness, zero-divisor transfer, O3, or any RH statement.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- COMPLETION ADMISSIBILITY LADDER
-- ============================================================

/-- Named compatibility levels for G8c completion candidates.

The order is intentionally diagnostic: weak finite agreement comes first;
receiving-side divisor compatibility is the last and strongest layer. -/
inductive G8CompletionAdmissibilityLevel where
  | finiteStageCompatible
  | tauTowerCompatible
  | zetaChartCompatible
  | functionalEquationCompatible
  | determinantCompatible
  | divisorCompatible
  deriving Repr, DecidableEq

/-- A proof-fielded admissibility ladder over a G8c completion context.

This is the main anti-smuggling object for the next G8 work.  A candidate may
be finite-stage compatible without being a normalized analytic completion; it
may be chart-compatible without yet carrying determinant/O3 compatibility; and
it may pass every earlier layer without yet licensing receiving-side divisor
claims. -/
structure G8CompletionAdmissibilityLadder
    (ctx : G8cCompletionUniquenessContext) where
  finiteStageCompatible : ctx.candidateType → Prop
  tauTowerCompatible : ctx.candidateType → Prop
  zetaChartCompatible : ctx.candidateType → Prop
  functionalEquationCompatible : ctx.candidateType → Prop
  determinantCompatible : ctx.candidateType → Prop
  divisorCompatible : ctx.candidateType → Prop
  fullAdmissible_to_base :
    ∀ candidate,
      finiteStageCompatible candidate →
      tauTowerCompatible candidate →
      zetaChartCompatible candidate →
      functionalEquationCompatible candidate →
      determinantCompatible candidate →
      divisorCompatible candidate →
        ctx.candidateAdmissible candidate

/-- Finite-stage compatibility alone. -/
def G8FiniteStageCompatible
    {ctx : G8cCompletionUniquenessContext}
    (ladder : G8CompletionAdmissibilityLadder ctx)
    (candidate : ctx.candidateType) : Prop :=
  ladder.finiteStageCompatible candidate

/-- Tau-tower compatibility alone. -/
def G8TauTowerCompatible
    {ctx : G8cCompletionUniquenessContext}
    (ladder : G8CompletionAdmissibilityLadder ctx)
    (candidate : ctx.candidateType) : Prop :=
  ladder.tauTowerCompatible candidate

/-- Receiving zeta/xi chart compatibility alone. -/
def G8ZetaChartCompatible
    {ctx : G8cCompletionUniquenessContext}
    (ladder : G8CompletionAdmissibilityLadder ctx)
    (candidate : ctx.candidateType) : Prop :=
  ladder.zetaChartCompatible candidate

/-- Functional-equation compatibility alone. -/
def G8FunctionalEquationCompatible
    {ctx : G8cCompletionUniquenessContext}
    (ladder : G8CompletionAdmissibilityLadder ctx)
    (candidate : ctx.candidateType) : Prop :=
  ladder.functionalEquationCompatible candidate

/-- Determinant/O3 compatibility alone. -/
def G8DeterminantCompatible
    {ctx : G8cCompletionUniquenessContext}
    (ladder : G8CompletionAdmissibilityLadder ctx)
    (candidate : ctx.candidateType) : Prop :=
  ladder.determinantCompatible candidate

/-- Receiving-divisor compatibility alone. -/
def G8DivisorCompatible
    {ctx : G8cCompletionUniquenessContext}
    (ladder : G8CompletionAdmissibilityLadder ctx)
    (candidate : ctx.candidateType) : Prop :=
  ladder.divisorCompatible candidate

/-- Full ladder admissibility: the candidate has passed every compatibility
    layer needed before the base G8c candidate-admissibility predicate may be
    consumed. -/
def G8CompletionLadderAdmissible
    {ctx : G8cCompletionUniquenessContext}
    (ladder : G8CompletionAdmissibilityLadder ctx)
    (candidate : ctx.candidateType) : Prop :=
  G8FiniteStageCompatible ladder candidate ∧
  G8TauTowerCompatible ladder candidate ∧
  G8ZetaChartCompatible ladder candidate ∧
  G8FunctionalEquationCompatible ladder candidate ∧
  G8DeterminantCompatible ladder candidate ∧
  G8DivisorCompatible ladder candidate

/-- Full ladder admissibility projects to the base G8c admissibility
    predicate. -/
theorem g8CompletionLadderAdmissible_to_base
    {ctx : G8cCompletionUniquenessContext}
    {ladder : G8CompletionAdmissibilityLadder ctx}
    {candidate : ctx.candidateType}
    (h : G8CompletionLadderAdmissible ladder candidate) :
    ctx.candidateAdmissible candidate :=
  ladder.fullAdmissible_to_base candidate
    h.left
    h.right.left
    h.right.right.left
    h.right.right.right.left
    h.right.right.right.right.left
    h.right.right.right.right.right

-- ============================================================
-- SAME-TOWER RELATION LADDER
-- ============================================================

/-- Relation ladder for saying that two candidates are "the same" at
    increasingly strong layers.

The weak layers are finite-stage and primorial-tower agreement.  The strong
layers are normalized chart and completed-divisor agreement.  The latter is
allowed to refute a different-divisor claim, but the weak layers are not. -/
structure G8SameTowerRelationLadder
    (ctx : G8cCompletionUniquenessContext) where
  sameFiniteStageSubstrate : ctx.candidateType → ctx.candidateType → Prop
  samePrimorialTower : ctx.candidateType → ctx.candidateType → Prop
  sameLocalEulerData : ctx.candidateType → ctx.candidateType → Prop
  sameNormalizedAnalyticChart : ctx.candidateType → ctx.candidateType → Prop
  sameCompletedXiDivisor : ctx.candidateType → ctx.candidateType → Prop
  sameFiniteStage_to_base :
    ∀ left right,
      sameFiniteStageSubstrate left right →
        ctx.sameFiniteApproximants left right
  samePrimorialTower_to_base :
    ∀ left right,
      samePrimorialTower left right →
        ctx.sameTauTower left right
  sameCompletedXiDivisor_refutes_differentDivisor :
    ∀ left right,
      sameCompletedXiDivisor left right →
        ¬ ctx.differentReceivingDivisor left right

/-- Two candidates share the same finite-stage substrate. -/
def G8SameFiniteStageSubstrate
    {ctx : G8cCompletionUniquenessContext}
    (relations : G8SameTowerRelationLadder ctx)
    (left right : ctx.candidateType) : Prop :=
  relations.sameFiniteStageSubstrate left right

/-- Two candidates share the same primorial/tau tower. -/
def G8SamePrimorialTower
    {ctx : G8cCompletionUniquenessContext}
    (relations : G8SameTowerRelationLadder ctx)
    (left right : ctx.candidateType) : Prop :=
  relations.samePrimorialTower left right

/-- Two candidates share the same local Euler data. -/
def G8SameLocalEulerData
    {ctx : G8cCompletionUniquenessContext}
    (relations : G8SameTowerRelationLadder ctx)
    (left right : ctx.candidateType) : Prop :=
  relations.sameLocalEulerData left right

/-- Two candidates share the same normalized analytic chart. -/
def G8SameNormalizedAnalyticChart
    {ctx : G8cCompletionUniquenessContext}
    (relations : G8SameTowerRelationLadder ctx)
    (left right : ctx.candidateType) : Prop :=
  relations.sameNormalizedAnalyticChart left right

/-- Two candidates share the same completed xi divisor. -/
def G8SameCompletedXiDivisor
    {ctx : G8cCompletionUniquenessContext}
    (relations : G8SameTowerRelationLadder ctx)
    (left right : ctx.candidateType) : Prop :=
  relations.sameCompletedXiDivisor left right

/-- Finite-stage sameness projects to the base finite-approximant relation. -/
theorem g8SameFiniteStageSubstrate_to_base
    {ctx : G8cCompletionUniquenessContext}
    (relations : G8SameTowerRelationLadder ctx)
    {left right : ctx.candidateType}
    (h : G8SameFiniteStageSubstrate relations left right) :
    ctx.sameFiniteApproximants left right :=
  relations.sameFiniteStage_to_base left right h

/-- Primorial-tower sameness projects to the base tau-tower relation. -/
theorem g8SamePrimorialTower_to_base
    {ctx : G8cCompletionUniquenessContext}
    (relations : G8SameTowerRelationLadder ctx)
    {left right : ctx.candidateType}
    (h : G8SamePrimorialTower relations left right) :
    ctx.sameTauTower left right :=
  relations.samePrimorialTower_to_base left right h

/-- Same completed xi divisor blocks the different-divisor falsifier at the
    same pair of candidates. -/
theorem g8SameCompletedXiDivisor_refutes_differentDivisor
    {ctx : G8cCompletionUniquenessContext}
    (relations : G8SameTowerRelationLadder ctx)
    {left right : ctx.candidateType}
    (h : G8SameCompletedXiDivisor relations left right) :
    ¬ ctx.differentReceivingDivisor left right :=
  relations.sameCompletedXiDivisor_refutes_differentDivisor left right h

-- ============================================================
-- RECEIVING DIVISOR DATA INTERFACE
-- ============================================================

/-- Neutral carrier interface for receiving-side divisor data.

This does not construct a classical xi divisor.  It provides the object shape
that later transfer work must instantiate: a carrier of receiving-side zeros,
multiplicity, critical-axis classification, and comparison predicates that
project to the G8c different-divisor relation. -/
structure G8ReceivingDivisorData
    (ctx : G8cCompletionUniquenessContext) where
  divisorCarrier : ctx.candidateType → Type 2
  multiplicity :
    ∀ candidate, divisorCarrier candidate → Nat
  onCriticalAxis :
    ∀ candidate, divisorCarrier candidate → Prop
  sameDivisorData : ctx.candidateType → ctx.candidateType → Prop
  differentDivisorData : ctx.candidateType → ctx.candidateType → Prop
  differentDivisorData_to_base :
    ∀ left right,
      differentDivisorData left right →
        ctx.differentReceivingDivisor left right
  sameDivisorData_refutes_differentData :
    ∀ left right,
      sameDivisorData left right →
        ¬ differentDivisorData left right

/-- Data-level divisor difference projects to the base G8c divisor
    difference. -/
theorem g8DifferentDivisorData_to_base
    {ctx : G8cCompletionUniquenessContext}
    (data : G8ReceivingDivisorData ctx)
    {left right : ctx.candidateType}
    (h : data.differentDivisorData left right) :
    ctx.differentReceivingDivisor left right :=
  data.differentDivisorData_to_base left right h

/-- Data-level divisor sameness refutes data-level divisor difference. -/
theorem g8SameDivisorData_refutes_differentData
    {ctx : G8cCompletionUniquenessContext}
    (data : G8ReceivingDivisorData ctx)
    {left right : ctx.candidateType}
    (h : data.sameDivisorData left right) :
    ¬ data.differentDivisorData left right :=
  data.sameDivisorData_refutes_differentData left right h

-- ============================================================
-- COUNTERMODEL HARNESS
-- ============================================================

/-- Weak countermodel pressure: the finite/tower layers agree while the
    receiving divisor differs.

This is not yet a base G8c non-uniqueness witness, because it carries no
admissibility proof.  It is the standing warning that finite/tower agreement
alone cannot license zero-divisor transfer. -/
structure G8WeakSameTowerDifferentDivisorWitness
    {ctx : G8cCompletionUniquenessContext}
    (relations : G8SameTowerRelationLadder ctx) where
  left : ctx.candidateType
  right : ctx.candidateType
  sameFiniteStage : G8SameFiniteStageSubstrate relations left right
  samePrimorialTower : G8SamePrimorialTower relations left right
  differentDivisor : ctx.differentReceivingDivisor left right

/-- A full ladder countermodel witness: both candidates are ladder-admissible,
    share finite-stage and primorial-tower data, yet differ in receiving-side
    divisor. -/
structure G8LadderCountermodelWitness
    {ctx : G8cCompletionUniquenessContext}
    (ladder : G8CompletionAdmissibilityLadder ctx)
    (relations : G8SameTowerRelationLadder ctx) where
  left : ctx.candidateType
  right : ctx.candidateType
  leftAdmissible : G8CompletionLadderAdmissible ladder left
  rightAdmissible : G8CompletionLadderAdmissible ladder right
  sameFiniteStage : G8SameFiniteStageSubstrate relations left right
  samePrimorialTower : G8SamePrimorialTower relations left right
  differentDivisor : ctx.differentReceivingDivisor left right

/-- A full ladder countermodel is the existence of a ladder witness. -/
def G8LadderCountermodelPressure
    {ctx : G8cCompletionUniquenessContext}
    (ladder : G8CompletionAdmissibilityLadder ctx)
    (relations : G8SameTowerRelationLadder ctx) : Prop :=
  Nonempty (G8LadderCountermodelWitness ladder relations)

/-- Convert a full ladder countermodel to the base G8c non-uniqueness
    witness. -/
def g8LadderCountermodel_to_base
    {ctx : G8cCompletionUniquenessContext}
    {ladder : G8CompletionAdmissibilityLadder ctx}
    {relations : G8SameTowerRelationLadder ctx}
    (w : G8LadderCountermodelWitness ladder relations) :
    G8cNonuniqueCompletionWitness ctx where
  left := w.left
  right := w.right
  leftAdmissible :=
    g8CompletionLadderAdmissible_to_base w.leftAdmissible
  rightAdmissible :=
    g8CompletionLadderAdmissible_to_base w.rightAdmissible
  sameTower :=
    g8SamePrimorialTower_to_base relations w.samePrimorialTower
  sameFinite :=
    g8SameFiniteStageSubstrate_to_base relations w.sameFiniteStage
  differentDivisor := w.differentDivisor

/-- Full ladder countermodel pressure refutes the base no-nonunique-completion
    guardrail. -/
theorem g8LadderCountermodelPressure_refutes_noNonuniqueCompletion
    {ctx : G8cCompletionUniquenessContext}
    {ladder : G8CompletionAdmissibilityLadder ctx}
    {relations : G8SameTowerRelationLadder ctx}
    (p : G8LadderCountermodelPressure ladder relations) :
    ¬ G8cNoNonuniqueCompletion ctx := by
  intro h
  rcases p with ⟨w⟩
  exact h ⟨g8LadderCountermodel_to_base w⟩

/-- Full ladder countermodel pressure refutes G8c transfer admissibility. -/
theorem g8LadderCountermodelPressure_refutes_transfer
    {ctx : G8cCompletionUniquenessContext}
    {ladder : G8CompletionAdmissibilityLadder ctx}
    {relations : G8SameTowerRelationLadder ctx}
    (p : G8LadderCountermodelPressure ladder relations) :
    ¬ G8cZeroDivisorTransferAdmissible ctx := by
  intro h
  exact g8LadderCountermodelPressure_refutes_noNonuniqueCompletion p
    (g8c_transfer_requires_noNonuniqueCompletion ctx h)

/-- A full ladder countermodel refutes any stage-aware certificate over the
    corresponding master-switch context. -/
theorem g8LadderCountermodel_refutes_stageAwareCertificate
    {ctx : G8MasterSwitchContext}
    {ladder : G8CompletionAdmissibilityLadder (g8e4CompletionContext ctx)}
    {relations : G8SameTowerRelationLadder (g8e4CompletionContext ctx)}
    (w : G8LadderCountermodelWitness ladder relations) :
    ¬ Nonempty (G8StageAwarePullbackRouteCertificate ctx) :=
  g8StageAware_sameTowerDifferentDivisor_refutes_certificate
    ctx (g8LadderCountermodel_to_base w)

/-- A full ladder countermodel refutes any stage-aware conditional target over
    the corresponding master-switch context. -/
theorem g8LadderCountermodel_refutes_stageAwareTarget
    {ctx : G8MasterSwitchContext}
    {ladder : G8CompletionAdmissibilityLadder (g8e4CompletionContext ctx)}
    {relations : G8SameTowerRelationLadder (g8e4CompletionContext ctx)}
    (w : G8LadderCountermodelWitness ladder relations) :
    ¬ Nonempty (G8StageAwareConditionalPullbackTarget ctx) :=
  g8StageAware_sameTowerDifferentDivisor_refutes_target
    ctx (g8LadderCountermodel_to_base w)

-- ============================================================
-- ONE-SIDED PULLBACK READINESS
-- ============================================================

/-- Readiness package for later one-sided off-critical pullback work.

This intentionally consumes a stage-aware target plus the stronger
admissibility and relation ladders.  It is the exact handoff shape for a future
attempt to prove that an orthodox off-critical zero must pull back to a
tau-native imbalance. -/
structure G8OneSidedPullbackReadiness
    (ctx : G8MasterSwitchContext) where
  target : G8StageAwareConditionalPullbackTarget ctx
  admissibility :
    G8CompletionAdmissibilityLadder (g8e4CompletionContext ctx)
  relations :
    G8SameTowerRelationLadder (g8e4CompletionContext ctx)
  divisorData :
    G8ReceivingDivisorData (g8e4CompletionContext ctx)

/-- One-sided readiness still exposes analytic-completion uniqueness as a
    target dependency. -/
theorem g8OneSidedReadiness_requires_completionUnique
    (ctx : G8MasterSwitchContext)
    (ready : G8OneSidedPullbackReadiness ctx) :
    tauTower_analyticCompletion_unique (g8e4ZetaChartContext ctx) :=
  g8StageAwareTarget_requires_completionUnique ctx ready.target

/-- One-sided readiness still exposes the same-xi-divisor dependency. -/
theorem g8OneSidedReadiness_requires_sameXiDivisor
    (ctx : G8MasterSwitchContext)
    (ready : G8OneSidedPullbackReadiness ctx) :
    (g8e4ZetaChartContext ctx).sameXiDivisor :=
  g8StageAwareTarget_requires_sameXiDivisor ctx ready.target

/-- One-sided readiness still exposes no-lost-zero transfer. -/
theorem g8OneSidedReadiness_requires_noLost
    (ctx : G8MasterSwitchContext)
    (ready : G8OneSidedPullbackReadiness ctx) :
    (g8e4TransferContext ctx).noLostZeros :=
  g8StageAwareTarget_requires_noLost ctx ready.target

/-- One-sided readiness still exposes no-spurious-zero transfer. -/
theorem g8OneSidedReadiness_requires_noSpurious
    (ctx : G8MasterSwitchContext)
    (ready : G8OneSidedPullbackReadiness ctx) :
    (g8e4TransferContext ctx).noSpuriousZeros :=
  g8StageAwareTarget_requires_noSpurious ctx ready.target

/-- One-sided readiness still exposes multiplicity preservation. -/
theorem g8OneSidedReadiness_requires_multiplicityPreserved
    (ctx : G8MasterSwitchContext)
    (ready : G8OneSidedPullbackReadiness ctx) :
    (g8e4TransferContext ctx).multiplicityPreserved :=
  g8StageAwareTarget_requires_multiplicityPreserved ctx ready.target

/-- One-sided readiness keeps the finite substrate below xi-divisor claims. -/
theorem g8OneSidedReadiness_noXiDivisorClaim_from_finiteStage
    (ctx : G8MasterSwitchContext)
    (ready : G8OneSidedPullbackReadiness ctx) :
    finiteG8bContext.noXiDivisorClaim :=
  g8StageAwareTarget_noXiDivisorClaim ctx ready.target

/-- One-sided readiness keeps the finite substrate below analytic-completion
    claims. -/
theorem g8OneSidedReadiness_noAnalyticCompletionClaim_from_finiteStage
    (ctx : G8MasterSwitchContext)
    (ready : G8OneSidedPullbackReadiness ctx) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8StageAwareTarget_noAnalyticCompletionClaim ctx ready.target

end Tau.BookIII.Bridge
