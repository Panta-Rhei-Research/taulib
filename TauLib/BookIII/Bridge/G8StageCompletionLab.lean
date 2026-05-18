import TauLib.BookIII.Bridge.G8StageAwarePullbackTarget

/-!
# TauLib.BookIII.Bridge.G8StageCompletionLab

Stage-indexed G8c non-uniqueness pressure lab for the RH bridge proof
program.

The stage-aware pullback target now carries both the route corridor and the
finite G8a/G8b substrate.  This module uses that handoff shape to name the
next decisive red-team test: a stage-indexed pair of admissible analytic
completion candidates with the same tau tower and finite approximants, but a
different receiving-side divisor.

The module does not prove completion uniqueness.  It only makes the
stage-indexed countermodel pressure executable and routes such a witness back
to the existing G8c falsifier interface.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- STAGE-INDEXED COMPLETION CONTEXT
-- ============================================================

/-- Stage-indexed completion context.

The candidate type is the one already selected by the G8e.4 completion
context.  The stage layer adds a finite support capsule and relation-level
proof fields showing how stage-indexed predicates project to the existing G8c
relations. -/
structure G8StageIndexedCompletionContext
    (ctx : G8MasterSwitchContext) where
  stageSupport : G8PullbackStageSupport
  stageAdmissible :
    (g8e4CompletionContext ctx).candidateType → Prop
  sameStageSubstrate :
    (g8e4CompletionContext ctx).candidateType →
      (g8e4CompletionContext ctx).candidateType → Prop
  sameTauTowerAtStage :
    (g8e4CompletionContext ctx).candidateType →
      (g8e4CompletionContext ctx).candidateType → Prop
  sameFiniteApproximantsAtStage :
    (g8e4CompletionContext ctx).candidateType →
      (g8e4CompletionContext ctx).candidateType → Prop
  differentReceivingDivisorAtStage :
    (g8e4CompletionContext ctx).candidateType →
      (g8e4CompletionContext ctx).candidateType → Prop
  stageAdmissible_to_base :
    ∀ candidate,
      stageAdmissible candidate →
        (g8e4CompletionContext ctx).candidateAdmissible candidate
  sameTauTower_to_base :
    ∀ left right,
      sameTauTowerAtStage left right →
        (g8e4CompletionContext ctx).sameTauTower left right
  sameFiniteApproximants_to_base :
    ∀ left right,
      sameFiniteApproximantsAtStage left right →
        (g8e4CompletionContext ctx).sameFiniteApproximants left right
  differentReceivingDivisor_to_base :
    ∀ left right,
      differentReceivingDivisorAtStage left right →
        (g8e4CompletionContext ctx).differentReceivingDivisor left right

/-- A candidate is admissible for the declared finite stage. -/
def G8StageCompletionAdmissible
    {ctx : G8MasterSwitchContext}
    (lab : G8StageIndexedCompletionContext ctx)
    (candidate : (g8e4CompletionContext ctx).candidateType) : Prop :=
  lab.stageAdmissible candidate

/-- Two candidates share the same finite stage substrate. -/
def G8SameStageSubstrate
    {ctx : G8MasterSwitchContext}
    (lab : G8StageIndexedCompletionContext ctx)
    (left right : (g8e4CompletionContext ctx).candidateType) : Prop :=
  lab.sameStageSubstrate left right

/-- Two candidates share the same tau tower at the declared stage. -/
def G8SameTauTowerAtStage
    {ctx : G8MasterSwitchContext}
    (lab : G8StageIndexedCompletionContext ctx)
    (left right : (g8e4CompletionContext ctx).candidateType) : Prop :=
  lab.sameTauTowerAtStage left right

/-- Two candidates share the same finite approximants at the declared
    stage. -/
def G8SameFiniteApproximantsAtStage
    {ctx : G8MasterSwitchContext}
    (lab : G8StageIndexedCompletionContext ctx)
    (left right : (g8e4CompletionContext ctx).candidateType) : Prop :=
  lab.sameFiniteApproximantsAtStage left right

/-- Two candidates differ in receiving-side divisor at the declared stage. -/
def G8DifferentReceivingDivisorAtStage
    {ctx : G8MasterSwitchContext}
    (lab : G8StageIndexedCompletionContext ctx)
    (left right : (g8e4CompletionContext ctx).candidateType) : Prop :=
  lab.differentReceivingDivisorAtStage left right

-- ============================================================
-- STAGE-INDEXED NONUNIQUENESS WITNESS
-- ============================================================

/-- Stage-indexed non-uniqueness witness.

This is the sharp countermodel shape for the next G8c work: two candidates are
admissible at the same finite substrate, share the same tau tower and finite
approximants, but differ in receiving-side divisor. -/
structure G8StageIndexedNonuniqueCompletionWitness
    {ctx : G8MasterSwitchContext}
    (lab : G8StageIndexedCompletionContext ctx) where
  left : (g8e4CompletionContext ctx).candidateType
  right : (g8e4CompletionContext ctx).candidateType
  leftAdmissible : G8StageCompletionAdmissible lab left
  rightAdmissible : G8StageCompletionAdmissible lab right
  sameStageSubstrate : G8SameStageSubstrate lab left right
  sameTauTower : G8SameTauTowerAtStage lab left right
  sameFinite : G8SameFiniteApproximantsAtStage lab left right
  differentDivisor : G8DifferentReceivingDivisorAtStage lab left right

/-- Non-uniqueness pressure is the existence of a stage-indexed witness. -/
def G8StageIndexedNonuniquenessPressure
    {ctx : G8MasterSwitchContext}
    (lab : G8StageIndexedCompletionContext ctx) : Prop :=
  Nonempty (G8StageIndexedNonuniqueCompletionWitness lab)

/-- Convert a stage-indexed non-uniqueness witness to the existing base G8c
    non-uniqueness witness. -/
def g8StageIndexedWitness_to_base
    {ctx : G8MasterSwitchContext}
    {lab : G8StageIndexedCompletionContext ctx}
    (w : G8StageIndexedNonuniqueCompletionWitness lab) :
    G8cNonuniqueCompletionWitness (g8e4CompletionContext ctx) where
  left := w.left
  right := w.right
  leftAdmissible :=
    lab.stageAdmissible_to_base w.left w.leftAdmissible
  rightAdmissible :=
    lab.stageAdmissible_to_base w.right w.rightAdmissible
  sameTower :=
    lab.sameTauTower_to_base w.left w.right w.sameTauTower
  sameFinite :=
    lab.sameFiniteApproximants_to_base w.left w.right w.sameFinite
  differentDivisor :=
    lab.differentReceivingDivisor_to_base
      w.left w.right w.differentDivisor

/-- Stage-indexed pressure refutes the base G8c no-nonunique-completion
    guardrail. -/
theorem g8StageIndexedPressure_refutes_noNonuniqueCompletion
    {ctx : G8MasterSwitchContext}
    {lab : G8StageIndexedCompletionContext ctx}
    (p : G8StageIndexedNonuniquenessPressure lab) :
    ¬ G8cNoNonuniqueCompletion (g8e4CompletionContext ctx) := by
  intro h
  rcases p with ⟨w⟩
  exact h ⟨g8StageIndexedWitness_to_base w⟩

-- ============================================================
-- REFUTATIONS AGAINST STAGE-AWARE HANDOFF OBJECTS
-- ============================================================

/-- A stage-indexed witness refutes any stage-aware route certificate for the
    same G8 corridor. -/
theorem g8StageIndexedWitness_refutes_stageAwareCertificate
    {ctx : G8MasterSwitchContext}
    {lab : G8StageIndexedCompletionContext ctx}
    (w : G8StageIndexedNonuniqueCompletionWitness lab) :
    ¬ Nonempty (G8StageAwarePullbackRouteCertificate ctx) :=
  g8StageAware_sameTowerDifferentDivisor_refutes_certificate
    ctx (g8StageIndexedWitness_to_base w)

/-- A stage-indexed witness refutes any stage-aware conditional target for the
    same G8 corridor. -/
theorem g8StageIndexedWitness_refutes_stageAwareTarget
    {ctx : G8MasterSwitchContext}
    {lab : G8StageIndexedCompletionContext ctx}
    (w : G8StageIndexedNonuniqueCompletionWitness lab) :
    ¬ Nonempty (G8StageAwareConditionalPullbackTarget ctx) :=
  g8StageAware_sameTowerDifferentDivisor_refutes_target
    ctx (g8StageIndexedWitness_to_base w)

/-- Stage-indexed pressure refutes any stage-aware route certificate for the
    same G8 corridor. -/
theorem g8StageIndexedPressure_refutes_stageAwareCertificate
    {ctx : G8MasterSwitchContext}
    {lab : G8StageIndexedCompletionContext ctx}
    (p : G8StageIndexedNonuniquenessPressure lab) :
    ¬ Nonempty (G8StageAwarePullbackRouteCertificate ctx) := by
  intro h
  rcases p with ⟨w⟩
  exact g8StageIndexedWitness_refutes_stageAwareCertificate w h

/-- Stage-indexed pressure refutes any stage-aware conditional target for the
    same G8 corridor. -/
theorem g8StageIndexedPressure_refutes_stageAwareTarget
    {ctx : G8MasterSwitchContext}
    {lab : G8StageIndexedCompletionContext ctx}
    (p : G8StageIndexedNonuniquenessPressure lab) :
    ¬ Nonempty (G8StageAwareConditionalPullbackTarget ctx) := by
  intro h
  rcases p with ⟨w⟩
  exact g8StageIndexedWitness_refutes_stageAwareTarget w h

-- ============================================================
-- FINITE-ONLY BARRIERS
-- ============================================================

/-- The lab's stage support is finite-only substrate. -/
theorem g8StageCompletionLab_finiteOnly
    {ctx : G8MasterSwitchContext}
    (lab : G8StageIndexedCompletionContext ctx) :
    finiteG8bContext.finiteOnly :=
  g8StageSupport_finiteOnly lab.stageSupport

/-- The lab's stage support carries no xi-divisor claim. -/
theorem g8StageCompletionLab_noXiDivisorClaim
    {ctx : G8MasterSwitchContext}
    (lab : G8StageIndexedCompletionContext ctx) :
    finiteG8bContext.noXiDivisorClaim :=
  g8StageSupport_noXiDivisorClaim lab.stageSupport

/-- The lab's stage support carries no analytic-completion claim. -/
theorem g8StageCompletionLab_noAnalyticCompletionClaim
    {ctx : G8MasterSwitchContext}
    (lab : G8StageIndexedCompletionContext ctx) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8StageSupport_noAnalyticCompletionClaim lab.stageSupport

/-- The lab's finite stage is visible at its primorial support. -/
theorem g8StageCompletionLab_stageVisible
    {ctx : G8MasterSwitchContext}
    (lab : G8StageIndexedCompletionContext ctx) :
    G8aFiniteSupportVisibleAt
      lab.stageSupport.approximant.support.modulus
      lab.stageSupport.approximant.support.stage :=
  g8StageSupport_visibleAtStage lab.stageSupport

/-- The lab's finite stage carries projection compatibility. -/
theorem g8StageCompletionLab_stageProjectionCompatible
    {ctx : G8MasterSwitchContext}
    (lab : G8StageIndexedCompletionContext ctx) (x : Nat) :
    lab.stageSupport.approximant.support.residue
      (PrimorialStageProjection x
        lab.stageSupport.approximant.support.stage) =
      lab.stageSupport.approximant.support.residue x :=
  g8StageSupport_projectionCompatible lab.stageSupport x

/-- Finite-only completion candidates lack chart compatibility. -/
theorem g8StageCompletionLab_finiteOnlyCandidate_not_chartCompatible
    (A D : Type 1) :
    ¬ CompletionCandidateChartCompatible
      (finiteOnlyCompletionCandidate A D) :=
  finiteOnlyCompletionCandidate_not_chartCompatible A D

/-- Finite-only completion candidates lack determinant/O3 compatibility. -/
theorem g8StageCompletionLab_finiteOnlyCandidate_not_determinantCompatible
    (A D : Type 1) :
    ¬ CompletionCandidateDeterminantCompatible
      (finiteOnlyCompletionCandidate A D) :=
  finiteOnlyCompletionCandidate_not_determinantCompatible A D

/-- Finite-only completion candidates are not G8c-admissible analytic
    completions. -/
theorem g8StageCompletionLab_finiteOnlyCandidate_not_admissible
    (A D : Type 1) :
    ¬ CompletionCandidateAdmissible (finiteOnlyCompletionCandidate A D) :=
  finiteOnlyCompletionCandidate_not_admissible A D

/-- A stage-aware target still exposes finite-only substrate. -/
theorem g8StageCompletionLab_target_finiteOnly
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    finiteG8bContext.finiteOnly :=
  g8StageAwareTarget_finiteOnly ctx target

/-- A stage-aware target carries no xi-divisor claim from its finite stage. -/
theorem g8StageCompletionLab_target_noXiDivisorClaim
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    finiteG8bContext.noXiDivisorClaim :=
  g8StageAwareTarget_noXiDivisorClaim ctx target

/-- A stage-aware target carries no analytic-completion claim from its finite
    stage. -/
theorem g8StageCompletionLab_target_noAnalyticCompletionClaim
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8StageAwareTarget_noAnalyticCompletionClaim ctx target

/-- A stage-aware target still carries the finite-only guardrail package. -/
theorem g8StageCompletionLab_target_finiteOnlyGuardrails
    (ctx : G8MasterSwitchContext)
    (target : G8StageAwareConditionalPullbackTarget ctx) :
    G8bFiniteOnlyGuardrails finiteG8bContext :=
  g8StageAwareTarget_finiteOnlyGuardrails ctx target

end Tau.BookIII.Bridge
