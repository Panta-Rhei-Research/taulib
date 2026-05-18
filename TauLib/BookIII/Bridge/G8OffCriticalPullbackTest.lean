import TauLib.BookIII.Bridge.G8OffCriticalPullback

/-!
# TauLib.BookIII.Bridge.G8OffCriticalPullbackTest

G8e.1 test context for the off-critical pullback route.

The preceding G8e interface states the indirect contradiction route in one
piece.  This module splits that route into the smaller obligations we actually
need to inspect:

* local fold readability: an orthodox off-critical zero has an off-axis shadow;
* chart faithfulness: an off-axis shadow reflects to a tau imbalance witness;
* witness realization: that tau imbalance is accepted as the tau-side witness
  in the G8e context;
* transfer discipline: the G8d/G8c zero-divisor stack is still explicit;
* chart-only off-critical zeros remain the standing falsifier.

This is a proof-engineering test harness.  It does not prove the pullback
obligation from analytic data, does not remove the G8c uniqueness problem, and
does not assert any global RH result.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- LOCAL SHADOW AND TAU-IMBALANCE PREDICATES
-- ============================================================

/-- Off-axis predicate in the centered receiving-side shadow model. -/
def ShadowOffAxis (p : CriticalAxisShadow) : Prop :=
  ¬ OnCriticalAxis p

/-- Fold obstruction predicate in the centered receiving-side shadow model. -/
def ShadowFoldObstruction (p : CriticalAxisShadow) : Prop :=
  ¬ FoldLooksReal p

/-- The local fold lemma turns off-axis shadow data into the same obstruction
    recorded by the quadratic spectral fold.  This is purely local algebraic
    bookkeeping; it contains no zero-divisor content. -/
theorem shadowOffAxis_iff_foldObstruction
    (p : CriticalAxisShadow) :
    ShadowOffAxis p ↔ ShadowFoldObstruction p := by
  unfold ShadowOffAxis ShadowFoldObstruction
  constructor
  · intro hAxis hFold
    exact hAxis ((CriticalAxisSpectralFold p).mp hFold)
  · intro hFold hAxis
    exact hFold ((CriticalAxisSpectralFold p).mpr hAxis)

/-- Tau-native off-criticality as failure of the tau critical locus. -/
def TauCriticalImbalance (nf : BoundaryNF) : Prop :=
  ¬ TauCriticalLocus nf

/-- Tau-native B/C imbalance as failure of B/C balance. -/
def TauBCImbalance (nf : BoundaryNF) : Prop :=
  ¬ BCBalanced nf

/-- Critical-locus imbalance and B/C imbalance are the same tau-native
    obstruction, by the already-proved fixed-locus characterization. -/
theorem tauCriticalImbalance_iff_bcImbalance
    (nf : BoundaryNF) :
    TauCriticalImbalance nf ↔ TauBCImbalance nf := by
  unfold TauCriticalImbalance TauBCImbalance
  constructor
  · intro hCrit hBC
    exact hCrit ((tauCriticalLocus_iff_bcBalanced nf).mpr hBC)
  · intro hBC hCrit
    exact hBC ((tauCriticalLocus_iff_bcBalanced nf).mp hCrit)

-- ============================================================
-- G8E.1 TEST CONTEXT
-- ============================================================

/-- Diagnostic status labels for the G8e.1 pullback reduction. -/
inductive OffCriticalPullbackTestStatus where
  | openTest
  | localFoldOnly
  | chartFaithfulnessNeeded
  | transferDisciplineNeeded
  | chartOnlyFalsifierOpen
  | conditionalPullbackAvailable
  deriving Repr, DecidableEq

/-- G8e.1 test context.

`orthodoxShadow` is the centered receiving-side shadow attached to an
orthodox zero candidate.  `tauNormalForm` is the tau-native boundary normal
form attached to a tau-side witness candidate.  The module does not construct
either map; it names the proof obligations needed for the pullback route to
be meaningful. -/
structure OffCriticalPullbackTestContext where
  base : OffCriticalZeroPullbackContext
  orthodoxShadow : base.orthodoxZero → CriticalAxisShadow
  tauNormalForm : base.tauWitness → BoundaryNF
  status : OffCriticalPullbackTestStatus := .openTest

/-- Local fold readability: every declared orthodox off-critical zero has an
    off-axis centered shadow. -/
def G8e1LocalFoldReadable
    (ctx : OffCriticalPullbackTestContext) : Prop :=
  ∀ z : ctx.base.orthodoxZero,
    ClassicalOffCriticalZero ctx.base z →
      ShadowOffAxis (ctx.orthodoxShadow z)

/-- Chart faithfulness in the one-sided direction needed for contradiction:
    every off-axis centered shadow reflects to a tau-native imbalance witness.

This is the decisive new test.  If it fails, the indirect route has not escaped
the G8 chart-only-zero obstruction. -/
def G8e1ChartFaithfulToTauImbalance
    (ctx : OffCriticalPullbackTestContext) : Prop :=
  ∀ z : ctx.base.orthodoxZero,
    ShadowOffAxis (ctx.orthodoxShadow z) →
      ∃ w : ctx.base.tauWitness,
        TauCriticalImbalance (ctx.tauNormalForm w)

/-- Tau witness realization: the tau-native imbalance produced by the chart
    faithfulness step is accepted as the tau-side off-critical witness in the
    original G8e context. -/
def G8e1TauImbalanceRealizesWitness
    (ctx : OffCriticalPullbackTestContext) : Prop :=
  ∀ w : ctx.base.tauWitness,
    TauCriticalImbalance (ctx.tauNormalForm w) →
      TauOffCriticalWitness ctx.base w

/-- Standing red-team guardrail for this test context: no chart-only
    off-critical-zero witness is available in the underlying G8e context. -/
def G8e1NoChartOnlyOffCriticalZero
    (ctx : OffCriticalPullbackTestContext) : Prop :=
  ¬ Nonempty (ChartOnlyOffCriticalZeroWitness ctx.base)

/-- The sub-obligation package that turns the G8e pullback route from one
    opaque obligation into inspectable pieces. -/
structure G8e1PullbackSubobligations
    (ctx : OffCriticalPullbackTestContext) where
  transfer : G8dZeroDivisorTransferAdmissible ctx.base.transfer
  localFold : G8e1LocalFoldReadable ctx
  chartFaithful : G8e1ChartFaithfulToTauImbalance ctx
  tauWitness : G8e1TauImbalanceRealizesWitness ctx
  noChartOnly : G8e1NoChartOnlyOffCriticalZero ctx

/-- The G8e.1 sub-obligations imply the original one-sided pullback obligation.

This is the central test-context theorem.  It does not prove the
sub-obligations; it proves that they are sufficient and correctly factored. -/
theorem g8e1_subobligations_yield_pullback
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    G8eOffCriticalPullback ctx.base := by
  intro z hz
  have hShadow : ShadowOffAxis (ctx.orthodoxShadow z) :=
    h.localFold z hz
  obtain ⟨w, hImbalance⟩ := h.chartFaithful z hShadow
  exact ⟨w, h.tauWitness w hImbalance⟩

/-- The sub-obligation package exposes the G8d transfer discipline. -/
theorem g8e1_subobligations_require_g8d
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    G8dZeroDivisorTransferAdmissible ctx.base.transfer :=
  h.transfer

/-- The sub-obligation package exposes the G8c completion/uniqueness guard. -/
theorem g8e1_subobligations_require_g8c
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    G8cZeroDivisorTransferAdmissible ctx.base.transfer.completion :=
  g8d_transfer_requires_g8c ctx.base.transfer h.transfer

/-- The sub-obligation package still depends on analytic-completion uniqueness
    from the zeta-as-chart context. -/
theorem g8e1_subobligations_require_completionUnique
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    tauTower_analyticCompletion_unique
      ctx.base.transfer.completion.chart :=
  g8c_transfer_requires_completionUnique
    ctx.base.transfer.completion
    (g8e1_subobligations_require_g8c ctx h)

/-- The sub-obligation package still depends on same-divisor discipline from
    the zeta-as-chart context. -/
theorem g8e1_subobligations_require_sameXiDivisor
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    ctx.base.transfer.completion.chart.sameXiDivisor :=
  zeroDivisorClaimsAdmissible_sameXiDivisor
    ctx.base.transfer.completion.chart
    (g8e1_subobligations_require_g8c ctx h).left

/-- The G8e.1 package still depends on the G3 zeta bridge obligation. -/
theorem g8e1_subobligations_require_g3ZetaBridge
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    ctx.base.transfer.completion.chart.g3ZetaBridge :=
  g8d_transfer_requires_g3ZetaBridge ctx.base.transfer h.transfer

/-- The G8e.1 package still depends on the G4 analytic-continuation obligation. -/
theorem g8e1_subobligations_require_g4AnalyticContinuation
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    ctx.base.transfer.completion.chart.g4AnalyticContinuation :=
  g8d_transfer_requires_g4AnalyticContinuation ctx.base.transfer h.transfer

/-- The G8e.1 package still depends on the G5 operator-carrier obligation. -/
theorem g8e1_subobligations_require_g5OperatorCarrier
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    ctx.base.transfer.completion.chart.g5OperatorCarrier :=
  g8d_transfer_requires_g5OperatorCarrier ctx.base.transfer h.transfer

/-- The G8e.1 package still depends on the G6 determinant/O3 bridge obligation. -/
theorem g8e1_subobligations_require_g6O3DeterminantBridge
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    ctx.base.transfer.completion.chart.g6O3DeterminantBridge :=
  g8d_transfer_requires_g6O3DeterminantBridge ctx.base.transfer h.transfer

/-- The G8e.1 package still depends on no-lost-zero transfer. -/
theorem g8e1_subobligations_require_noLost
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    ctx.base.transfer.noLostZeros :=
  g8d_transfer_requires_noLost ctx.base.transfer h.transfer

/-- The G8e.1 package still depends on no-spurious-zero transfer. -/
theorem g8e1_subobligations_require_noSpurious
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    ctx.base.transfer.noSpuriousZeros :=
  g8d_transfer_requires_noSpurious ctx.base.transfer h.transfer

/-- The G8e.1 package still depends on multiplicity preservation. -/
theorem g8e1_subobligations_require_multiplicityPreserved
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    ctx.base.transfer.multiplicityPreserved :=
  g8d_transfer_requires_multiplicityPreserved ctx.base.transfer h.transfer

/-- The G8e.1 package also exposes the chart-level no-lost-zero obligation. -/
theorem g8e1_subobligations_require_chartNoLostZeros
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    ctx.base.transfer.completion.chart.noLostZeros :=
  g8d_transfer_requires_chartNoLostZeros ctx.base.transfer h.transfer

/-- The G8e.1 package also exposes the chart-level no-spurious-zero obligation. -/
theorem g8e1_subobligations_require_chartNoSpuriousZeros
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    ctx.base.transfer.completion.chart.noSpuriousZeros :=
  g8d_transfer_requires_chartNoSpuriousZeros ctx.base.transfer h.transfer

/-- The G8e.1 package also exposes chart-level multiplicity preservation. -/
theorem g8e1_subobligations_require_chartMultiplicityPreserved
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    ctx.base.transfer.completion.chart.multiplicityPreserved :=
  g8d_transfer_requires_chartMultiplicityPreserved ctx.base.transfer h.transfer

/-- The G8e.1 package carries the non-uniqueness falsifier guardrail. -/
theorem g8e1_subobligations_require_noTwoCompletionsGuard
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1PullbackSubobligations ctx) :
    noTwoCompletions_sameTauTower_differentDivisor
      ctx.base.transfer.completion.chart :=
  g8d_transfer_requires_noTwoCompletionsGuard ctx.base.transfer h.transfer

-- ============================================================
-- CONDITIONAL TEST ASSEMBLY
-- ============================================================

/-- Test-level admissibility for the indirect contradiction route. -/
def G8e1ContradictionTestAdmissible
    (ctx : OffCriticalPullbackTestContext) : Prop :=
  G8e1PullbackSubobligations ctx ∧
  G8eTauPurityExcludesOffCritical ctx.base

/-- G8e.1 test admissibility recovers the original G8e admissibility. -/
theorem g8e1_testAdmissible_to_g8eAdmissible
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1ContradictionTestAdmissible ctx) :
    G8eOffCriticalContradictionAdmissible ctx.base :=
  ⟨h.left.transfer,
    g8e1_subobligations_yield_pullback ctx h.left,
    h.right⟩

/-- Conditional no-off-critical-zero conclusion at the test-context level.

This is deliberately local to the declared orthodox zero object.  It is not a
global theorem about the classical problem. -/
theorem g8e1_noOffCriticalZeros_from_testAdmissible
    (ctx : OffCriticalPullbackTestContext)
    (h : G8e1ContradictionTestAdmissible ctx) :
    G8eNoOrthodoxOffCriticalZeros ctx.base :=
  rh_by_contradiction_from_pullback_and_tauPurity ctx.base
    (g8e1_testAdmissible_to_g8eAdmissible ctx h)

end Tau.BookIII.Bridge
