import TauLib.BookIII.Bridge.G8PullbackDependencyChain

/-!
# TauLib.BookIII.Bridge.G8PullbackFalsifierPressure

G8e.6 falsifier-pressure layer for the RH bridge proof program.

`G8PullbackDependencyChain` shows what an admissible off-critical pullback
route must expose.  This module turns the red-team tests around: concrete
falsifier witnesses refute admissibility of the G8e.4 route.

This is still proof-program plumbing.  The module does not prove analytic
completion uniqueness, zero-divisor transfer, O3, or RH.  It proves that the
route cannot ignore the named failure modes.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- LOCAL ABBREVIATIONS
-- ============================================================

/-- The G8e.1 test context carried by a G8e.4 master-switch context. -/
abbrev g8e4TestContext (ctx : G8MasterSwitchContext) :
    OffCriticalPullbackTestContext :=
  ctx.chart.faithfulness.test

/-- The G8e base pullback context carried by a G8e.4 context. -/
abbrev g8e4BaseContext (ctx : G8MasterSwitchContext) :
    OffCriticalZeroPullbackContext :=
  (g8e4TestContext ctx).base

-- ============================================================
-- GUARDRAIL PREDICATES
-- ============================================================

/-- No concrete multiplicity-mismatch witness is present. -/
def G8dNoMultiplicityMismatch
    (ctx : G8dZeroDivisorTransferContext) : Prop :=
  ¬ Nonempty (MultiplicityMismatchWitness ctx)

/-- Multiplicity preservation rules out concrete mismatch witnesses. -/
theorem g8d_multiplicityPreserved_rulesOut_mismatchWitness
    (ctx : G8dZeroDivisorTransferContext)
    (h : G8dMultiplicityPreserved ctx) :
    G8dNoMultiplicityMismatch ctx := by
  intro hw
  rcases hw with ⟨w⟩
  exact g8d_mismatchWitness_refutes_multiplicityPreserved ctx w h

/-- Compact suite of falsifier guardrails carried by an admissible G8e.4
    pullback route. -/
structure G8PullbackFalsifierGuards
    (ctx : G8MasterSwitchContext) where
  noNonuniqueCompletion :
    G8cNoNonuniqueCompletion (g8e4CompletionContext ctx)
  noLostZero : G8dNoLostZeros (g8e4TransferContext ctx)
  noSpuriousZero : G8dNoSpuriousZeros (g8e4TransferContext ctx)
  noMultiplicityMismatch :
    G8dNoMultiplicityMismatch (g8e4TransferContext ctx)
  noChartOnly : G8e1NoChartOnlyOffCriticalZero (g8e4TestContext ctx)
  noMeromorphicArtifact :
    ¬ Nonempty (MeromorphicChartArtifactFalsifier ctx.chart)
  noNoPreimage :
    G8e2NoTauPreimageFalsifier ctx.chart.faithfulness
  noBalancedPreimage :
    G8e2NoBalancedPreimageFalsifier ctx.chart.faithfulness

/-- Build the falsifier-guard suite from a G8e.4 admissible route. -/
def g8e4_falsifierGuards
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    G8PullbackFalsifierGuards ctx where
  noNonuniqueCompletion :=
    g8e4_admissible_rulesOut_nonuniqueCompletionWitness ctx h
  noLostZero := g8e4_admissible_rulesOut_lostZeroWitness ctx h
  noSpuriousZero := g8e4_admissible_rulesOut_spuriousZeroWitness ctx h
  noMultiplicityMismatch :=
    g8d_multiplicityPreserved_rulesOut_mismatchWitness
      (g8e4TransferContext ctx)
      (g8e4_admissible_requires_multiplicityWitnessFree ctx h)
  noChartOnly := h.left.noChartOnly
  noMeromorphicArtifact :=
    g8e4_masterSwitches_ruleOut_artifactFalsifier
      ctx h.left.masterSwitches
  noNoPreimage :=
    g8e3_chartRelation_rulesOut_noPreimageFalsifier
      ctx.chart h.left.masterSwitches.chartRelation
  noBalancedPreimage :=
    g8e3_chartRelation_rulesOut_balancedPreimageFalsifier
      ctx.chart h.left.masterSwitches.chartRelation

-- ============================================================
-- FALSIFIERS REFUTE ADMISSIBILITY
-- ============================================================

/-- A non-unique analytic-completion witness refutes the G8e.4 route. -/
theorem g8e4_nonuniqueCompletionWitness_refutes_admissible
    (ctx : G8MasterSwitchContext)
    (w : G8cNonuniqueCompletionWitness (g8e4CompletionContext ctx)) :
    ¬ G8e4ContradictionTestAdmissible ctx := by
  intro h
  exact g8c_witness_refutes_noNonuniqueCompletion
    (g8e4CompletionContext ctx) w
    (g8e4_admissible_rulesOut_nonuniqueCompletionWitness ctx h)

/-- A lost orthodox zero witness refutes the G8e.4 route. -/
theorem g8e4_lostZeroWitness_refutes_admissible
    (ctx : G8MasterSwitchContext)
    (w : LostOrthodoxZeroWitness (g8e4TransferContext ctx)) :
    ¬ G8e4ContradictionTestAdmissible ctx := by
  intro h
  exact g8d_lostWitness_refutes_noLost
    (g8e4TransferContext ctx) w
    (g8e4_admissible_rulesOut_lostZeroWitness ctx h)

/-- A spurious tau zero witness refutes the G8e.4 route. -/
theorem g8e4_spuriousZeroWitness_refutes_admissible
    (ctx : G8MasterSwitchContext)
    (w : SpuriousTauZeroWitness (g8e4TransferContext ctx)) :
    ¬ G8e4ContradictionTestAdmissible ctx := by
  intro h
  exact g8d_spuriousWitness_refutes_noSpurious
    (g8e4TransferContext ctx) w
    (g8e4_admissible_rulesOut_spuriousZeroWitness ctx h)

/-- A multiplicity mismatch witness refutes the G8e.4 route. -/
theorem g8e4_multiplicityMismatchWitness_refutes_admissible
    (ctx : G8MasterSwitchContext)
    (w : MultiplicityMismatchWitness (g8e4TransferContext ctx)) :
    ¬ G8e4ContradictionTestAdmissible ctx := by
  intro h
  exact g8d_mismatchWitness_refutes_multiplicityPreserved
    (g8e4TransferContext ctx) w
    (g8e4_admissible_requires_multiplicityWitnessFree ctx h)

/-- A chart-only off-critical zero witness refutes the G8e.4 route. -/
theorem g8e4_chartOnlyWitness_refutes_admissible
    (ctx : G8MasterSwitchContext)
    (w : ChartOnlyOffCriticalZeroWitness (g8e4BaseContext ctx)) :
    ¬ G8e4ContradictionTestAdmissible ctx := by
  intro h
  exact h.left.noChartOnly ⟨w⟩

/-- An uncontrolled meromorphic-artifact witness refutes the G8e.4 route. -/
theorem g8e4_meromorphicArtifactWitness_refutes_admissible
    (ctx : G8MasterSwitchContext)
    (w : MeromorphicChartArtifactFalsifier ctx.chart) :
    ¬ G8e4ContradictionTestAdmissible ctx := by
  intro h
  exact
    (g8e4_masterSwitches_ruleOut_artifactFalsifier
      ctx h.left.masterSwitches) ⟨w⟩

/-- A no-preimage off-axis shadow witness refutes the G8e.4 route. -/
theorem g8e4_noPreimageWitness_refutes_admissible
    (ctx : G8MasterSwitchContext)
    (w : NoTauPreimageForOffAxisShadowWitness ctx.chart.faithfulness) :
    ¬ G8e4ContradictionTestAdmissible ctx := by
  intro h
  exact g8e2_noPreimageWitness_refutes_preimageExistence
    ctx.chart.faithfulness w
    h.left.masterSwitches.chartRelation.preimage

/-- A balanced tau preimage witness refutes the G8e.4 route. -/
theorem g8e4_balancedPreimageWitness_refutes_admissible
    (ctx : G8MasterSwitchContext)
    (w : BalancedTauPreimageWitness ctx.chart.faithfulness) :
    ¬ G8e4ContradictionTestAdmissible ctx := by
  intro h
  exact g8e2_balancedPreimage_refutes_imbalancePreservation
    ctx.chart.faithfulness w
    h.left.masterSwitches.chartRelation.imbalance

end Tau.BookIII.Bridge
