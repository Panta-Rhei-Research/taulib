import TauLib.BookIII.Bridge.G8OffCriticalPullbackTest

/-!
# TauLib.BookIII.Bridge.G8ChartFaithfulness

G8e.2 chart-faithfulness scaffold for the RH bridge proof program.

G8e.1 showed that the indirect off-critical route can be factored into local
fold readability, chart faithfulness, tau witness realization, and transfer
discipline.  This module opens the chart-faithfulness step itself:

* every off-axis receiving-side shadow must have a tau preimage;
* every related tau preimage must carry tau-native critical imbalance;
* no-preimage shadows and balanced tau preimages are explicit red-team
  falsifiers.

This is still a scaffold.  It does not construct the analytic chart, does not
prove tau/xi divisor transfer, and does not turn finite data into an infinite
zero statement.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- CHART-FAITHFULNESS STATUS AND CONTEXT
-- ============================================================

/-- Diagnostic labels for the G8e.2 chart-faithfulness problem. -/
inductive ChartFaithfulnessStatus where
  | openObligation
  | preimageExistenceNeeded
  | imbalancePreservationNeeded
  | noPreimagePressure
  | balancedPreimagePressure
  | conditionalFaithfulnessAvailable
  deriving Repr, DecidableEq

/-- G8e.2 context: a relation between receiving-side shadows and tau-side
    witness candidates.

The relation is deliberately abstract.  Future modules may instantiate it with
an actual chart/pullback construction. -/
structure ChartFaithfulnessContext where
  test : OffCriticalPullbackTestContext
  shadowTauRelated :
    test.base.orthodoxZero → test.base.tauWitness → Prop
  status : ChartFaithfulnessStatus := .openObligation

/-- Every off-axis receiving-side shadow has at least one tau preimage under
    the declared chart relation. -/
def G8e2OffAxisHasTauPreimage
    (ctx : ChartFaithfulnessContext) : Prop :=
  ∀ z : ctx.test.base.orthodoxZero,
    ShadowOffAxis (ctx.test.orthodoxShadow z) →
      ∃ w : ctx.test.base.tauWitness, ctx.shadowTauRelated z w

/-- Every related tau preimage of an off-axis shadow carries tau-native
    critical imbalance. -/
def G8e2RelatedPreimageCarriesTauImbalance
    (ctx : ChartFaithfulnessContext) : Prop :=
  ∀ (z : ctx.test.base.orthodoxZero)
    (w : ctx.test.base.tauWitness),
    ShadowOffAxis (ctx.test.orthodoxShadow z) →
      ctx.shadowTauRelated z w →
        TauCriticalImbalance (ctx.test.tauNormalForm w)

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- An off-axis shadow with no tau preimage under the declared chart relation.
    This directly pressures the chart-faithfulness route. -/
structure NoTauPreimageForOffAxisShadowWitness
    (ctx : ChartFaithfulnessContext) where
  z : ctx.test.base.orthodoxZero
  offAxis : ShadowOffAxis (ctx.test.orthodoxShadow z)
  noTauPreimage :
    ∀ w : ctx.test.base.tauWitness, ¬ ctx.shadowTauRelated z w

/-- A related tau preimage that remains B/C-balanced.  Such a witness pressures
    the claim that off-axis receiving-side data reflects to tau imbalance. -/
structure BalancedTauPreimageWitness
    (ctx : ChartFaithfulnessContext) where
  z : ctx.test.base.orthodoxZero
  w : ctx.test.base.tauWitness
  offAxis : ShadowOffAxis (ctx.test.orthodoxShadow z)
  related : ctx.shadowTauRelated z w
  balanced : BCBalanced (ctx.test.tauNormalForm w)

/-- No no-preimage falsifier is present. -/
def G8e2NoTauPreimageFalsifier
    (ctx : ChartFaithfulnessContext) : Prop :=
  ¬ Nonempty (NoTauPreimageForOffAxisShadowWitness ctx)

/-- No balanced-preimage falsifier is present. -/
def G8e2NoBalancedPreimageFalsifier
    (ctx : ChartFaithfulnessContext) : Prop :=
  ¬ Nonempty (BalancedTauPreimageWitness ctx)

/-- A no-preimage witness refutes off-axis preimage existence. -/
theorem g8e2_noPreimageWitness_refutes_preimageExistence
    (ctx : ChartFaithfulnessContext)
    (w : NoTauPreimageForOffAxisShadowWitness ctx) :
    ¬ G8e2OffAxisHasTauPreimage ctx := by
  intro h
  obtain ⟨tauW, hRel⟩ := h w.z w.offAxis
  exact w.noTauPreimage tauW hRel

/-- A balanced tau preimage refutes imbalance preservation. -/
theorem g8e2_balancedPreimage_refutes_imbalancePreservation
    (ctx : ChartFaithfulnessContext)
    (w : BalancedTauPreimageWitness ctx) :
    ¬ G8e2RelatedPreimageCarriesTauImbalance ctx := by
  intro h
  have hImbalance :=
    h w.z w.w w.offAxis w.related
  unfold TauCriticalImbalance at hImbalance
  exact hImbalance
    ((tauCriticalLocus_iff_bcBalanced (ctx.test.tauNormalForm w.w)).mpr
      w.balanced)

/-- Preimage existence rules out the no-preimage falsifier. -/
theorem g8e2_preimageExistence_rulesOut_noPreimageFalsifier
    (ctx : ChartFaithfulnessContext)
    (h : G8e2OffAxisHasTauPreimage ctx) :
    G8e2NoTauPreimageFalsifier ctx := by
  intro hw
  rcases hw with ⟨w⟩
  exact g8e2_noPreimageWitness_refutes_preimageExistence ctx w h

/-- Imbalance preservation rules out the balanced-preimage falsifier. -/
theorem g8e2_imbalancePreservation_rulesOut_balancedPreimageFalsifier
    (ctx : ChartFaithfulnessContext)
    (h : G8e2RelatedPreimageCarriesTauImbalance ctx) :
    G8e2NoBalancedPreimageFalsifier ctx := by
  intro hw
  rcases hw with ⟨w⟩
  exact g8e2_balancedPreimage_refutes_imbalancePreservation ctx w h

-- ============================================================
-- FACTORING G8E.1 CHART FAITHFULNESS
-- ============================================================

/-- The two G8e.2 chart-faithfulness obligations imply the G8e.1 chart
    faithfulness predicate. -/
theorem g8e2_chartFaithfulness_yields_g8e1
    (ctx : ChartFaithfulnessContext)
    (hPre : G8e2OffAxisHasTauPreimage ctx)
    (hImb : G8e2RelatedPreimageCarriesTauImbalance ctx) :
    G8e1ChartFaithfulToTauImbalance ctx.test := by
  intro z hOffAxis
  obtain ⟨w, hRel⟩ := hPre z hOffAxis
  exact ⟨w, hImb z w hOffAxis hRel⟩

/-- G8e.2 obligations sufficient to rebuild the G8e.1 pullback package. -/
structure G8e2PullbackSubobligations
    (ctx : ChartFaithfulnessContext) where
  transfer : G8dZeroDivisorTransferAdmissible ctx.test.base.transfer
  localFold : G8e1LocalFoldReadable ctx.test
  preimage : G8e2OffAxisHasTauPreimage ctx
  imbalance : G8e2RelatedPreimageCarriesTauImbalance ctx
  tauWitness : G8e1TauImbalanceRealizesWitness ctx.test
  noChartOnly : G8e1NoChartOnlyOffCriticalZero ctx.test

/-- The G8e.2 package rebuilds the G8e.1 package, making the next stair-step
    explicit. -/
theorem g8e2_subobligations_yield_g8e1
    (ctx : ChartFaithfulnessContext)
    (h : G8e2PullbackSubobligations ctx) :
    G8e1PullbackSubobligations ctx.test :=
  { transfer := h.transfer
    localFold := h.localFold
    chartFaithful :=
      g8e2_chartFaithfulness_yields_g8e1 ctx h.preimage h.imbalance
    tauWitness := h.tauWitness
    noChartOnly := h.noChartOnly }

/-- The G8e.2 package exposes the no-preimage falsifier guardrail. -/
theorem g8e2_subobligations_ruleOut_noPreimageFalsifier
    (ctx : ChartFaithfulnessContext)
    (h : G8e2PullbackSubobligations ctx) :
    G8e2NoTauPreimageFalsifier ctx :=
  g8e2_preimageExistence_rulesOut_noPreimageFalsifier ctx h.preimage

/-- The G8e.2 package exposes the balanced-preimage falsifier guardrail. -/
theorem g8e2_subobligations_ruleOut_balancedPreimageFalsifier
    (ctx : ChartFaithfulnessContext)
    (h : G8e2PullbackSubobligations ctx) :
    G8e2NoBalancedPreimageFalsifier ctx :=
  g8e2_imbalancePreservation_rulesOut_balancedPreimageFalsifier
    ctx h.imbalance

/-- G8e.2 test-level admissibility. -/
def G8e2ContradictionTestAdmissible
    (ctx : ChartFaithfulnessContext) : Prop :=
  G8e2PullbackSubobligations ctx ∧
  G8eTauPurityExcludesOffCritical ctx.test.base

/-- G8e.2 admissibility recovers the G8e.1 admissibility interface. -/
theorem g8e2_testAdmissible_to_g8e1TestAdmissible
    (ctx : ChartFaithfulnessContext)
    (h : G8e2ContradictionTestAdmissible ctx) :
    G8e1ContradictionTestAdmissible ctx.test :=
  ⟨g8e2_subobligations_yield_g8e1 ctx h.left, h.right⟩

/-- Conditional no-off-critical-zero conclusion at the G8e.2 test level. -/
theorem g8e2_noOffCriticalZeros_from_testAdmissible
    (ctx : ChartFaithfulnessContext)
    (h : G8e2ContradictionTestAdmissible ctx) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8e1_noOffCriticalZeros_from_testAdmissible ctx.test
    (g8e2_testAdmissible_to_g8e1TestAdmissible ctx h)

end Tau.BookIII.Bridge
