import TauLib.BookIII.Bridge.G8OneSidedPullbackCorridor

/-!
# TauLib.BookIII.Bridge.G8OffCriticalExclusionTransfer

One-sided off-critical exclusion transfer for the G8 pullback corridor.

The preceding corridor modules make the full route audit explicit.  This module
records the sharper observation needed for an indirect RH-style argument:
excluding orthodox off-critical zeros does not require a full equality of
receiving-side zero divisors.  It requires only a one-sided transfer from an
orthodox off-critical zero to a tau-native imbalance witness, plus tau-side
purity excluding such witnesses.

This is still a conditional bridge interface.  It does not construct the
analytic chart, does not prove completion uniqueness, does not prove O3, and
does not assert any global classical result.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- OFF-CRITICAL EXCLUSION STATUS
-- ============================================================

/-- Local status labels for the weaker off-critical exclusion transfer. -/
inductive G8OffCriticalExclusionStatus where
  | openObligation
  | finiteSubstrateOnly
  | offAxisChartGuard
  | conditionalExclusionAvailable
  | offAxisGhostPressure
  deriving Repr, DecidableEq

-- ============================================================
-- WEAK ONE-SIDED EXCLUSION CONTEXT
-- ============================================================

/-- Weak off-critical exclusion transfer context.

The context deliberately separates the one-sided off-critical route from the
full G8d zero-divisor transfer stack.  Finite G8a/G8b data remain visible as
guardrails, but they do not create an orthodox `xi` divisor or an analytic
completion claim. -/
structure G8OffCriticalExclusionTransferContext where
  base : OffCriticalZeroPullbackContext
  offCriticalChartAdmissible : Prop
  offCriticalPullback : G8eOffCriticalPullback base
  tauPurity : G8eTauPurityExcludesOffCritical base
  finiteGuardrails : G8bFiniteOnlyGuardrails finiteG8bContext :=
    finiteG8bContext_guardrails
  status : G8OffCriticalExclusionStatus := .openObligation

/-- Admissibility for the weak off-critical exclusion transfer.

Unlike `G8eOffCriticalContradictionAdmissible`, this package does not contain
the full G8d zero-divisor-transfer admissibility proof.  It names the smaller
one-sided burden: chart admissibility outside the critical axis, one-sided
pullback, and tau-side purity. -/
def G8OffCriticalExclusionTransferAdmissible
    (ctx : G8OffCriticalExclusionTransferContext) : Prop :=
  ctx.offCriticalChartAdmissible

/-- The weak exclusion context exposes its local off-critical chart guard. -/
theorem g8OffCriticalExclusion_requires_chartGuard
    (ctx : G8OffCriticalExclusionTransferContext)
    (h : G8OffCriticalExclusionTransferAdmissible ctx) :
    ctx.offCriticalChartAdmissible :=
  h

/-- The weak exclusion context exposes the one-sided pullback obligation. -/
theorem g8OffCriticalExclusion_requires_pullback
    (ctx : G8OffCriticalExclusionTransferContext)
    (_h : G8OffCriticalExclusionTransferAdmissible ctx) :
    G8eOffCriticalPullback ctx.base :=
  ctx.offCriticalPullback

/-- The weak exclusion context exposes tau-side purity. -/
theorem g8OffCriticalExclusion_requires_tauPurity
    (ctx : G8OffCriticalExclusionTransferContext)
    (_h : G8OffCriticalExclusionTransferAdmissible ctx) :
    G8eTauPurityExcludesOffCritical ctx.base :=
  ctx.tauPurity

/-- The weak exclusion context keeps finite-stage support below orthodox
    zero-divisor claims. -/
theorem g8OffCriticalExclusion_noXiDivisorClaim_from_finiteStage
    (ctx : G8OffCriticalExclusionTransferContext) :
    finiteG8bContext.noXiDivisorClaim :=
  ctx.finiteGuardrails.right.left

/-- The weak exclusion context keeps finite-stage support below analytic
    completion claims. -/
theorem g8OffCriticalExclusion_noAnalyticCompletionClaim_from_finiteStage
    (ctx : G8OffCriticalExclusionTransferContext) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  ctx.finiteGuardrails.right.right

/-- The weak exclusion context records that G8a/G8b data are finite substrate
    only. -/
theorem g8OffCriticalExclusion_finiteOnlyGuardrail
    (ctx : G8OffCriticalExclusionTransferContext) :
    finiteG8bContext.finiteOnly :=
  ctx.finiteGuardrails.left

-- ============================================================
-- LOCAL NO-OFF-CRITICAL-ZERO RESULT
-- ============================================================

/-- Weak off-critical exclusion theorem.

If every orthodox off-critical zero pulls back to a tau-native imbalance and
tau purity excludes such imbalances, then the declared orthodox-zero object has
no off-critical zeros.  This theorem does not use full zero-divisor equality,
no-spurious-zero transfer, no-lost-zero transfer, or multiplicity preservation.
-/
theorem g8OffCriticalExclusion_noOffCriticalZeros
    (ctx : G8OffCriticalExclusionTransferContext)
    (h : G8OffCriticalExclusionTransferAdmissible ctx) :
    G8eNoOrthodoxOffCriticalZeros ctx.base := by
  intro z hz
  obtain ⟨w, hw⟩ :=
    (g8OffCriticalExclusion_requires_pullback ctx h) z hz
  exact (g8OffCriticalExclusion_requires_tauPurity ctx h) w hw

-- ============================================================
-- OFF-AXIS GHOST PRESSURE
-- ============================================================

/-- Off-critical ghost witness for the weak route.

This is the same chart-only witness as in G8e, renamed at this layer to mark
the key failure mode: an orthodox off-critical chart zero with no tau-native
imbalance preimage. -/
abbrev G8OffCriticalGhostZeroWitness
    (ctx : G8OffCriticalExclusionTransferContext) :=
  ChartOnlyOffCriticalZeroWitness ctx.base

/-- An off-critical ghost witness refutes the weak exclusion transfer. -/
theorem g8OffCriticalGhost_refutes_exclusionTransfer
    (ctx : G8OffCriticalExclusionTransferContext)
    (w : G8OffCriticalGhostZeroWitness ctx) :
    ¬ G8OffCriticalExclusionTransferAdmissible ctx := by
  intro h
  obtain ⟨tauW, hTauW⟩ :=
    (g8OffCriticalExclusion_requires_pullback ctx h) w.z w.offCritical
  exact w.noTauPreimage tauW hTauW

/-- The stage-aware one-sided corridor already rules out off-axis receiving
    divisor witnesses at its own target layer.  This re-export keeps the
    off-axis ghost pressure visible from the weaker exclusion module. -/
theorem g8OffCriticalExclusion_corridor_noOffAxisDivisor
    {ctx : G8MasterSwitchContext}
    (corridor : G8OneSidedDivisorPullbackCorridor ctx) :
    ¬ Nonempty (G8OffAxisReceivingDivisorWitness corridor) :=
  g8OneSidedCorridor_rulesOut_offAxisDivisor corridor

-- ============================================================
-- NO-FULL-DIVISOR-BURDEN RECORD
-- ============================================================

/-- Documentation record for the weaker burden of the off-critical route.

The fields are intentionally propositional guard labels.  They mark that the
off-critical exclusion theorem above is a one-sided argument and does not, by
itself, require on-axis spurious-zero control, full same-divisor equivalence,
or multiplicity preservation. -/
structure G8OffCriticalExclusionNoFullDivisorBurden where
  noSameXiDivisorRequiredForLocalExclusion : Prop := True
  noOnAxisSpuriousControlRequiredForLocalExclusion : Prop := True
  noMultiplicityRequiredForLocalExclusion : Prop := True

/-- The weak transfer exposes the no-full-divisor-burden record. -/
def g8OffCriticalExclusion_noFullDivisorBurden
    (_ctx : G8OffCriticalExclusionTransferContext) :
    G8OffCriticalExclusionNoFullDivisorBurden where
  noSameXiDivisorRequiredForLocalExclusion := True
  noOnAxisSpuriousControlRequiredForLocalExclusion := True
  noMultiplicityRequiredForLocalExclusion := True

/-- The weak transfer's no-full-divisor-burden record is inhabited in each
    component. -/
theorem g8OffCriticalExclusion_noFullDivisorBurden_components
    (ctx : G8OffCriticalExclusionTransferContext) :
    (g8OffCriticalExclusion_noFullDivisorBurden ctx).noSameXiDivisorRequiredForLocalExclusion ∧
    (g8OffCriticalExclusion_noFullDivisorBurden ctx).noOnAxisSpuriousControlRequiredForLocalExclusion ∧
    (g8OffCriticalExclusion_noFullDivisorBurden ctx).noMultiplicityRequiredForLocalExclusion :=
  ⟨trivial, trivial, trivial⟩

end Tau.BookIII.Bridge
