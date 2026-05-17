import TauLib.BookIII.Bridge.G8MasterSwitches

/-!
# TauLib.BookIII.Bridge.G8PullbackDependencyChain

G8e.5 dependency-chain extraction for the RH bridge proof program.

The off-critical pullback route is attractive because it phrases RH as a
contradiction argument: an orthodox off-axis zero would have to pull back to a
tau-native imbalance, and tau purity would exclude that imbalance.

This module records the hard lesson from the G8 situation-room analysis:
that route is a stairway, not a tunnel.  A master-switch-disciplined G8e.4
admissible context still has to expose the G8d zero-divisor-transfer stack and
the G8c analytic-completion uniqueness guardrail.  The theorems below are
pure bookkeeping extractions from the existing scaffold; they add no axioms,
prove no zero-divisor correspondence, and do not claim the classical Riemann
Hypothesis.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- LOCAL ABBREVIATIONS
-- ============================================================

/-- The G8d transfer context carried by a G8e.4 master-switch context. -/
abbrev g8e4TransferContext (ctx : G8MasterSwitchContext) :
    G8dZeroDivisorTransferContext :=
  ctx.chart.faithfulness.test.base.transfer

/-- The G8c completion context carried by a G8e.4 master-switch context. -/
abbrev g8e4CompletionContext (ctx : G8MasterSwitchContext) :
    G8cCompletionUniquenessContext :=
  (g8e4TransferContext ctx).completion

/-- The zeta-as-coordinate-chart context carried by a G8e.4 context. -/
abbrev g8e4ZetaChartContext (ctx : G8MasterSwitchContext) :
    ZetaAsCoordinateChartContext :=
  (g8e4CompletionContext ctx).chart

-- ============================================================
-- DEPENDENCY EXTRACTIONS
-- ============================================================

/-- A G8e.4 contradiction route still exposes the G8d transfer stack. -/
theorem g8e4_admissible_requires_g8d
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    G8dZeroDivisorTransferAdmissible (g8e4TransferContext ctx) :=
  h.left.transfer

/-- A G8e.4 contradiction route still exposes the G8c completion/uniqueness
    stack. -/
theorem g8e4_admissible_requires_g8c
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    G8cZeroDivisorTransferAdmissible (g8e4CompletionContext ctx) :=
  g8d_transfer_requires_g8c (g8e4TransferContext ctx)
    (g8e4_admissible_requires_g8d ctx h)

/-- A G8e.4 contradiction route still exposes the zeta-as-chart admissibility
    hypotheses. -/
theorem g8e4_admissible_requires_zeroDivisorClaimsAdmissible
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    ZeroDivisorClaimsAdmissible (g8e4ZetaChartContext ctx) :=
  (g8e4_admissible_requires_g8c ctx h).left

/-- In particular, the indirect pullback route does not bypass analytic
    completion uniqueness. -/
theorem g8e4_admissible_requires_completionUnique
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    tauTower_analyticCompletion_unique (g8e4ZetaChartContext ctx) :=
  zeroDivisorClaimsAdmissible_completionUnique
    (g8e4ZetaChartContext ctx)
    (g8e4_admissible_requires_zeroDivisorClaimsAdmissible ctx h)

/-- The route also still needs the same-xi-divisor hypothesis. -/
theorem g8e4_admissible_requires_sameXiDivisor
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    (g8e4ZetaChartContext ctx).sameXiDivisor :=
  zeroDivisorClaimsAdmissible_sameXiDivisor
    (g8e4ZetaChartContext ctx)
    (g8e4_admissible_requires_zeroDivisorClaimsAdmissible ctx h)

/-- The route still needs the no-lost-zero proposition from G8d. -/
theorem g8e4_admissible_requires_noLost
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    (g8e4TransferContext ctx).noLostZeros :=
  g8d_transfer_requires_noLost (g8e4TransferContext ctx)
    (g8e4_admissible_requires_g8d ctx h)

/-- The route still needs the no-spurious-zero proposition from G8d. -/
theorem g8e4_admissible_requires_noSpurious
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    (g8e4TransferContext ctx).noSpuriousZeros :=
  g8d_transfer_requires_noSpurious (g8e4TransferContext ctx)
    (g8e4_admissible_requires_g8d ctx h)

/-- The route still needs multiplicity preservation from G8d. -/
theorem g8e4_admissible_requires_multiplicityPreserved
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    (g8e4TransferContext ctx).multiplicityPreserved :=
  g8d_transfer_requires_multiplicityPreserved (g8e4TransferContext ctx)
    (g8e4_admissible_requires_g8d ctx h)

/-- The route rules out the concrete G8c non-unique-completion falsifier only
    by carrying the G8c guardrail explicitly. -/
theorem g8e4_admissible_rulesOut_nonuniqueCompletionWitness
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    G8cNoNonuniqueCompletion (g8e4CompletionContext ctx) :=
  g8c_transfer_requires_noNonuniqueCompletion
    (g8e4CompletionContext ctx)
    (g8e4_admissible_requires_g8c ctx h)

/-- The route rules out concrete lost-zero witnesses only through G8d. -/
theorem g8e4_admissible_rulesOut_lostZeroWitness
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    G8dNoLostZeros (g8e4TransferContext ctx) :=
  g8d_transfer_requires_noLostWitness (g8e4TransferContext ctx)
    (g8e4_admissible_requires_g8d ctx h)

/-- The route rules out concrete spurious-zero witnesses only through G8d. -/
theorem g8e4_admissible_rulesOut_spuriousZeroWitness
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    G8dNoSpuriousZeros (g8e4TransferContext ctx) :=
  g8d_transfer_requires_noSpuriousWitness (g8e4TransferContext ctx)
    (g8e4_admissible_requires_g8d ctx h)

/-- The route exposes the concrete multiplicity-equality predicate from G8d. -/
theorem g8e4_admissible_requires_multiplicityWitnessFree
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    G8dMultiplicityPreserved (g8e4TransferContext ctx) :=
  g8d_transfer_requires_multiplicityWitnessFree
    (g8e4TransferContext ctx)
    (g8e4_admissible_requires_g8d ctx h)

-- ============================================================
-- COMPACT DEPENDENCY RECORD
-- ============================================================

/-- Compact record of what a G8e.4 pullback route has actually committed to.

This is useful downstream because it prevents the indirect contradiction route
from being read as a shortcut around G8c/G8d. -/
structure G8PullbackDependencyChain
    (ctx : G8MasterSwitchContext) where
  g8d : G8dZeroDivisorTransferAdmissible (g8e4TransferContext ctx)
  g8c : G8cZeroDivisorTransferAdmissible (g8e4CompletionContext ctx)
  zeroDivisorClaims : ZeroDivisorClaimsAdmissible (g8e4ZetaChartContext ctx)
  completionUnique :
    tauTower_analyticCompletion_unique (g8e4ZetaChartContext ctx)
  sameXiDivisor : (g8e4ZetaChartContext ctx).sameXiDivisor
  noLost : (g8e4TransferContext ctx).noLostZeros
  noSpurious : (g8e4TransferContext ctx).noSpuriousZeros
  multiplicityPreserved :
    (g8e4TransferContext ctx).multiplicityPreserved
  noNonuniqueCompletion :
    G8cNoNonuniqueCompletion (g8e4CompletionContext ctx)
  noLostWitness : G8dNoLostZeros (g8e4TransferContext ctx)
  noSpuriousWitness : G8dNoSpuriousZeros (g8e4TransferContext ctx)
  multiplicityWitnessFree :
    G8dMultiplicityPreserved (g8e4TransferContext ctx)

/-- Build the dependency record from a G8e.4 admissible route. -/
def g8e4_dependencyChain
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    G8PullbackDependencyChain ctx where
  g8d := g8e4_admissible_requires_g8d ctx h
  g8c := g8e4_admissible_requires_g8c ctx h
  zeroDivisorClaims :=
    g8e4_admissible_requires_zeroDivisorClaimsAdmissible ctx h
  completionUnique := g8e4_admissible_requires_completionUnique ctx h
  sameXiDivisor := g8e4_admissible_requires_sameXiDivisor ctx h
  noLost := g8e4_admissible_requires_noLost ctx h
  noSpurious := g8e4_admissible_requires_noSpurious ctx h
  multiplicityPreserved :=
    g8e4_admissible_requires_multiplicityPreserved ctx h
  noNonuniqueCompletion :=
    g8e4_admissible_rulesOut_nonuniqueCompletionWitness ctx h
  noLostWitness := g8e4_admissible_rulesOut_lostZeroWitness ctx h
  noSpuriousWitness := g8e4_admissible_rulesOut_spuriousZeroWitness ctx h
  multiplicityWitnessFree :=
    g8e4_admissible_requires_multiplicityWitnessFree ctx h

end Tau.BookIII.Bridge
