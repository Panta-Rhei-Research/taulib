import TauLib.BookIII.Bridge.G8WeakOffCriticalPullbackTest

/-!
# TauLib.BookIII.Bridge.G8OffAxisChartGuard

Off-axis chart guard for the weak G8 off-critical pullback route.

The decisive falsifier for the weak route is not an arbitrary on-axis
receiving-side artifact.  It is an orthodox off-critical zero whose centered
shadow is off-axis but which has no tau-native imbalance preimage.  This module
names that witness and proves that excluding it supplies the chart-only guard
needed by the weak pullback test.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- OFF-AXIS CHART-ONLY GHOSTS
-- ============================================================

/-- Off-axis chart-only ghost witness.

This refines `ChartOnlyOffCriticalZeroWitness` with the local shadow evidence
that the receiving-side zero is actually off the critical axis in the centered
fold chart. -/
structure G8OffAxisChartOnlyGhostWitness
    (ctx : OffCriticalPullbackTestContext) where
  z : ctx.base.orthodoxZero
  offCritical : ClassicalOffCriticalZero ctx.base z
  offAxis : ShadowOffAxis (ctx.orthodoxShadow z)
  noTauPreimage :
    ∀ w : ctx.base.tauWitness, ¬ TauOffCriticalWitness ctx.base w

/-- No off-axis chart-only ghost exists in the declared test context. -/
def NoChartOnlyOffCriticalZerosOutsideAxis
    (ctx : OffCriticalPullbackTestContext) : Prop :=
  ¬ Nonempty (G8OffAxisChartOnlyGhostWitness ctx)

/-- Forgetting the off-axis shadow data recovers the older chart-only witness. -/
def g8OffAxisGhost_to_chartOnlyWitness
    {ctx : OffCriticalPullbackTestContext}
    (w : G8OffAxisChartOnlyGhostWitness ctx) :
    ChartOnlyOffCriticalZeroWitness ctx.base where
  z := w.z
  offCritical := w.offCritical
  noTauPreimage := w.noTauPreimage

/-- Local fold readability upgrades a chart-only off-critical zero to an
    off-axis chart-only ghost. -/
def g8ChartOnlyWitness_to_offAxisGhost
    {ctx : OffCriticalPullbackTestContext}
    (localFold : G8e1LocalFoldReadable ctx)
    (w : ChartOnlyOffCriticalZeroWitness ctx.base) :
    G8OffAxisChartOnlyGhostWitness ctx where
  z := w.z
  offCritical := w.offCritical
  offAxis := localFold w.z w.offCritical
  noTauPreimage := w.noTauPreimage

/-- Local fold readability plus the off-axis guard supplies the older
    chart-only guard. -/
theorem g8OffAxisGuard_noChartOnly
    (ctx : OffCriticalPullbackTestContext)
    (localFold : G8e1LocalFoldReadable ctx)
    (guard : NoChartOnlyOffCriticalZerosOutsideAxis ctx) :
    G8e1NoChartOnlyOffCriticalZero ctx := by
  intro h
  rcases h with ⟨w⟩
  exact guard ⟨g8ChartOnlyWitness_to_offAxisGhost localFold w⟩

/-- An off-axis ghost witness refutes the off-axis chart guard. -/
theorem g8OffAxisGhost_refutes_chartGuard
    {ctx : OffCriticalPullbackTestContext}
    (w : G8OffAxisChartOnlyGhostWitness ctx) :
    ¬ NoChartOnlyOffCriticalZerosOutsideAxis ctx := by
  intro guard
  exact guard ⟨w⟩

-- ============================================================
-- GUARDED WEAK SUBOBLIGATIONS
-- ============================================================

/-- Weak pullback subobligations with the no-chart-only field replaced by the
    sharper off-axis chart guard. -/
structure G8OffAxisGuardedWeakSubobligations
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  localFold : G8e1LocalFoldReadable ctx.test
  chartFaithful : G8e1ChartFaithfulToTauImbalance ctx.test
  tauWitness : G8e1TauImbalanceRealizesWitness ctx.test
  offAxisGuard : NoChartOnlyOffCriticalZerosOutsideAxis ctx.test

/-- Off-axis guarded obligations yield the weak pullback subobligations. -/
def g8OffAxisGuarded_to_weakSubobligations
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (h : G8OffAxisGuardedWeakSubobligations ctx) :
    G8WeakOffCriticalPullbackSubobligations ctx where
  localFold := h.localFold
  chartFaithful := h.chartFaithful
  tauWitness := h.tauWitness
  noChartOnly :=
    g8OffAxisGuard_noChartOnly ctx.test h.localFold h.offAxisGuard

/-- Off-axis guarded obligations refute failure of the weak pullback package. -/
theorem g8OffAxisGuard_refutes_weakPullbackPackageFailure
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (h : G8OffAxisGuardedWeakSubobligations ctx) :
    ¬ (¬ Nonempty (G8WeakOffCriticalPullbackSubobligations ctx)) := by
  intro failure
  exact failure ⟨g8OffAxisGuarded_to_weakSubobligations ctx h⟩

/-- Off-axis guarded obligations and tau purity yield the local
    no-off-critical-zero conclusion. -/
theorem g8OffAxisGuard_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (h : G8OffAxisGuardedWeakSubobligations ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8WeakOffCritical_noOffCriticalZeros ctx
    (g8OffAxisGuarded_to_weakSubobligations ctx h)
    tauPurity

end Tau.BookIII.Bridge
