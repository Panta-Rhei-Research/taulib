import TauLib.BookIII.Bridge.G8OrthodoxNormalizedAxisClass

/-!
# TauLib.BookIII.Bridge.G8OrthodoxTauUnitWitnessSupply

Tau witness supply for the normalized G8f off-axis pullback corridor.

The normalized axis relation reduced the tau-side preimage requirement to a
binary target: every readable off-axis orthodox shadow needs a tau witness
whose prime-polarity axis offset is `1`.  This module makes the remaining
obligation proof-facing:

* B/C-imbalance witnesses supply unit tau preimages;
* critical-imbalance witnesses supply B/C-imbalance witnesses;
* either supply feeds the normalized preimage context and hence the existing
  local pullback corridor;
* missing imbalance witnesses are explicit falsifiers.

No tau witness is constructed from the abstract pullback context alone.  The
actual witness source must come from the next tau-geometry/normal-form step.
This module proves only the adapter algebra around that supply obligation.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- POINTWISE WITNESS SUPPLY
-- ============================================================

/-- For each readable off-axis orthodox shadow, some tau witness carries B/C
    imbalance. -/
def G8OrthodoxTauBCImbalanceWitnessesExist
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) : Prop :=
  ∀ z : ctx.test.base.orthodoxZero,
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z →
      ∃ w : ctx.test.base.tauWitness,
        TauBCImbalance (ctx.test.tauNormalForm w)

/-- For each readable off-axis orthodox shadow, some tau witness carries tau
    critical-locus imbalance. -/
def G8OrthodoxTauCriticalImbalanceWitnessesExist
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) : Prop :=
  ∀ z : ctx.test.base.orthodoxZero,
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z →
      ∃ w : ctx.test.base.tauWitness,
        TauCriticalImbalance (ctx.test.tauNormalForm w)

/-- B/C-imbalance witness supply yields unit tau preimages. -/
theorem g8OrthodoxTauBCImbalanceWitnesses_to_unitAxisPreimages
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (hSupply : G8OrthodoxTauBCImbalanceWitnessesExist source) :
    G8OrthodoxTauUnitAxisPreimagesExist source := by
  intro z hOffAxis
  obtain ⟨w, hBC⟩ := hSupply z hOffAxis
  exact ⟨w,
    (primePolarityAxisOffset_eq_one_iff_bcImbalance
      (ctx.test.tauNormalForm w)).mpr hBC⟩

/-- Critical-imbalance witness supply yields B/C-imbalance witness supply. -/
theorem g8OrthodoxTauCriticalImbalanceWitnesses_to_bcImbalanceWitnesses
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (hSupply : G8OrthodoxTauCriticalImbalanceWitnessesExist source) :
    G8OrthodoxTauBCImbalanceWitnessesExist source := by
  intro z hOffAxis
  obtain ⟨w, hCrit⟩ := hSupply z hOffAxis
  exact ⟨w,
    (tauCriticalImbalance_iff_bcImbalance
      (ctx.test.tauNormalForm w)).mp hCrit⟩

/-- Critical-imbalance witness supply yields unit tau preimages. -/
theorem g8OrthodoxTauCriticalImbalanceWitnesses_to_unitAxisPreimages
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (hSupply : G8OrthodoxTauCriticalImbalanceWitnessesExist source) :
    G8OrthodoxTauUnitAxisPreimagesExist source :=
  g8OrthodoxTauBCImbalanceWitnesses_to_unitAxisPreimages
    source
    (g8OrthodoxTauCriticalImbalanceWitnesses_to_bcImbalanceWitnesses
      source hSupply)

-- ============================================================
-- GLOBAL DIAGNOSTIC WITNESS FORMS
-- ============================================================

/-- A single tau witness with unit prime-polarity axis offset.

This is a strong diagnostic supply form: it gives every off-axis orthodox
shadow the same unit tau witness.  Later geometry should usually provide the
pointwise form above, but this record is useful for small model tests. -/
structure G8TauUnitAxisWitness
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  witness : ctx.test.base.tauWitness
  unitAxis :
    primePolarityAxisOffset (ctx.test.tauNormalForm witness) = 1

/-- A single tau witness with B/C imbalance. -/
structure G8TauBCImbalanceWitness
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  witness : ctx.test.base.tauWitness
  imbalance :
    TauBCImbalance (ctx.test.tauNormalForm witness)

/-- A single tau witness with critical-locus imbalance. -/
structure G8TauCriticalImbalanceWitness
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  witness : ctx.test.base.tauWitness
  imbalance :
    TauCriticalImbalance (ctx.test.tauNormalForm witness)

/-- A global B/C-imbalance witness is a global unit-axis witness. -/
def g8TauBCImbalanceWitness_to_unitAxisWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (w : G8TauBCImbalanceWitness ctx) :
    G8TauUnitAxisWitness ctx where
  witness := w.witness
  unitAxis :=
    (primePolarityAxisOffset_eq_one_iff_bcImbalance
      (ctx.test.tauNormalForm w.witness)).mpr w.imbalance

/-- A global critical-imbalance witness is a global B/C-imbalance witness. -/
def g8TauCriticalImbalanceWitness_to_bcImbalanceWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (w : G8TauCriticalImbalanceWitness ctx) :
    G8TauBCImbalanceWitness ctx where
  witness := w.witness
  imbalance :=
    (tauCriticalImbalance_iff_bcImbalance
      (ctx.test.tauNormalForm w.witness)).mp w.imbalance

/-- A global critical-imbalance witness is a global unit-axis witness. -/
def g8TauCriticalImbalanceWitness_to_unitAxisWitness
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (w : G8TauCriticalImbalanceWitness ctx) :
    G8TauUnitAxisWitness ctx :=
  g8TauBCImbalanceWitness_to_unitAxisWitness
    (g8TauCriticalImbalanceWitness_to_bcImbalanceWitness w)

/-- A global unit-axis witness supplies pointwise unit preimages. -/
theorem g8TauUnitAxisWitness_to_unitPreimages
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (w : G8TauUnitAxisWitness ctx) :
    G8OrthodoxTauUnitAxisPreimagesExist source := by
  intro _z _hOffAxis
  exact ⟨w.witness, w.unitAxis⟩

/-- A global B/C-imbalance witness supplies pointwise B/C-imbalance
    witnesses. -/
theorem g8TauBCImbalanceWitness_to_bcImbalanceWitnesses
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (w : G8TauBCImbalanceWitness ctx) :
    G8OrthodoxTauBCImbalanceWitnessesExist source := by
  intro _z _hOffAxis
  exact ⟨w.witness, w.imbalance⟩

/-- A global critical-imbalance witness supplies pointwise critical-imbalance
    witnesses. -/
theorem g8TauCriticalImbalanceWitness_to_criticalImbalanceWitnesses
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx)
    (w : G8TauCriticalImbalanceWitness ctx) :
    G8OrthodoxTauCriticalImbalanceWitnessesExist source := by
  intro _z _hOffAxis
  exact ⟨w.witness, w.imbalance⟩

-- ============================================================
-- SUPPLY CONTEXTS AND CORRIDOR ADAPTERS
-- ============================================================

/-- B/C-imbalance witness supply context for the normalized axis corridor. -/
structure G8OrthodoxTauUnitWitnessSupplyContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  source : G8OrthodoxShadowAxisSource ctx
  bcImbalanceWitnesses :
    G8OrthodoxTauBCImbalanceWitnessesExist source
  tauWitness :
    G8OffAxisTauWitnessRealization
      (g8OrthodoxShadowAxisSource_to_chart source)
  offAxisGuard :
    G8OffAxisChartOnlyGhostGuard
      (g8OrthodoxShadowAxisSource_to_chart source)

/-- Critical-imbalance witness supply context for the normalized axis
    corridor. -/
structure G8OrthodoxTauCriticalWitnessSupplyContext
    (ctx : G8WeakOffCriticalPullbackTestContext) where
  source : G8OrthodoxShadowAxisSource ctx
  criticalImbalanceWitnesses :
    G8OrthodoxTauCriticalImbalanceWitnessesExist source
  tauWitness :
    G8OffAxisTauWitnessRealization
      (g8OrthodoxShadowAxisSource_to_chart source)
  offAxisGuard :
    G8OffAxisChartOnlyGhostGuard
      (g8OrthodoxShadowAxisSource_to_chart source)

/-- B/C-imbalance witness supply feeds the normalized preimage context. -/
def g8OrthodoxTauUnitWitnessSupply_to_normalizedPreimageContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (supply : G8OrthodoxTauUnitWitnessSupplyContext ctx) :
    G8OrthodoxNormalizedAxisPreimageContext ctx where
  source := supply.source
  unitTauPreimages :=
    g8OrthodoxTauBCImbalanceWitnesses_to_unitAxisPreimages
      supply.source supply.bcImbalanceWitnesses
  tauWitness := supply.tauWitness
  offAxisGuard := supply.offAxisGuard

/-- Critical-imbalance witness supply feeds the B/C witness-supply context. -/
def g8OrthodoxTauCriticalWitnessSupply_to_unitWitnessSupply
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (supply : G8OrthodoxTauCriticalWitnessSupplyContext ctx) :
    G8OrthodoxTauUnitWitnessSupplyContext ctx where
  source := supply.source
  bcImbalanceWitnesses :=
    g8OrthodoxTauCriticalImbalanceWitnesses_to_bcImbalanceWitnesses
      supply.source supply.criticalImbalanceWitnesses
  tauWitness := supply.tauWitness
  offAxisGuard := supply.offAxisGuard

/-- Critical-imbalance witness supply feeds the normalized preimage context. -/
def g8OrthodoxTauCriticalWitnessSupply_to_normalizedPreimageContext
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (supply : G8OrthodoxTauCriticalWitnessSupplyContext ctx) :
    G8OrthodoxNormalizedAxisPreimageContext ctx :=
  g8OrthodoxTauUnitWitnessSupply_to_normalizedPreimageContext
    (g8OrthodoxTauCriticalWitnessSupply_to_unitWitnessSupply supply)

/-- B/C witness supply yields the local one-sided pullback. -/
theorem g8OrthodoxTauUnitWitnessSupply_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (supply : G8OrthodoxTauUnitWitnessSupplyContext ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8OrthodoxNormalizedAxisPreimage_yields_pullback ctx
    (g8OrthodoxTauUnitWitnessSupply_to_normalizedPreimageContext supply)

/-- Critical witness supply yields the local one-sided pullback. -/
theorem g8OrthodoxTauCriticalWitnessSupply_yields_pullback
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (supply : G8OrthodoxTauCriticalWitnessSupplyContext ctx) :
    G8eOffCriticalPullback ctx.test.base :=
  g8OrthodoxNormalizedAxisPreimage_yields_pullback ctx
    (g8OrthodoxTauCriticalWitnessSupply_to_normalizedPreimageContext supply)

/-- B/C witness supply plus tau-side purity yields local no-off-critical
    orthodox zeros. -/
theorem g8OrthodoxTauUnitWitnessSupply_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (supply : G8OrthodoxTauUnitWitnessSupplyContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OrthodoxNormalizedAxisPreimage_noOffCriticalZeros ctx
    (g8OrthodoxTauUnitWitnessSupply_to_normalizedPreimageContext supply)
    tauPurity

/-- Critical witness supply plus tau-side purity yields local no-off-critical
    orthodox zeros. -/
theorem g8OrthodoxTauCriticalWitnessSupply_noOffCriticalZeros
    (ctx : G8WeakOffCriticalPullbackTestContext)
    (supply : G8OrthodoxTauCriticalWitnessSupplyContext ctx)
    (tauPurity : G8eTauPurityExcludesOffCritical ctx.test.base) :
    G8eNoOrthodoxOffCriticalZeros ctx.test.base :=
  g8OrthodoxNormalizedAxisPreimage_noOffCriticalZeros ctx
    (g8OrthodoxTauCriticalWitnessSupply_to_normalizedPreimageContext supply)
    tauPurity

-- ============================================================
-- WITNESS-SUPPLY FALSIFIERS
-- ============================================================

/-- At an off-axis orthodox shadow, no B/C-imbalance tau witness is available. -/
structure G8OrthodoxTauBCImbalanceWitnessUnavailable
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  offAxis :
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z
  noBCWitness :
    ∀ w : ctx.test.base.tauWitness,
      ¬ TauBCImbalance (ctx.test.tauNormalForm w)

/-- At an off-axis orthodox shadow, no critical-imbalance tau witness is
    available. -/
structure G8OrthodoxTauCriticalImbalanceWitnessUnavailable
    {ctx : G8WeakOffCriticalPullbackTestContext}
    (source : G8OrthodoxShadowAxisSource ctx) where
  z : ctx.test.base.orthodoxZero
  offAxis :
    G8ChartOffAxis (g8OrthodoxShadowAxisSource_to_chart source) z
  noCriticalWitness :
    ∀ w : ctx.test.base.tauWitness,
      ¬ TauCriticalImbalance (ctx.test.tauNormalForm w)

/-- Missing B/C-imbalance witnesses refute B/C witness supply. -/
theorem g8OrthodoxTauBCImbalanceWitnessUnavailable_refutes_bcSupply
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8OrthodoxTauBCImbalanceWitnessUnavailable source) :
    ¬ G8OrthodoxTauBCImbalanceWitnessesExist source := by
  intro hSupply
  obtain ⟨tauW, hBC⟩ := hSupply w.z w.offAxis
  exact w.noBCWitness tauW hBC

/-- Missing critical-imbalance witnesses refute critical witness supply. -/
theorem
    g8OrthodoxTauCriticalImbalanceWitnessUnavailable_refutes_criticalSupply
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {source : G8OrthodoxShadowAxisSource ctx}
    (w : G8OrthodoxTauCriticalImbalanceWitnessUnavailable source) :
    ¬ G8OrthodoxTauCriticalImbalanceWitnessesExist source := by
  intro hSupply
  obtain ⟨tauW, hCrit⟩ := hSupply w.z w.offAxis
  exact w.noCriticalWitness tauW hCrit

/-- Missing B/C witnesses refute the B/C supply context. -/
theorem
    g8OrthodoxTauBCImbalanceWitnessUnavailable_refutes_unitWitnessSupply
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {supply : G8OrthodoxTauUnitWitnessSupplyContext ctx}
    (w : G8OrthodoxTauBCImbalanceWitnessUnavailable supply.source) :
    False :=
  g8OrthodoxTauBCImbalanceWitnessUnavailable_refutes_bcSupply w
    supply.bcImbalanceWitnesses

/-- Missing critical witnesses refute the critical supply context. -/
theorem
    g8OrthodoxTauCriticalImbalanceWitnessUnavailable_refutes_criticalWitnessSupply
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {supply : G8OrthodoxTauCriticalWitnessSupplyContext ctx}
    (w : G8OrthodoxTauCriticalImbalanceWitnessUnavailable supply.source) :
    False :=
  g8OrthodoxTauCriticalImbalanceWitnessUnavailable_refutes_criticalSupply w
    supply.criticalImbalanceWitnesses

/-- Missing B/C witnesses also refute critical witness supply, since critical
    imbalance implies B/C imbalance. -/
theorem
    g8OrthodoxTauBCImbalanceWitnessUnavailable_refutes_criticalWitnessSupply
    {ctx : G8WeakOffCriticalPullbackTestContext}
    {supply : G8OrthodoxTauCriticalWitnessSupplyContext ctx}
    (w : G8OrthodoxTauBCImbalanceWitnessUnavailable supply.source) :
    False :=
  g8OrthodoxTauBCImbalanceWitnessUnavailable_refutes_bcSupply w
    (g8OrthodoxTauCriticalImbalanceWitnesses_to_bcImbalanceWitnesses
      supply.source supply.criticalImbalanceWitnesses)

end Tau.BookIII.Bridge
