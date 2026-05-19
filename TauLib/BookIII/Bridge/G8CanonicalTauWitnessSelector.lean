import TauLib.BookIII.Bridge.G8CanonicalTauWitnessContext

/-!
# TauLib.BookIII.Bridge.G8CanonicalTauWitnessSelector

Pointwise canonical tau-witness selector for the G8f corridor.

`G8CanonicalTauWitnessContext` instantiated the tau witness carrier as
provenance-backed canonical boundary witnesses.  This module sharpens that
carrier into a pointwise selector: for each readable off-axis orthodox shadow,
it selects the canonical tau witness whose normal form is the shadow-selected
boundary normal form.

The selector proves the local facts needed by the current corridor:

* the selected carrier witness has the selected normal form;
* the selected normal form is B/C-imbalanced and tau-critical-imbalanced;
* the selected witness has unit prime-polarity axis offset;
* the selected witness satisfies the normalized orthodox/tau axis relation.

Tau-side purity remains external.  This module does not prove the analytic
xi chart, O3 correspondence, divisor transfer, or the final global target.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- POINTWISE SELECTOR
-- ============================================================

/-- The explicit chart object induced by the canonical tau-witness source. -/
abbrev g8CanonicalTauWitness_chart
    (source : G8CanonicalTauWitnessSource) :
    G8OffAxisChartObject (g8CanonicalTauWitness_weak source) :=
  g8OrthodoxShadowAxisSource_to_chart
    (g8CanonicalTauWitness_shadowAxisSource source)

/-- The canonical boundary witness selected by one readable off-axis shadow. -/
def g8CanonicalBoundaryWitnessForOffAxis
    (source : G8CanonicalTauWitnessSource)
    (z : source.orthodoxZero)
    (hOffAxis :
      G8ChartOffAxis (g8CanonicalTauWitness_chart source) z) :
    G8CanonicalBoundaryWitness :=
  (g8TauShadowSelectedCanonicalBoundaryRealization
    (g8CanonicalTauWitness_shadowAxisSource source)).realize
      z hOffAxis

/-- The selected canonical boundary witness has exactly the normal form
    selected by the centered shadow. -/
theorem g8CanonicalBoundaryWitnessForOffAxis_normalForm
    (source : G8CanonicalTauWitnessSource)
    (z : source.orthodoxZero)
    (hOffAxis :
      G8ChartOffAxis (g8CanonicalTauWitness_chart source) z) :
    (g8CanonicalBoundaryWitnessForOffAxis source z hOffAxis).nf =
      g8TauShadowSelectedNormalForm (source.centeredShadow z) :=
  (g8TauShadowSelectedCanonicalBoundaryRealization
    (g8CanonicalTauWitness_shadowAxisSource source)).realize_selected
      z hOffAxis

/-- The canonical tau carrier witness selected by one readable off-axis
    shadow. -/
def g8CanonicalTauWitnessForOffAxis
    (source : G8CanonicalTauWitnessSource)
    (z : source.orthodoxZero)
    (hOffAxis :
      G8ChartOffAxis (g8CanonicalTauWitness_chart source) z) :
    (g8CanonicalTauWitness_base source).tauWitness :=
  ULift.up (g8CanonicalBoundaryWitnessForOffAxis source z hOffAxis)

/-- The selected canonical tau witness has exactly the normal form selected
    by the centered shadow. -/
theorem g8CanonicalTauWitnessForOffAxis_normalForm
    (source : G8CanonicalTauWitnessSource)
    (z : source.orthodoxZero)
    (hOffAxis :
      G8ChartOffAxis (g8CanonicalTauWitness_chart source) z) :
    (g8CanonicalTauWitness_test source).tauNormalForm
        (g8CanonicalTauWitnessForOffAxis source z hOffAxis) =
      g8TauShadowSelectedNormalForm (source.centeredShadow z) :=
  g8CanonicalBoundaryWitnessForOffAxis_normalForm source z hOffAxis

/-- Pointwise selector package for the canonical tau-witness carrier. -/
structure G8CanonicalTauWitnessPointwiseSelector
    (source : G8CanonicalTauWitnessSource) where
  select :
    ∀ (z : source.orthodoxZero),
      G8ChartOffAxis (g8CanonicalTauWitness_chart source) z →
        (g8CanonicalTauWitness_base source).tauWitness
  select_normalForm :
    ∀ (z : source.orthodoxZero)
      (hOffAxis :
        G8ChartOffAxis (g8CanonicalTauWitness_chart source) z),
      (g8CanonicalTauWitness_test source).tauNormalForm
          (select z hOffAxis) =
        g8TauShadowSelectedNormalForm (source.centeredShadow z)

/-- The concrete canonical pointwise selector. -/
def g8CanonicalTauWitness_pointwiseSelector
    (source : G8CanonicalTauWitnessSource) :
    G8CanonicalTauWitnessPointwiseSelector source where
  select := g8CanonicalTauWitnessForOffAxis source
  select_normalForm :=
    g8CanonicalTauWitnessForOffAxis_normalForm source

-- ============================================================
-- SELECTOR FACTS
-- ============================================================

/-- The selected pointwise witness has B/C imbalance. -/
theorem g8CanonicalTauWitnessForOffAxis_bcImbalance
    (source : G8CanonicalTauWitnessSource)
    (z : source.orthodoxZero)
    (hOffAxis :
      G8ChartOffAxis (g8CanonicalTauWitness_chart source) z) :
    TauBCImbalance
      ((g8CanonicalTauWitness_test source).tauNormalForm
        (g8CanonicalTauWitnessForOffAxis source z hOffAxis)) := by
  rw [g8CanonicalTauWitnessForOffAxis_normalForm]
  exact
    g8TauShadowSelectedNormalForm_offAxis_bcImbalance
      (source.centeredShadow z)
      (g8OrthodoxShadowAxisSource_chartOffAxis_to_sourceOffAxis
        (g8CanonicalTauWitness_shadowAxisSource source) z hOffAxis)

/-- The selected pointwise witness has tau critical-locus imbalance. -/
theorem g8CanonicalTauWitnessForOffAxis_criticalImbalance
    (source : G8CanonicalTauWitnessSource)
    (z : source.orthodoxZero)
    (hOffAxis :
      G8ChartOffAxis (g8CanonicalTauWitness_chart source) z) :
    TauCriticalImbalance
      ((g8CanonicalTauWitness_test source).tauNormalForm
        (g8CanonicalTauWitnessForOffAxis source z hOffAxis)) :=
  (tauCriticalImbalance_iff_bcImbalance
    ((g8CanonicalTauWitness_test source).tauNormalForm
      (g8CanonicalTauWitnessForOffAxis source z hOffAxis))).mpr
    (g8CanonicalTauWitnessForOffAxis_bcImbalance
      source z hOffAxis)

/-- The selected pointwise witness is an off-critical tau witness in the
    canonical pullback context. -/
theorem g8CanonicalTauWitnessForOffAxis_tauOffCritical
    (source : G8CanonicalTauWitnessSource)
    (z : source.orthodoxZero)
    (hOffAxis :
      G8ChartOffAxis (g8CanonicalTauWitness_chart source) z) :
    TauOffCriticalWitness
      (g8CanonicalTauWitness_base source)
      (g8CanonicalTauWitnessForOffAxis source z hOffAxis) := by
  change
    TauCriticalImbalance
      ((g8CanonicalTauWitness_test source).tauNormalForm
        (g8CanonicalTauWitnessForOffAxis source z hOffAxis))
  exact g8CanonicalTauWitnessForOffAxis_criticalImbalance
    source z hOffAxis

/-- The selected pointwise witness has unit prime-polarity axis offset. -/
theorem g8CanonicalTauWitnessForOffAxis_unitAxis
    (source : G8CanonicalTauWitnessSource)
    (z : source.orthodoxZero)
    (hOffAxis :
      G8ChartOffAxis (g8CanonicalTauWitness_chart source) z) :
    primePolarityAxisOffset
      ((g8CanonicalTauWitness_test source).tauNormalForm
        (g8CanonicalTauWitnessForOffAxis source z hOffAxis)) = 1 :=
  (primePolarityAxisOffset_eq_one_iff_bcImbalance
    ((g8CanonicalTauWitness_test source).tauNormalForm
      (g8CanonicalTauWitnessForOffAxis source z hOffAxis))).mpr
    (g8CanonicalTauWitnessForOffAxis_bcImbalance
      source z hOffAxis)

/-- The selected pointwise witness satisfies the normalized orthodox/tau axis
    relation. -/
theorem g8CanonicalTauWitnessForOffAxis_normalizedRelated
    (source : G8CanonicalTauWitnessSource)
    (z : source.orthodoxZero)
    (hOffAxis :
      G8ChartOffAxis (g8CanonicalTauWitness_chart source) z) :
    G8OrthodoxTauNormalizedAxisRelated
      (g8CanonicalTauWitness_shadowAxisSource source)
      z
      (g8CanonicalTauWitnessForOffAxis source z hOffAxis) := by
  unfold G8OrthodoxTauNormalizedAxisRelated
  exact
    (normalizedAxisOffset_eq_one_of_offAxis hOffAxis).trans
      (g8CanonicalTauWitnessForOffAxis_unitAxis
        source z hOffAxis).symm

-- ============================================================
-- ADAPTERS INTO THE NORMALIZED CORRIDOR
-- ============================================================

/-- The pointwise selector supplies B/C-imbalance witnesses for every readable
    off-axis orthodox shadow. -/
theorem g8CanonicalTauWitness_selector_to_bcImbalanceWitnesses
    (source : G8CanonicalTauWitnessSource) :
    G8OrthodoxTauBCImbalanceWitnessesExist
      (g8CanonicalTauWitness_shadowAxisSource source) := by
  intro z hOffAxis
  exact
    ⟨g8CanonicalTauWitnessForOffAxis source z hOffAxis,
      g8CanonicalTauWitnessForOffAxis_bcImbalance
        source z hOffAxis⟩

/-- The pointwise selector supplies critical-imbalance witnesses for every
    readable off-axis orthodox shadow. -/
theorem g8CanonicalTauWitness_selector_to_criticalImbalanceWitnesses
    (source : G8CanonicalTauWitnessSource) :
    G8OrthodoxTauCriticalImbalanceWitnessesExist
      (g8CanonicalTauWitness_shadowAxisSource source) := by
  intro z hOffAxis
  exact
    ⟨g8CanonicalTauWitnessForOffAxis source z hOffAxis,
      g8CanonicalTauWitnessForOffAxis_criticalImbalance
        source z hOffAxis⟩

/-- The pointwise selector supplies unit tau preimages for the normalized
    off-axis relation. -/
theorem g8CanonicalTauWitness_selector_to_unitPreimages
    (source : G8CanonicalTauWitnessSource) :
    G8OrthodoxTauUnitAxisPreimagesExist
      (g8CanonicalTauWitness_shadowAxisSource source) := by
  intro z hOffAxis
  exact
    ⟨g8CanonicalTauWitnessForOffAxis source z hOffAxis,
      g8CanonicalTauWitnessForOffAxis_unitAxis source z hOffAxis⟩

/-- The pointwise selector supplies normalized-axis preimages. -/
theorem g8CanonicalTauWitness_selector_to_normalizedPreimages
    (source : G8CanonicalTauWitnessSource) :
    G8OrthodoxTauNormalizedAxisPreimagesExist
      (g8CanonicalTauWitness_shadowAxisSource source) :=
  g8OrthodoxTauUnitPreimages_to_normalizedPreimages
    (g8CanonicalTauWitness_shadowAxisSource source)
    (g8CanonicalTauWitness_selector_to_unitPreimages source)

/-- The pointwise selector gives the normalized preimage context consumed by
    the existing G8f corridor. -/
def g8CanonicalTauWitness_selector_to_normalizedPreimageContext
    (source : G8CanonicalTauWitnessSource) :
    G8OrthodoxNormalizedAxisPreimageContext
      (g8CanonicalTauWitness_weak source) where
  source := g8CanonicalTauWitness_shadowAxisSource source
  unitTauPreimages :=
    g8CanonicalTauWitness_selector_to_unitPreimages source
  tauWitness := g8CanonicalTauWitness_tauWitnessRealization source
  offAxisGuard := g8CanonicalTauWitness_offAxisGuard source

/-- The pointwise selector yields the local one-sided pullback through the
    normalized relation corridor. -/
theorem g8CanonicalTauWitness_selector_yields_pullback
    (source : G8CanonicalTauWitnessSource) :
    G8eOffCriticalPullback
      (g8CanonicalTauWitness_base source) :=
  g8OrthodoxNormalizedAxisPreimage_yields_pullback
    (g8CanonicalTauWitness_weak source)
    (g8CanonicalTauWitness_selector_to_normalizedPreimageContext source)

/-- The pointwise selector plus tau-side purity yields local no-off-critical
    orthodox zeros through the normalized relation corridor. -/
theorem g8CanonicalTauWitness_selector_noOffCriticalZeros
    (source : G8CanonicalTauWitnessSource)
    (tauPurity :
      G8eTauPurityExcludesOffCritical
        (g8CanonicalTauWitness_base source)) :
    G8eNoOrthodoxOffCriticalZeros
      (g8CanonicalTauWitness_base source) :=
  g8OrthodoxNormalizedAxisPreimage_noOffCriticalZeros
    (g8CanonicalTauWitness_weak source)
    (g8CanonicalTauWitness_selector_to_normalizedPreimageContext source)
    tauPurity

-- ============================================================
-- POINTWISE FALSIFIER CLOSURE
-- ============================================================

/-- A readable off-axis shadow whose selected normal form has no carrier
    witness. -/
structure G8CanonicalSelectedWitnessUnavailable
    (source : G8CanonicalTauWitnessSource) where
  z : source.orthodoxZero
  offAxis :
    G8ChartOffAxis (g8CanonicalTauWitness_chart source) z
  noSelectedWitness :
    ∀ w : (g8CanonicalTauWitness_base source).tauWitness,
      (g8CanonicalTauWitness_test source).tauNormalForm w ≠
        g8TauShadowSelectedNormalForm (source.centeredShadow z)

/-- The canonical pointwise selector refutes missing selected carrier
    witnesses. -/
theorem g8CanonicalSelectedWitnessUnavailable_refutes_selector
    {source : G8CanonicalTauWitnessSource}
    (w : G8CanonicalSelectedWitnessUnavailable source) :
    False :=
  w.noSelectedWitness
    (g8CanonicalTauWitnessForOffAxis source w.z w.offAxis)
    (g8CanonicalTauWitnessForOffAxis_normalForm
      source w.z w.offAxis)

/-- A readable off-axis shadow with no normalized tau preimage. -/
structure G8CanonicalNormalizedPreimageUnavailable
    (source : G8CanonicalTauWitnessSource) where
  z : source.orthodoxZero
  offAxis :
    G8ChartOffAxis (g8CanonicalTauWitness_chart source) z
  noNormalizedPreimage :
    ∀ w : (g8CanonicalTauWitness_base source).tauWitness,
      ¬ G8OrthodoxTauNormalizedAxisRelated
        (g8CanonicalTauWitness_shadowAxisSource source) z w

/-- The canonical pointwise selector refutes missing normalized preimages. -/
theorem g8CanonicalNormalizedPreimageUnavailable_refutes_selector
    {source : G8CanonicalTauWitnessSource}
    (w : G8CanonicalNormalizedPreimageUnavailable source) :
    False :=
  w.noNormalizedPreimage
    (g8CanonicalTauWitnessForOffAxis source w.z w.offAxis)
    (g8CanonicalTauWitnessForOffAxis_normalizedRelated
      source w.z w.offAxis)

/-- Any off-axis chart-only ghost for the canonical carrier is refuted by the
    pointwise selected canonical tau witness at that same shadow. -/
theorem g8CanonicalTauWitness_offAxisGhost_refutes_pointwiseSelector
    (source : G8CanonicalTauWitnessSource)
    (ghost :
      G8OffAxisChartOnlyGhostWitness
        (g8CanonicalTauWitness_test source)) :
    False := by
  have hOffAxis :
      G8ChartOffAxis (g8CanonicalTauWitness_chart source) ghost.z :=
    g8ChartOffAxis_from_context
      (g8CanonicalTauWitness_chart source)
      ghost.offAxis
  exact
    ghost.noTauPreimage
      (g8CanonicalTauWitnessForOffAxis source ghost.z hOffAxis)
      (g8CanonicalTauWitnessForOffAxis_tauOffCritical
        source ghost.z hOffAxis)

/-- The canonical off-axis guard can be proved pointwise, not merely from a
    global sample witness. -/
theorem g8CanonicalTauWitness_offAxisGuard_pointwise
    (source : G8CanonicalTauWitnessSource) :
    G8OffAxisChartOnlyGhostGuard
      (g8CanonicalTauWitness_chart source) := by
  intro hGhost
  rcases hGhost with ⟨ghost⟩
  exact g8CanonicalTauWitness_offAxisGhost_refutes_pointwiseSelector
    source ghost

end Tau.BookIII.Bridge
