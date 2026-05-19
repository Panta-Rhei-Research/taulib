import TauLib.BookIII.Bridge.G8ActualXiZetaThinSource
import TauLib.BookIII.Bridge.G8ActualXiZetaCanonicalPreimageRealization

/-!
# TauLib.BookIII.Bridge.G8ActualXiZetaStrictPointGeometry

Strict point-geometry target for actual off-axis `xi` shadows.

The canonical preimage realization proves the current pointwise no-ghost
contract.  This module strengthens the bookkeeping around that witness: a
pointwise tau preimage should carry a canonical finite boundary address and
agree with the chart-selected boundary normal form.

The key discipline is still local and conditional.  We do not prove O3,
analytic-completion uniqueness, full divisor transfer, tau purity, or RH.
We only make the tau witness provenance explicit enough for the next proof
wave to ask whether the canonical selected witness is geometrically
point-specific in the stronger address-resolution sense.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- CANONICAL THIN SOURCE
-- ============================================================

/-- The canonical actual `xi`/`zeta` source as a thin source.

This forgets the full G8d transfer object except for its receiving chart and
the G3/G4 readout proofs. -/
def g8ActualXiZetaCanonical_to_thinSource
    (source : G8ActualXiZetaCanonicalPreimageSource) :
    G8ActualXiZetaThinSourceContext where
  chart := source.transfer.completion.chart
  tauWitness := G8CanonicalTauWitnessCarrier
  tauNormalForm := fun w => w.down.nf
  g3ZetaChartReadout := source.g3ZetaChartReadout
  g4CompletedXiReadout := source.g4CompletedXiReadout
  status := .conditionalExclusionAvailable

/-- Thin off-axis readability for the canonical actual source is the same
    off-axis predicate consumed by the canonical tau-witness selector. -/
theorem g8ActualXiZetaCanonical_thinOffAxis_to_canonicalOffAxis
    (source : G8ActualXiZetaCanonicalPreimageSource)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (g8ActualXiZetaCanonical_to_thinSource source) z) :
    G8ChartOffAxis
      (g8CanonicalTauWitness_chart
        (g8ActualXiZetaCanonical_to_canonicalSource source)) z := by
  change ShadowOffAxis (orthodoxXiCarrierCenteredShadow z)
  change ShadowOffAxis (orthodoxXiCarrierCenteredShadow z) at hOffAxis
  exact hOffAxis

/-- The canonical boundary witness selected for one thin off-axis actual
    `xi` shadow. -/
def g8ActualXiZetaCanonicalBoundaryForThinOffAxis
    (source : G8ActualXiZetaCanonicalPreimageSource)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (g8ActualXiZetaCanonical_to_thinSource source) z) :
    G8CanonicalBoundaryWitness :=
  g8CanonicalBoundaryWitnessForOffAxis
    (g8ActualXiZetaCanonical_to_canonicalSource source)
    z
    (g8ActualXiZetaCanonical_thinOffAxis_to_canonicalOffAxis
      source z hOffAxis)

/-- The canonical tau carrier witness selected for one thin off-axis actual
    `xi` shadow. -/
def g8ActualXiZetaCanonicalWitnessForThinOffAxis
    (source : G8ActualXiZetaCanonicalPreimageSource)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (g8ActualXiZetaCanonical_to_thinSource source) z) :
    (g8ActualXiZetaCanonical_to_thinSource source).tauWitness :=
  ULift.up
    (g8ActualXiZetaCanonicalBoundaryForThinOffAxis
      source z hOffAxis)

-- ============================================================
-- STRICT POINT-GEOMETRY CONTRACT
-- ============================================================

/-- Strict point-geometry contract over a thin actual `xi` source.

In addition to the normalized-axis relation and tau critical imbalance, this
contract records the canonical finite boundary witness/address that realizes
the selected tau normal form for each off-axis receiving shadow. -/
structure G8ActualXiZetaThinStrictPointGeometryTarget
    (source : G8ActualXiZetaThinSourceContext) where
  pointSpecificWitness :
    ∀ z : OrthodoxXiZeroCarrier,
      G8ActualXiZetaThinChartOffAxis source z →
        source.tauWitness
  canonicalBoundaryAddress :
    ∀ (z : OrthodoxXiZeroCarrier)
      (_hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
        G8CanonicalBoundaryWitness
  witness_normalForm_eq_address :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      source.tauNormalForm (pointSpecificWitness z hOffAxis) =
        (canonicalBoundaryAddress z hOffAxis).nf
  address_selectedShadow :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      (canonicalBoundaryAddress z hOffAxis).nf =
        g8TauShadowSelectedNormalForm
          (g8ActualXiZetaThinCenteredShadow source z)
  normalizedRelated :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      G8ActualXiZetaThinNormalizedAxisRelated
        source z (pointSpecificWitness z hOffAxis)
  criticalImbalance :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      TauCriticalImbalance
        (source.tauNormalForm (pointSpecificWitness z hOffAxis))
  nonSampleGeometryDiscipline : Prop

/-- The strict point-geometry target exposes finite boundary-address
    realizability for every selected witness. -/
theorem
    g8ActualXiZetaThinStrictPointGeometry_witnessRealizable
    {source : G8ActualXiZetaThinSourceContext}
    (target : G8ActualXiZetaThinStrictPointGeometryTarget source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    BoundaryNFRealizable
      (source.tauNormalForm
        (target.pointSpecificWitness z hOffAxis)) := by
  rw [target.witness_normalForm_eq_address z hOffAxis]
  exact
    g8CanonicalBoundaryWitness_realizable
      (target.canonicalBoundaryAddress z hOffAxis)

/-- The strict point-geometry target exposes selected-shadow normal-form
    agreement for every pointwise witness. -/
theorem
    g8ActualXiZetaThinStrictPointGeometry_selectedNormalForm
    {source : G8ActualXiZetaThinSourceContext}
    (target : G8ActualXiZetaThinStrictPointGeometryTarget source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    source.tauNormalForm
        (target.pointSpecificWitness z hOffAxis) =
      g8TauShadowSelectedNormalForm
        (g8ActualXiZetaThinCenteredShadow source z) := by
  rw [
    target.witness_normalForm_eq_address z hOffAxis,
    target.address_selectedShadow z hOffAxis
  ]

/-- Strict point geometry supplies the thin pointwise preimage contract. -/
theorem
    g8ActualXiZetaThinStrictPointGeometry_to_pointwise
    {source : G8ActualXiZetaThinSourceContext}
    (target : G8ActualXiZetaThinStrictPointGeometryTarget source) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist source := by
  intro z hOffAxis
  exact
    ⟨target.pointSpecificWitness z hOffAxis,
      ⟨target.normalizedRelated z hOffAxis,
        target.criticalImbalance z hOffAxis⟩⟩

-- ============================================================
-- CANONICAL STRICT TARGET
-- ============================================================

/-- The canonical actual source satisfies the strict point-geometry contract
    over the thin source. -/
def g8ActualXiZetaCanonical_to_thinStrictPointGeometry
    (source : G8ActualXiZetaCanonicalPreimageSource) :
    G8ActualXiZetaThinStrictPointGeometryTarget
      (g8ActualXiZetaCanonical_to_thinSource source) where
  pointSpecificWitness :=
    g8ActualXiZetaCanonicalWitnessForThinOffAxis source
  canonicalBoundaryAddress :=
    g8ActualXiZetaCanonicalBoundaryForThinOffAxis source
  witness_normalForm_eq_address := by
    intro z hOffAxis
    rfl
  address_selectedShadow := by
    intro z hOffAxis
    exact
      g8CanonicalBoundaryWitnessForOffAxis_normalForm
        (g8ActualXiZetaCanonical_to_canonicalSource source)
        z
        (g8ActualXiZetaCanonical_thinOffAxis_to_canonicalOffAxis
          source z hOffAxis)
  normalizedRelated := by
    intro z hOffAxis
    unfold G8ActualXiZetaThinNormalizedAxisRelated
    have hNorm :
        normalizedAxisOffset
            (g8ActualXiZetaThinCenteredShadow
              (g8ActualXiZetaCanonical_to_thinSource source) z) = 1 :=
      normalizedAxisOffset_eq_one_of_offAxis hOffAxis
    have hUnit :
        primePolarityAxisOffset
          ((g8ActualXiZetaCanonical_to_thinSource source).tauNormalForm
            (g8ActualXiZetaCanonicalWitnessForThinOffAxis
              source z hOffAxis)) = 1 := by
      simpa [
        g8ActualXiZetaCanonical_to_thinSource,
        g8ActualXiZetaCanonicalWitnessForThinOffAxis
      ] using
        g8CanonicalTauWitnessForOffAxis_unitAxis
          (g8ActualXiZetaCanonical_to_canonicalSource source)
          z
          (g8ActualXiZetaCanonical_thinOffAxis_to_canonicalOffAxis
            source z hOffAxis)
    exact hNorm.trans hUnit.symm
  criticalImbalance := by
    intro z hOffAxis
    simpa [
      g8ActualXiZetaCanonical_to_thinSource,
      g8ActualXiZetaCanonicalWitnessForThinOffAxis
    ] using
      g8CanonicalTauWitnessForOffAxis_criticalImbalance
        (g8ActualXiZetaCanonical_to_canonicalSource source)
        z
        (g8ActualXiZetaCanonical_thinOffAxis_to_canonicalOffAxis
          source z hOffAxis)
  nonSampleGeometryDiscipline := True

/-- The canonical strict point-geometry contract supplies the thin pointwise
    preimage contract. -/
theorem
    g8ActualXiZetaCanonical_thinStrictPointGeometry_to_pointwise
    (source : G8ActualXiZetaCanonicalPreimageSource) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist
      (g8ActualXiZetaCanonical_to_thinSource source) :=
  g8ActualXiZetaThinStrictPointGeometry_to_pointwise
    (g8ActualXiZetaCanonical_to_thinStrictPointGeometry source)

end Tau.BookIII.Bridge
