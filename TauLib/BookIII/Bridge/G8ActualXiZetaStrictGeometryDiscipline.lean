import TauLib.BookIII.Bridge.G8ActualXiZetaStrictGeometryCorridor

/-!
# TauLib.BookIII.Bridge.G8ActualXiZetaStrictGeometryDiscipline

Strict point-geometry discipline for the actual `xi` no-ghost corridor.

The previous strict target carried a marker field
`nonSampleGeometryDiscipline : Prop`.  This module replaces that marker, at
the proof-facing layer, by explicit facts:

* the selected witness normal form is finite-stage realizable;
* the selected witness normal form is exactly the chart-selected boundary
  normal form;
* the canonical boundary address realizes the same selected normal form;
* off-axis selected addresses carry the unit axis class and tau critical
  imbalance.

The module also isolates the handoff where an actual off-axis `xi` shadow is
sent to a canonical tau boundary address.  This is still local chart/corridor
engineering: it does not prove O3, analytic-completion uniqueness, full
divisor transfer, tau purity, or the final RH target.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- STRICT DISCIPLINE FIELDS
-- ============================================================

/-- Explicit replacement for the old non-sample discipline marker.

The fields say precisely what a strict point-geometry target must provide
about its pointwise tau witness and its canonical boundary address. -/
structure G8ActualXiZetaThinStrictPointGeometryDiscipline
    (source : G8ActualXiZetaThinSourceContext)
    (target : G8ActualXiZetaThinStrictPointGeometryTarget source) where
  witnessRealizable :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      BoundaryNFRealizable
        (source.tauNormalForm
          (target.pointSpecificWitness z hOffAxis))
  witnessNormalForm_eq_selected :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      source.tauNormalForm
          (target.pointSpecificWitness z hOffAxis) =
        g8TauShadowSelectedNormalForm
          (g8ActualXiZetaThinCenteredShadow source z)
  addressRealizable :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      BoundaryNFRealizable
        ((target.canonicalBoundaryAddress z hOffAxis).nf)
  addressNormalForm_eq_selected :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      (target.canonicalBoundaryAddress z hOffAxis).nf =
        g8TauShadowSelectedNormalForm
          (g8ActualXiZetaThinCenteredShadow source z)
  address_unitAxis :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      primePolarityAxisOffset
        ((target.canonicalBoundaryAddress z hOffAxis).nf) = 1
  address_criticalImbalance :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      TauCriticalImbalance
        ((target.canonicalBoundaryAddress z hOffAxis).nf)

/-- Every strict point-geometry target canonically supplies the explicit
    discipline fields. -/
def g8ActualXiZetaThinStrictPointGeometry_discipline
    {source : G8ActualXiZetaThinSourceContext}
    (target : G8ActualXiZetaThinStrictPointGeometryTarget source) :
    G8ActualXiZetaThinStrictPointGeometryDiscipline source target where
  witnessRealizable :=
    g8ActualXiZetaThinStrictPointGeometry_witnessRealizable target
  witnessNormalForm_eq_selected :=
    g8ActualXiZetaThinStrictPointGeometry_selectedNormalForm target
  addressRealizable := by
    intro z hOffAxis
    exact
      g8CanonicalBoundaryWitness_realizable
        (target.canonicalBoundaryAddress z hOffAxis)
  addressNormalForm_eq_selected := by
    intro z hOffAxis
    exact target.address_selectedShadow z hOffAxis
  address_unitAxis := by
    intro z hOffAxis
    have hOff :
        ShadowOffAxis
          (g8ActualXiZetaThinCenteredShadow source z) :=
      hOffAxis
    have hBC :
        TauBCImbalance
          ((target.canonicalBoundaryAddress z hOffAxis).nf) := by
      rw [target.address_selectedShadow z hOffAxis]
      exact
        g8TauShadowSelectedNormalForm_offAxis_bcImbalance
          (g8ActualXiZetaThinCenteredShadow source z) hOff
    exact
      (primePolarityAxisOffset_eq_one_iff_bcImbalance
        ((target.canonicalBoundaryAddress z hOffAxis).nf)).mpr hBC
  address_criticalImbalance := by
    intro z hOffAxis
    have hOff :
        ShadowOffAxis
          (g8ActualXiZetaThinCenteredShadow source z) :=
      hOffAxis
    have hBC :
        TauBCImbalance
          ((target.canonicalBoundaryAddress z hOffAxis).nf) := by
      rw [target.address_selectedShadow z hOffAxis]
      exact
        g8TauShadowSelectedNormalForm_offAxis_bcImbalance
          (g8ActualXiZetaThinCenteredShadow source z) hOff
    exact
      (tauCriticalImbalance_iff_bcImbalance
        ((target.canonicalBoundaryAddress z hOffAxis).nf)).mpr hBC

/-- Certified strict point-geometry target: the old target plus explicit
    discipline fields. -/
structure G8ActualXiZetaThinCertifiedStrictPointGeometry
    (source : G8ActualXiZetaThinSourceContext) where
  target : G8ActualXiZetaThinStrictPointGeometryTarget source
  discipline :
    G8ActualXiZetaThinStrictPointGeometryDiscipline source target :=
      g8ActualXiZetaThinStrictPointGeometry_discipline target

/-- A certified strict target still supplies the thin pointwise preimage
    contract. -/
theorem
    g8ActualXiZetaThinCertifiedStrictPointGeometry_to_pointwise
    {source : G8ActualXiZetaThinSourceContext}
    (cert : G8ActualXiZetaThinCertifiedStrictPointGeometry source) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist source :=
  g8ActualXiZetaThinStrictPointGeometry_to_pointwise cert.target

-- ============================================================
-- ACTUAL SHADOW TO CANONICAL BOUNDARY ADDRESS HANDOFF
-- ============================================================

/-- Handoff object for the exact step:
    actual off-axis `xi` shadow -> canonical tau boundary address. -/
structure G8ActualXiZetaThinBoundaryAddressHandoff
    (source : G8ActualXiZetaThinSourceContext) where
  address :
    ∀ (z : OrthodoxXiZeroCarrier),
      G8ActualXiZetaThinChartOffAxis source z →
        G8CanonicalBoundaryWitness
  address_selected :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      (address z hOffAxis).nf =
        g8TauShadowSelectedNormalForm
          (g8ActualXiZetaThinCenteredShadow source z)
  address_realizable :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      BoundaryNFRealizable ((address z hOffAxis).nf)
  address_unitAxis :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      primePolarityAxisOffset ((address z hOffAxis).nf) = 1
  address_criticalImbalance :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      TauCriticalImbalance ((address z hOffAxis).nf)

/-- A strict target exposes its canonical boundary-address handoff. -/
def g8ActualXiZetaThinStrictPointGeometry_to_boundaryAddressHandoff
    {source : G8ActualXiZetaThinSourceContext}
    (target : G8ActualXiZetaThinStrictPointGeometryTarget source) :
    G8ActualXiZetaThinBoundaryAddressHandoff source where
  address := target.canonicalBoundaryAddress
  address_selected := target.address_selectedShadow
  address_realizable := by
    intro z hOffAxis
    exact
      (g8ActualXiZetaThinStrictPointGeometry_discipline
        target).addressRealizable z hOffAxis
  address_unitAxis := by
    intro z hOffAxis
    exact
      (g8ActualXiZetaThinStrictPointGeometry_discipline
        target).address_unitAxis z hOffAxis
  address_criticalImbalance := by
    intro z hOffAxis
    exact
      (g8ActualXiZetaThinStrictPointGeometry_discipline
        target).address_criticalImbalance z hOffAxis

/-- A boundary-address handoff records that the selected address lies on the
    off-axis tau class. -/
theorem g8ActualXiZetaThinBoundaryAddressHandoff_tauOffAxisClass
    {source : G8ActualXiZetaThinSourceContext}
    (handoff : G8ActualXiZetaThinBoundaryAddressHandoff source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    primePolarityAxisOffset (handoff.address z hOffAxis).nf = 1 :=
  handoff.address_unitAxis z hOffAxis

-- ============================================================
-- CANONICAL ACTUAL XI/ZETA DISCIPLINE
-- ============================================================

/-- The canonical actual source supplies a certified strict target. -/
def g8ActualXiZetaCanonical_to_thinCertifiedStrictPointGeometry
    (source : G8ActualXiZetaCanonicalPreimageSource) :
    G8ActualXiZetaThinCertifiedStrictPointGeometry
      (g8ActualXiZetaCanonical_to_thinSource source) where
  target := g8ActualXiZetaCanonical_to_thinStrictPointGeometry source
  discipline :=
    g8ActualXiZetaThinStrictPointGeometry_discipline
      (g8ActualXiZetaCanonical_to_thinStrictPointGeometry source)

/-- The canonical actual source supplies the actual-shadow to canonical
    boundary-address handoff. -/
def g8ActualXiZetaCanonical_to_thinBoundaryAddressHandoff
    (source : G8ActualXiZetaCanonicalPreimageSource) :
    G8ActualXiZetaThinBoundaryAddressHandoff
      (g8ActualXiZetaCanonical_to_thinSource source) :=
  g8ActualXiZetaThinStrictPointGeometry_to_boundaryAddressHandoff
    (g8ActualXiZetaCanonical_to_thinStrictPointGeometry source)

/-- Pointwise canonical selected normal form for the thin actual source. -/
theorem
    g8ActualXiZetaCanonical_thinWitnessNormalForm_eq_selected
    (source : G8ActualXiZetaCanonicalPreimageSource)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (g8ActualXiZetaCanonical_to_thinSource source) z) :
    (g8ActualXiZetaCanonical_to_thinSource source).tauNormalForm
        (g8ActualXiZetaCanonicalWitnessForThinOffAxis
          source z hOffAxis) =
      g8TauShadowSelectedNormalForm
        (g8ActualXiZetaThinCenteredShadow
          (g8ActualXiZetaCanonical_to_thinSource source) z) :=
  g8ActualXiZetaThinStrictPointGeometry_selectedNormalForm
    (g8ActualXiZetaCanonical_to_thinStrictPointGeometry source)
    z hOffAxis

/-- Pointwise canonical boundary address realizes the selected normal form
    for the thin actual source. -/
theorem
    g8ActualXiZetaCanonical_thinBoundaryAddress_eq_selected
    (source : G8ActualXiZetaCanonicalPreimageSource)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (g8ActualXiZetaCanonical_to_thinSource source) z) :
    (g8ActualXiZetaCanonicalBoundaryForThinOffAxis
        source z hOffAxis).nf =
      g8TauShadowSelectedNormalForm
        (g8ActualXiZetaThinCenteredShadow
          (g8ActualXiZetaCanonical_to_thinSource source) z) :=
  (g8ActualXiZetaCanonical_to_thinBoundaryAddressHandoff
    source).address_selected z hOffAxis

/-- The current concrete canonical selector sends every readable off-axis
    actual `xi` shadow to the off-axis sample boundary witness.

This theorem is deliberately diagnostic: it identifies exactly where the
present selected-normal-form model is still binary/sample-class, so later
point-specific geometry work knows the precise seam to refine. -/
theorem
    g8ActualXiZetaCanonical_thinBoundaryAddress_eq_offAxisSample
    (source : G8ActualXiZetaCanonicalPreimageSource)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (g8ActualXiZetaCanonical_to_thinSource source) z) :
    g8ActualXiZetaCanonicalBoundaryForThinOffAxis source z hOffAxis =
      g8TauSampleOffAxisCanonicalBoundaryWitness := by
  rfl

/-- The diagnostic sample-class fact is compatible with selected-normal-form
    equality for off-axis shadows. -/
theorem
    g8ActualXiZetaCanonical_offAxisSample_nf_eq_selected
    (source : G8ActualXiZetaCanonicalPreimageSource)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis :
      G8ActualXiZetaThinChartOffAxis
        (g8ActualXiZetaCanonical_to_thinSource source) z) :
    g8TauSampleOffAxisCanonicalBoundaryWitness.nf =
      g8TauShadowSelectedNormalForm
        (g8ActualXiZetaThinCenteredShadow
          (g8ActualXiZetaCanonical_to_thinSource source) z) := by
  rw [
    ← g8ActualXiZetaCanonical_thinBoundaryAddress_eq_selected
      source z hOffAxis,
    g8ActualXiZetaCanonical_thinBoundaryAddress_eq_offAxisSample
      source z hOffAxis
  ]

-- ============================================================
-- CERTIFIED TARGET TO CORRIDOR
-- ============================================================

/-- Certified strict point geometry supplies the actual no-ghost
    decomposition after explicit thickening. -/
def
    g8ActualXiZetaThinCertifiedStrictPointGeometry_to_noGhostDecomposition
    (source : G8ActualXiZetaThinSourceContext)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart)
    (cert : G8ActualXiZetaThinCertifiedStrictPointGeometry source) :
    G8ActualXiZetaNoGhostDecomposition
      (g8ActualXiZetaThin_to_fullSource
        source transfer chartAgreement) :=
  g8ActualXiZetaThinStrictPointGeometry_to_noGhostDecomposition
    source transfer chartAgreement cert.target

/-- Certified strict point geometry yields local one-sided pullback after
    explicit thickening. -/
theorem
    g8ActualXiZetaThinCertifiedStrictPointGeometry_yields_pullback
    (source : G8ActualXiZetaThinSourceContext)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart)
    (cert : G8ActualXiZetaThinCertifiedStrictPointGeometry source) :
    G8eOffCriticalPullback
      (g8ActualXiZeta_base
        (g8ActualXiZetaThin_to_fullSource
          source transfer chartAgreement)) :=
  g8ActualXiZetaThinStrictPointGeometry_yields_pullback
    source transfer chartAgreement cert.target

end Tau.BookIII.Bridge
