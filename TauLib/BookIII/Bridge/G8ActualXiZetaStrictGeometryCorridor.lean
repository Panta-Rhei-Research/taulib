import TauLib.BookIII.Bridge.G8ActualXiZetaStrictPointGeometry

/-!
# TauLib.BookIII.Bridge.G8ActualXiZetaStrictGeometryCorridor

Corridor adapters for the strict point-geometry target.

The thin strict target is the clean proof-facing layer: it records actual
off-axis `xi` shadows, point-specific tau witnesses, canonical boundary
addresses, normalized axis relation, and tau critical imbalance without
carrying the full G8d divisor-transfer package.  Existing corridor APIs still
consume the legacy actual-source context, so this module performs the explicit
thickening step only at that boundary.

No O3 theorem, analytic-completion uniqueness, full divisor transfer, tau
purity, or final localization theorem is proved here.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- THIN STRICT TARGET TO LEGACY ACTUAL CORRIDOR
-- ============================================================

/-- A thin strict point-geometry target supplies the legacy actual-source
    pointwise preimage contract after explicit thickening by a transfer
    context using the same chart. -/
theorem g8ActualXiZetaThinStrictPointGeometry_to_fullPointwise
    (source : G8ActualXiZetaThinSourceContext)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart)
    (target : G8ActualXiZetaThinStrictPointGeometryTarget source) :
    G8ActualXiZetaPointwiseTauImbalancePreimagesExist
      (g8ActualXiZetaThin_to_fullSource
        source transfer chartAgreement) :=
  g8ActualXiZetaThinPointwise_to_fullPointwise
    source transfer chartAgreement
    (g8ActualXiZetaThinStrictPointGeometry_to_pointwise target)

/-- The thickened thin source realizes tau critical imbalance as the local
    tau off-critical witness predicate. -/
theorem g8ActualXiZetaThin_to_fullTauWitnessRealization
    (source : G8ActualXiZetaThinSourceContext)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart) :
    G8OffAxisTauWitnessRealization
      (g8ActualXiZeta_chart
        (g8ActualXiZetaThin_to_fullSource
          source transfer chartAgreement)) := by
  intro _w hImbalance
  exact hImbalance

/-- A thin strict point-geometry target supplies the actual no-ghost
    decomposition once thickened at the legacy boundary. -/
def g8ActualXiZetaThinStrictPointGeometry_to_noGhostDecomposition
    (source : G8ActualXiZetaThinSourceContext)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart)
    (target : G8ActualXiZetaThinStrictPointGeometryTarget source) :
    G8ActualXiZetaNoGhostDecomposition
      (g8ActualXiZetaThin_to_fullSource
        source transfer chartAgreement) where
  pointwisePreimages :=
    g8ActualXiZetaThinStrictPointGeometry_to_fullPointwise
      source transfer chartAgreement target
  tauWitness :=
    g8ActualXiZetaThin_to_fullTauWitnessRealization
      source transfer chartAgreement

/-- A thin strict point-geometry target supplies the existing actual
    `xi`/`zeta` corridor after explicit thickening. -/
def g8ActualXiZetaThinStrictPointGeometry_to_corridor
    (source : G8ActualXiZetaThinSourceContext)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart)
    (target : G8ActualXiZetaThinStrictPointGeometryTarget source) :
    G8ActualXiZetaCorridor
      (g8ActualXiZetaThin_to_fullSource
        source transfer chartAgreement) :=
  g8ActualXiZetaNoGhostDecomposition_to_corridor
    (g8ActualXiZetaThinStrictPointGeometry_to_noGhostDecomposition
      source transfer chartAgreement target)

/-- A thin strict point-geometry target yields the local one-sided pullback
    after explicit thickening. -/
theorem g8ActualXiZetaThinStrictPointGeometry_yields_pullback
    (source : G8ActualXiZetaThinSourceContext)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart)
    (target : G8ActualXiZetaThinStrictPointGeometryTarget source) :
    G8eOffCriticalPullback
      (g8ActualXiZeta_base
        (g8ActualXiZetaThin_to_fullSource
          source transfer chartAgreement)) :=
  g8ActualXiZetaNoGhostDecomposition_yields_pullback
    (g8ActualXiZetaThin_to_fullSource
      source transfer chartAgreement)
    (g8ActualXiZetaThinStrictPointGeometry_to_noGhostDecomposition
      source transfer chartAgreement target)

/-- A thin strict point-geometry target plus tau-side purity yields local
    exclusion of off-critical actual `xi` zeros after explicit thickening. -/
theorem g8ActualXiZetaThinStrictPointGeometry_noOffCriticalXiZeros
    (source : G8ActualXiZetaThinSourceContext)
    (transfer : G8dZeroDivisorTransferContext)
    (chartAgreement : transfer.completion.chart = source.chart)
    (target : G8ActualXiZetaThinStrictPointGeometryTarget source)
    (tauPurity :
      G8eTauPurityExcludesOffCritical
        (g8ActualXiZeta_base
          (g8ActualXiZetaThin_to_fullSource
            source transfer chartAgreement))) :
    G8eNoOrthodoxOffCriticalZeros
      (g8ActualXiZeta_base
        (g8ActualXiZetaThin_to_fullSource
          source transfer chartAgreement)) :=
  g8ActualXiZetaNoGhostDecomposition_noOffCriticalXiZeros
    (g8ActualXiZetaThin_to_fullSource
      source transfer chartAgreement)
    (g8ActualXiZetaThinStrictPointGeometry_to_noGhostDecomposition
      source transfer chartAgreement target)
    tauPurity

-- ============================================================
-- CANONICAL STRICT TARGET HANDOFFS
-- ============================================================

/-- The canonical actual source also satisfies the older full strict
    point-geometry target. -/
def g8ActualXiZetaCanonical_to_fullStrictPointGeometryTarget
    (source : G8ActualXiZetaCanonicalPreimageSource) :
    G8ActualXiZetaStrictPointGeometryTarget
      (g8ActualXiZetaCanonical_to_actualSource source) where
  pointSpecificWitness := by
    intro z hOffAxis
    exact
      g8CanonicalTauWitnessForOffAxis
        (g8ActualXiZetaCanonical_to_canonicalSource source)
        z
        (g8ActualXiZetaCanonical_actualOffAxis_to_canonicalOffAxis
          source z hOffAxis)
  normalizedRelated := by
    intro z hOffAxis
    exact
      g8ActualXiZetaCanonical_selectedWitness_actualRelated
        source z hOffAxis
  criticalImbalance := by
    intro z hOffAxis
    exact
      g8ActualXiZetaCanonical_selectedWitness_tauCritical
        source z hOffAxis
  nonSampleGeometryDiscipline := True

/-- The canonical thin strict target supplies the no-ghost decomposition
    through the thin-to-legacy adapter. -/
def g8ActualXiZetaCanonical_thinStrict_to_noGhostDecomposition
    (source : G8ActualXiZetaCanonicalPreimageSource) :
    G8ActualXiZetaNoGhostDecomposition
      (g8ActualXiZetaThin_to_fullSource
        (g8ActualXiZetaCanonical_to_thinSource source)
        source.transfer
        rfl) :=
  g8ActualXiZetaThinStrictPointGeometry_to_noGhostDecomposition
    (g8ActualXiZetaCanonical_to_thinSource source)
    source.transfer
    rfl
    (g8ActualXiZetaCanonical_to_thinStrictPointGeometry source)

/-- The canonical thin strict target yields the local one-sided pullback
    through the thin-to-legacy adapter. -/
theorem g8ActualXiZetaCanonical_thinStrict_yields_pullback
    (source : G8ActualXiZetaCanonicalPreimageSource) :
    G8eOffCriticalPullback
      (g8ActualXiZeta_base
        (g8ActualXiZetaThin_to_fullSource
          (g8ActualXiZetaCanonical_to_thinSource source)
          source.transfer
          rfl)) :=
  g8ActualXiZetaThinStrictPointGeometry_yields_pullback
    (g8ActualXiZetaCanonical_to_thinSource source)
    source.transfer
    rfl
    (g8ActualXiZetaCanonical_to_thinStrictPointGeometry source)

/-- The canonical thin strict target plus tau-side purity yields local
    off-critical exclusion through the thin-to-legacy adapter. -/
theorem g8ActualXiZetaCanonical_thinStrict_noOffCriticalXiZeros
    (source : G8ActualXiZetaCanonicalPreimageSource)
    (tauPurity :
      G8eTauPurityExcludesOffCritical
        (g8ActualXiZeta_base
          (g8ActualXiZetaThin_to_fullSource
            (g8ActualXiZetaCanonical_to_thinSource source)
            source.transfer
            rfl))) :
    G8eNoOrthodoxOffCriticalZeros
      (g8ActualXiZeta_base
        (g8ActualXiZetaThin_to_fullSource
          (g8ActualXiZetaCanonical_to_thinSource source)
          source.transfer
          rfl)) :=
  g8ActualXiZetaThinStrictPointGeometry_noOffCriticalXiZeros
    (g8ActualXiZetaCanonical_to_thinSource source)
    source.transfer
    rfl
    (g8ActualXiZetaCanonical_to_thinStrictPointGeometry source)
    tauPurity

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- The strict point-geometry corridor remains finite-only at G8b. -/
theorem g8ActualXiZetaThinStrictPointGeometry_finiteOnly
    {source : G8ActualXiZetaThinSourceContext}
    {transfer : G8dZeroDivisorTransferContext}
    {chartAgreement : transfer.completion.chart = source.chart}
    (target : G8ActualXiZetaThinStrictPointGeometryTarget source) :
    finiteG8bContext.finiteOnly :=
  g8ActualXiZetaNoGhostDecomposition_finiteOnly
    (g8ActualXiZetaThinStrictPointGeometry_to_noGhostDecomposition
      source transfer chartAgreement target)

/-- The strict point-geometry corridor carries no `xi` divisor claim from
    finite stages. -/
theorem g8ActualXiZetaThinStrictPointGeometry_noXiDivisorClaim
    {source : G8ActualXiZetaThinSourceContext}
    {transfer : G8dZeroDivisorTransferContext}
    {chartAgreement : transfer.completion.chart = source.chart}
    (target : G8ActualXiZetaThinStrictPointGeometryTarget source) :
    finiteG8bContext.noXiDivisorClaim :=
  g8ActualXiZetaNoGhostDecomposition_noXiDivisorClaim
    (g8ActualXiZetaThinStrictPointGeometry_to_noGhostDecomposition
      source transfer chartAgreement target)

/-- The strict point-geometry corridor carries no analytic-completion claim
    from finite stages. -/
theorem g8ActualXiZetaThinStrictPointGeometry_noAnalyticCompletionClaim
    {source : G8ActualXiZetaThinSourceContext}
    {transfer : G8dZeroDivisorTransferContext}
    {chartAgreement : transfer.completion.chart = source.chart}
    (target : G8ActualXiZetaThinStrictPointGeometryTarget source) :
    finiteG8bContext.noAnalyticCompletionClaim :=
  g8ActualXiZetaNoGhostDecomposition_noAnalyticCompletionClaim
    (g8ActualXiZetaThinStrictPointGeometry_to_noGhostDecomposition
      source transfer chartAgreement target)

end Tau.BookIII.Bridge
