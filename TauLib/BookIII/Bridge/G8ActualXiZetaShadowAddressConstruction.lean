import TauLib.BookIII.Bridge.G8ActualXiZetaCanonicalBoundaryCarrier

/-!
# TauLib.BookIII.Bridge.G8ActualXiZetaShadowAddressConstruction

Explicit actual-`xi` centered-shadow address construction for the G8f
corridor.

The preceding address-map layer allowed an actual centered `xi` shadow to
induce a boundary address through the generic point-sensitive selector.  This
module makes the construction more direct:

```text
actual centered xi data
  -> centered axis class plus vertical discriminator
  -> finite boundary point address
  -> normalized canonical boundary witness
```

The localization-bearing coordinate remains the centered axis class.  The
vertical discriminator is only an address-resolution discriminator: it can
certify point sensitivity when two actual off-axis carriers separate in that
coordinate.  The module does not prove O3, analytic-completion uniqueness,
full divisor transfer, tau purity, classical RH, or any global zero-divisor
claim.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- EXPLICIT CENTERED-XI ADDRESS CONSTRUCTION
-- ============================================================

/-- The vertical centered receiving coordinate used only as a finite-address
    discriminator.

The actual localization signal is still the centered axis offset.  This
coordinate is intentionally coarse: it separates the real-axis shadow from the
non-real centered shadow without claiming to classify on-axis height or
multiplicity. -/
def orthodoxXiCarrierCenteredVerticalCoordinate
    (z : OrthodoxXiZeroCarrier) : ℝ :=
  z.toZero.point.im

/-- Binary address-resolution class extracted from actual centered `xi` data.

This is not the RH critical-axis predicate.  It is the point-sensitive address
discriminator used after the centered chart has already supplied the
localization-bearing axis coordinate. -/
def orthodoxXiCarrierCenteredAddressClass
    (z : OrthodoxXiZeroCarrier) : Nat :=
  if orthodoxXiCarrierCenteredVerticalCoordinate z = 0 then 0 else 1

/-- The centered address class is binary. -/
theorem orthodoxXiCarrierCenteredAddressClass_binary
    (z : OrthodoxXiZeroCarrier) :
    orthodoxXiCarrierCenteredAddressClass z = 0 ∨
      orthodoxXiCarrierCenteredAddressClass z = 1 := by
  unfold orthodoxXiCarrierCenteredAddressClass
  by_cases h : orthodoxXiCarrierCenteredVerticalCoordinate z = 0
  · simp [h]
  · simp [h]

/-- Explicit finite boundary address attached to actual centered `xi` data.

On-axis shadows use the protected on-axis address.  Off-axis shadows use a
point-sensitive off-axis address determined by the actual centered vertical
class.  Thus the formula depends on the real centered `xi` carrier, not on a
global off-axis sample. -/
def orthodoxXiCarrierCenteredBoundaryPointAddress
    (z : OrthodoxXiZeroCarrier) : G8BoundaryPointAddress :=
  if (orthodoxXiCarrierCenteredShadow z).axisOffset = 0 then
    { sourceValue := 0, stage := 3 }
  else if orthodoxXiCarrierCenteredAddressClass z = 0 then
    g8PointSensitiveOffAxisAddressA
  else
    g8PointSensitiveOffAxisAddressB

/-- On-axis actual centered data maps to the protected on-axis address. -/
theorem orthodoxXiCarrierCenteredBoundaryPointAddress_onAxis
    (z : OrthodoxXiZeroCarrier)
    (hAxis : OnCriticalAxis (orthodoxXiCarrierCenteredShadow z)) :
    orthodoxXiCarrierCenteredBoundaryPointAddress z =
      { sourceValue := 0, stage := 3 } := by
  unfold OnCriticalAxis at hAxis
  simp [orthodoxXiCarrierCenteredBoundaryPointAddress, hAxis]

/-- Off-axis actual centered data with vertical class `0` maps to the first
    theorem-backed off-axis address. -/
theorem orthodoxXiCarrierCenteredBoundaryPointAddress_offAxis_classZero
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : ShadowOffAxis (orthodoxXiCarrierCenteredShadow z))
    (hClass : orthodoxXiCarrierCenteredAddressClass z = 0) :
    orthodoxXiCarrierCenteredBoundaryPointAddress z =
      g8PointSensitiveOffAxisAddressA := by
  have hAxisNe :
      (orthodoxXiCarrierCenteredShadow z).axisOffset ≠ 0 := by
    simpa [ShadowOffAxis, OnCriticalAxis] using hOffAxis
  simp [
    orthodoxXiCarrierCenteredBoundaryPointAddress,
    hAxisNe,
    hClass
  ]

/-- Off-axis actual centered data with nonzero vertical class maps to the
    second theorem-backed off-axis address. -/
theorem orthodoxXiCarrierCenteredBoundaryPointAddress_offAxis_classNonzero
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : ShadowOffAxis (orthodoxXiCarrierCenteredShadow z))
    (hClass : orthodoxXiCarrierCenteredAddressClass z ≠ 0) :
    orthodoxXiCarrierCenteredBoundaryPointAddress z =
      g8PointSensitiveOffAxisAddressB := by
  have hAxisNe :
      (orthodoxXiCarrierCenteredShadow z).axisOffset ≠ 0 := by
    simpa [ShadowOffAxis, OnCriticalAxis] using hOffAxis
  simp [
    orthodoxXiCarrierCenteredBoundaryPointAddress,
    hAxisNe,
    hClass
  ]

/-- The explicit centered address has the correct normalized tau axis class. -/
theorem orthodoxXiCarrierCenteredBoundaryPointAddress_axisClass
    (z : OrthodoxXiZeroCarrier) :
    primePolarityAxisOffset
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf =
      normalizedAxisOffset (orthodoxXiCarrierCenteredShadow z) := by
  by_cases hAxis :
      (orthodoxXiCarrierCenteredShadow z).axisOffset = 0
  · have hNorm :
        normalizedAxisOffset (orthodoxXiCarrierCenteredShadow z) = 0 :=
      normalizedAxisOffset_eq_zero_of_onAxis hAxis
    have hPrime :
        primePolarityAxisOffset
            (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf =
          0 := by
      simpa [
        orthodoxXiCarrierCenteredBoundaryPointAddress,
        hAxis,
        G8BoundaryPointAddress.normalize,
        g8CanonicalBoundaryWitnessOfStage,
        g8TauSampleOnAxisBoundaryNF
      ] using
        (primePolarityAxisOffset_eq_zero_iff_bcBalanced
          g8TauSampleOnAxisBoundaryNF).mpr
          g8TauSampleOnAxisBoundaryNF_bcBalanced
    rw [hPrime, hNorm]
  · have hOffAxis :
        ShadowOffAxis (orthodoxXiCarrierCenteredShadow z) := by
      simpa [ShadowOffAxis, OnCriticalAxis] using hAxis
    have hNorm :
        normalizedAxisOffset (orthodoxXiCarrierCenteredShadow z) = 1 :=
      normalizedAxisOffset_eq_one_of_offAxis hOffAxis
    by_cases hClass : orthodoxXiCarrierCenteredAddressClass z = 0
    · have hPrime :
          primePolarityAxisOffset
              (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf =
            1 := by
        simpa [
          orthodoxXiCarrierCenteredBoundaryPointAddress,
          hAxis,
          hClass
        ] using g8PointSensitiveOffAxisAddressA_unitAxis
      rw [hPrime, hNorm]
    · have hPrime :
          primePolarityAxisOffset
              (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf =
            1 := by
        simpa [
          orthodoxXiCarrierCenteredBoundaryPointAddress,
          hAxis,
          hClass
        ] using g8PointSensitiveOffAxisAddressB_unitAxis
      rw [hPrime, hNorm]

/-- Off-axis actual centered data maps to a tau unit-axis boundary address. -/
theorem orthodoxXiCarrierCenteredBoundaryPointAddress_unitAxis
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : ShadowOffAxis (orthodoxXiCarrierCenteredShadow z)) :
    primePolarityAxisOffset
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf = 1 := by
  exact
    (orthodoxXiCarrierCenteredBoundaryPointAddress_axisClass z).trans
      (normalizedAxisOffset_eq_one_of_offAxis hOffAxis)

/-- Off-axis actual centered data maps to a B/C-imbalanced tau normal form. -/
theorem orthodoxXiCarrierCenteredBoundaryPointAddress_bcImbalance
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : ShadowOffAxis (orthodoxXiCarrierCenteredShadow z)) :
    TauBCImbalance
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf :=
  (primePolarityAxisOffset_eq_one_iff_bcImbalance
    (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf).mp
    (orthodoxXiCarrierCenteredBoundaryPointAddress_unitAxis z hOffAxis)

/-- Off-axis actual centered data maps to a tau critical-imbalance normal
    form. -/
theorem orthodoxXiCarrierCenteredBoundaryPointAddress_criticalImbalance
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : ShadowOffAxis (orthodoxXiCarrierCenteredShadow z)) :
    TauCriticalImbalance
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf :=
  (tauCriticalImbalance_iff_bcImbalance
    (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf).mpr
    (orthodoxXiCarrierCenteredBoundaryPointAddress_bcImbalance z hOffAxis)

-- ============================================================
-- EXPLICIT ACTUAL THIN ADDRESS MAP
-- ============================================================

/-- Explicit point-address map from actual centered `xi` data. -/
def g8ActualXiZetaThinExplicitBoundaryPointAddressMap
    (source : G8ActualXiZetaThinSourceContext) :
    G8ActualXiZetaThinBoundaryPointAddressMap source where
  addressOf := fun z _hOffAxis =>
    orthodoxXiCarrierCenteredBoundaryPointAddress z
  normalizedAxis_agrees := by
    intro z _hOffAxis
    exact orthodoxXiCarrierCenteredBoundaryPointAddress_axisClass z
  finiteStageGuardrails := True
  finiteStageGuardrails_proof := by
    trivial
  noXiDivisorClaim := True
  noXiDivisorClaim_proof := by
    trivial
  noAnalyticCompletionClaim := True
  noAnalyticCompletionClaim_proof := by
    trivial

/-- The explicit map selects exactly the centered boundary address. -/
theorem g8ActualXiZetaThinExplicitBoundaryPointAddressMap_addressOf
    (source : G8ActualXiZetaThinSourceContext)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    (g8ActualXiZetaThinExplicitBoundaryPointAddressMap source).addressOf
        z hOffAxis =
      orthodoxXiCarrierCenteredBoundaryPointAddress z :=
  rfl

/-- The explicit actual address map normalizes to tau unit axis on off-axis
    shadows. -/
theorem g8ActualXiZetaThinExplicitBoundaryPointAddressMap_unitAxis
    (source : G8ActualXiZetaThinSourceContext)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    primePolarityAxisOffset
        ((g8ActualXiZetaThinExplicitBoundaryPointAddressMap
          source).normalizedWitness z hOffAxis).nf = 1 :=
  g8ActualXiZetaThinBoundaryPointAddressMap_unitAxis
    (g8ActualXiZetaThinExplicitBoundaryPointAddressMap source)
    z hOffAxis

/-- The explicit actual address map normalizes to tau critical imbalance on
    off-axis shadows. -/
theorem g8ActualXiZetaThinExplicitBoundaryPointAddressMap_criticalImbalance
    (source : G8ActualXiZetaThinSourceContext)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    TauCriticalImbalance
      ((g8ActualXiZetaThinExplicitBoundaryPointAddressMap
        source).normalizedWitness z hOffAxis).nf :=
  g8ActualXiZetaThinBoundaryPointAddressMap_criticalImbalance
    (g8ActualXiZetaThinExplicitBoundaryPointAddressMap source)
    z hOffAxis

-- ============================================================
-- CANONICAL CARRIER ADAPTER
-- ============================================================

/-- Explicit actual-centered address map into the canonical boundary carrier. -/
def g8ActualXiZetaCanonicalBoundaryExplicitAddressMap
    (chart : ZetaAsCoordinateChartContext)
    (hG3 : chart.g3ZetaBridge)
    (hG4 : chart.g4AnalyticContinuation) :
    G8ActualXiZetaThinBoundaryPointAddressMap
      (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4) :=
  g8ActualXiZetaThinExplicitBoundaryPointAddressMap
    (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4)

/-- Explicit actual-centered address-resolved source into the canonical
    boundary carrier. -/
def g8ActualXiZetaCanonicalBoundaryExplicitResolvedSource
    (chart : ZetaAsCoordinateChartContext)
    (hG3 : chart.g3ZetaBridge)
    (hG4 : chart.g4AnalyticContinuation) :
    G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource
      (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4) :=
  g8ActualXiZetaCanonicalBoundaryAddressResolvedSource
    (g8ActualXiZetaCanonicalBoundaryExplicitAddressMap chart hG3 hG4)

/-- The explicit centered address construction supplies canonical-boundary
    pointwise tau imbalance preimages. -/
theorem g8ActualXiZetaCanonicalBoundaryExplicit_pointwisePreimages
    (chart : ZetaAsCoordinateChartContext)
    (hG3 : chart.g3ZetaBridge)
    (hG4 : chart.g4AnalyticContinuation) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist
      (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4) :=
  (g8ActualXiZetaCanonicalBoundaryExplicitResolvedSource
    chart hG3 hG4).to_pointwisePreimages

/-- The explicit centered address construction preserves finite-stage
    guardrails. -/
theorem g8ActualXiZetaCanonicalBoundaryExplicit_finiteStageGuardrails
    (chart : ZetaAsCoordinateChartContext)
    (hG3 : chart.g3ZetaBridge)
    (hG4 : chart.g4AnalyticContinuation) :
    (g8ActualXiZetaCanonicalBoundaryExplicitResolvedSource
      chart hG3 hG4).addrMap.finiteStageGuardrails :=
  (g8ActualXiZetaCanonicalBoundaryExplicitResolvedSource
    chart hG3 hG4).finiteStageGuardrails

/-- The explicit centered address construction makes no receiving-side
    `xi` divisor claim. -/
theorem g8ActualXiZetaCanonicalBoundaryExplicit_noXiDivisorClaim
    (chart : ZetaAsCoordinateChartContext)
    (hG3 : chart.g3ZetaBridge)
    (hG4 : chart.g4AnalyticContinuation) :
    (g8ActualXiZetaCanonicalBoundaryExplicitResolvedSource
      chart hG3 hG4).addrMap.noXiDivisorClaim :=
  (g8ActualXiZetaCanonicalBoundaryExplicitResolvedSource
    chart hG3 hG4).noXiDivisorClaim

/-- The explicit centered address construction makes no analytic-completion
    claim. -/
theorem g8ActualXiZetaCanonicalBoundaryExplicit_noAnalyticCompletionClaim
    (chart : ZetaAsCoordinateChartContext)
    (hG3 : chart.g3ZetaBridge)
    (hG4 : chart.g4AnalyticContinuation) :
    (g8ActualXiZetaCanonicalBoundaryExplicitResolvedSource
      chart hG3 hG4).addrMap.noAnalyticCompletionClaim :=
  (g8ActualXiZetaCanonicalBoundaryExplicitResolvedSource
    chart hG3 hG4).noAnalyticCompletionClaim

-- ============================================================
-- POINT-SENSITIVITY CERTIFICATE FOR THE ACTUAL MAP
-- ============================================================

/-- Certificate that the actual `xi` carrier supplies two off-axis points
    separated by the explicit centered address discriminator. -/
structure G8ActualXiZetaCenteredAddressSeparation
    (source : G8ActualXiZetaThinSourceContext) where
  zA : OrthodoxXiZeroCarrier
  zB : OrthodoxXiZeroCarrier
  offAxisA : G8ActualXiZetaThinChartOffAxis source zA
  offAxisB : G8ActualXiZetaThinChartOffAxis source zB
  classA_zero : orthodoxXiCarrierCenteredAddressClass zA = 0
  classB_nonzero : orthodoxXiCarrierCenteredAddressClass zB ≠ 0

/-- A centered-address separation certificate makes the explicit map
    point-sensitive. -/
theorem g8ActualXiZetaCenteredAddressSeparation_pointSensitive
    {source : G8ActualXiZetaThinSourceContext}
    (cert : G8ActualXiZetaCenteredAddressSeparation source) :
    G8ActualXiZetaThinBoundaryPointAddressMapPointSensitive
      (g8ActualXiZetaThinExplicitBoundaryPointAddressMap source) := by
  refine
    ⟨cert.zA, cert.zB, cert.offAxisA, cert.offAxisB, ?_⟩
  intro hEq
  have hA :
      (g8ActualXiZetaThinExplicitBoundaryPointAddressMap
          source).normalizedWitness cert.zA cert.offAxisA =
        g8PointSensitiveOffAxisAddressA.normalize := by
    simp [
      G8ActualXiZetaThinBoundaryPointAddressMap.normalizedWitness,
      g8ActualXiZetaThinExplicitBoundaryPointAddressMap,
      orthodoxXiCarrierCenteredBoundaryPointAddress_offAxis_classZero
        cert.zA cert.offAxisA cert.classA_zero
    ]
  have hB :
      (g8ActualXiZetaThinExplicitBoundaryPointAddressMap
          source).normalizedWitness cert.zB cert.offAxisB =
        g8PointSensitiveOffAxisAddressB.normalize := by
    simp [
      G8ActualXiZetaThinBoundaryPointAddressMap.normalizedWitness,
      g8ActualXiZetaThinExplicitBoundaryPointAddressMap,
      orthodoxXiCarrierCenteredBoundaryPointAddress_offAxis_classNonzero
        cert.zB cert.offAxisB cert.classB_nonzero
    ]
  exact
    g8PointSensitiveOffAxisAddressA_ne_B
      (hA.symm.trans (hEq.trans hB))

/-- A centered-address separation certificate refutes sample-class collapse
    for the explicit actual map. -/
theorem g8ActualXiZetaCenteredAddressSeparation_not_sampleClass
    {source : G8ActualXiZetaThinSourceContext}
    (cert : G8ActualXiZetaCenteredAddressSeparation source) :
    ¬ G8ActualXiZetaThinBoundaryPointAddressMapSampleClass
        (g8ActualXiZetaThinExplicitBoundaryPointAddressMap source) :=
  g8ActualXiZetaThinBoundaryPointAddressMap_pointSensitive_not_sampleClass
    (g8ActualXiZetaCenteredAddressSeparation_pointSensitive cert)

/-- Actual canonical-boundary explicit map is point-sensitive whenever the
    actual carrier supplies a centered-address separation certificate. -/
theorem g8ActualXiZetaCanonicalBoundaryExplicit_pointSensitive
    {chart : ZetaAsCoordinateChartContext}
    {hG3 : chart.g3ZetaBridge}
    {hG4 : chart.g4AnalyticContinuation}
    (cert :
      G8ActualXiZetaCenteredAddressSeparation
        (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4)) :
    G8ActualXiZetaThinBoundaryPointAddressMapPointSensitive
      (g8ActualXiZetaCanonicalBoundaryExplicitAddressMap
        chart hG3 hG4) :=
  g8ActualXiZetaCenteredAddressSeparation_pointSensitive cert

/-- Actual canonical-boundary explicit map is not sample-class whenever the
    actual carrier supplies a centered-address separation certificate. -/
theorem g8ActualXiZetaCanonicalBoundaryExplicit_not_sampleClass
    {chart : ZetaAsCoordinateChartContext}
    {hG3 : chart.g3ZetaBridge}
    {hG4 : chart.g4AnalyticContinuation}
    (cert :
      G8ActualXiZetaCenteredAddressSeparation
        (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4)) :
    ¬ G8ActualXiZetaThinBoundaryPointAddressMapSampleClass
        (g8ActualXiZetaCanonicalBoundaryExplicitAddressMap
          chart hG3 hG4) :=
  g8ActualXiZetaCenteredAddressSeparation_not_sampleClass cert

end Tau.BookIII.Bridge
