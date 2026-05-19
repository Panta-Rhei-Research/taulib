import TauLib.BookIII.Bridge.G8PointSensitiveBoundaryAddress

/-!
# TauLib.BookIII.Bridge.G8ActualXiZetaBoundaryAddressMap

Actual `xi` shadow to tau boundary point-address maps for the G8f corridor.

The strict-geometry layer already has a canonical-boundary-witness handoff,
but its current concrete source is deliberately diagnosed as off-axis
sample-class.  This module inserts the missing address layer:

```text
actual off-axis xi shadow
  -> finite boundary point address
  -> normalized canonical boundary witness
  -> tau B/C and critical imbalance
```

The map is local to the weak off-axis localization corridor.  It does not
prove O3, analytic-completion uniqueness, full divisor transfer, tau purity,
classical RH, or any global zero-divisor statement.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- ACTUAL XI/ZETA BOUNDARY POINT-ADDRESS MAP
-- ============================================================

/-- A point-address map for actual off-axis `xi` shadows.

The localization-bearing law is stated after address normalization: the tau
prime-polarity axis class of the normalized boundary witness agrees with the
binary centered-shadow axis class.  The remaining proposition fields are
explicit finite-stage guardrails; they are markers for this interface and do
not assert a receiving-side zero-divisor or analytic-completion theorem. -/
structure G8ActualXiZetaThinBoundaryPointAddressMap
    (source : G8ActualXiZetaThinSourceContext) where
  addressOf :
    ∀ (z : OrthodoxXiZeroCarrier),
      G8ActualXiZetaThinChartOffAxis source z →
        G8BoundaryPointAddress
  normalizedAxis_agrees :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      primePolarityAxisOffset ((addressOf z hOffAxis).normalize.nf) =
        normalizedAxisOffset (g8ActualXiZetaThinCenteredShadow source z)
  finiteStageGuardrails : Prop
  finiteStageGuardrails_proof : finiteStageGuardrails
  noXiDivisorClaim : Prop
  noXiDivisorClaim_proof : noXiDivisorClaim
  noAnalyticCompletionClaim : Prop
  noAnalyticCompletionClaim_proof : noAnalyticCompletionClaim

/-- The normalized canonical boundary witness selected by a point-address
    map. -/
def G8ActualXiZetaThinBoundaryPointAddressMap.normalizedWitness
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    G8CanonicalBoundaryWitness :=
  (addrMap.addressOf z hOffAxis).normalize

/-- Address-map normalization records the finite source value of the selected
    point address. -/
theorem
    g8ActualXiZetaThinBoundaryPointAddressMap_sourceValue
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    (addrMap.normalizedWitness z hOffAxis).sourceValue =
      (addrMap.addressOf z hOffAxis).sourceValue :=
  g8BoundaryPointAddress_normalize_sourceValue
    (addrMap.addressOf z hOffAxis)

/-- Address-map normalization records the finite stage of the selected point
    address. -/
theorem
    g8ActualXiZetaThinBoundaryPointAddressMap_stage
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    (addrMap.normalizedWitness z hOffAxis).stage =
      (addrMap.addressOf z hOffAxis).stage :=
  g8BoundaryPointAddress_normalize_stage
    (addrMap.addressOf z hOffAxis)

/-- Point-address-map outputs are finite-stage realizable after
    normalization. -/
theorem
    g8ActualXiZetaThinBoundaryPointAddressMap_realizable
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    BoundaryNFRealizable
      ((addrMap.normalizedWitness z hOffAxis).nf) :=
  g8BoundaryPointAddress_normalize_realizable
    (addrMap.addressOf z hOffAxis)

/-- Off-axis actual shadows normalize to tau unit axis class. -/
theorem
    g8ActualXiZetaThinBoundaryPointAddressMap_unitAxis
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    primePolarityAxisOffset
        ((addrMap.normalizedWitness z hOffAxis).nf) = 1 := by
  simpa [
    G8ActualXiZetaThinBoundaryPointAddressMap.normalizedWitness
  ] using
    (addrMap.normalizedAxis_agrees z hOffAxis).trans
      (normalizedAxisOffset_eq_one_of_offAxis hOffAxis)

/-- Off-axis actual shadows normalize to tau B/C imbalance. -/
theorem
    g8ActualXiZetaThinBoundaryPointAddressMap_bcImbalance
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    TauBCImbalance
      ((addrMap.normalizedWitness z hOffAxis).nf) :=
  (primePolarityAxisOffset_eq_one_iff_bcImbalance
    ((addrMap.normalizedWitness z hOffAxis).nf)).mp
    (g8ActualXiZetaThinBoundaryPointAddressMap_unitAxis
      addrMap z hOffAxis)

/-- Off-axis actual shadows normalize to tau critical imbalance. -/
theorem
    g8ActualXiZetaThinBoundaryPointAddressMap_criticalImbalance
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    TauCriticalImbalance
      ((addrMap.normalizedWitness z hOffAxis).nf) :=
  (tauCriticalImbalance_iff_bcImbalance
    ((addrMap.normalizedWitness z hOffAxis).nf)).mpr
    (g8ActualXiZetaThinBoundaryPointAddressMap_bcImbalance
      addrMap z hOffAxis)

/-- Finite-stage guardrails remain visible at the point-address layer. -/
theorem
    g8ActualXiZetaThinBoundaryPointAddressMap_finiteStageGuardrails
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source) :
    addrMap.finiteStageGuardrails :=
  addrMap.finiteStageGuardrails_proof

/-- The point-address layer does not by itself assert a receiving-side
    `xi` divisor claim. -/
theorem
    g8ActualXiZetaThinBoundaryPointAddressMap_noXiDivisorClaim
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source) :
    addrMap.noXiDivisorClaim :=
  addrMap.noXiDivisorClaim_proof

/-- The point-address layer does not by itself assert an analytic-completion
    claim. -/
theorem
    g8ActualXiZetaThinBoundaryPointAddressMap_noAnalyticCompletionClaim
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source) :
    addrMap.noAnalyticCompletionClaim :=
  addrMap.noAnalyticCompletionClaim_proof

-- ============================================================
-- ADAPTERS TO EXISTING CORRIDORS
-- ============================================================

/-- Compatibility with the older selected-normal-form corridor.

This is intentionally separate from the point-address map.  A genuinely
point-sensitive map should not be forced to prove this unless the downstream
binary selected-NF handoff is the desired target. -/
def G8ActualXiZetaThinBoundaryPointAddressMapSelectedNFCompatible
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source) :
    Prop :=
  ∀ (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
    (addrMap.normalizedWitness z hOffAxis).nf =
      g8TauShadowSelectedNormalForm
        (g8ActualXiZetaThinCenteredShadow source z)

/-- A selected-NF-compatible point-address map feeds the existing canonical
    boundary-address handoff. -/
def
    G8ActualXiZetaThinBoundaryPointAddressMap.to_boundaryAddressHandoff
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source)
    (hSelected :
      G8ActualXiZetaThinBoundaryPointAddressMapSelectedNFCompatible
        addrMap) :
    G8ActualXiZetaThinBoundaryAddressHandoff source where
  address := addrMap.normalizedWitness
  address_selected := hSelected
  address_realizable :=
    g8ActualXiZetaThinBoundaryPointAddressMap_realizable addrMap
  address_unitAxis :=
    g8ActualXiZetaThinBoundaryPointAddressMap_unitAxis addrMap
  address_criticalImbalance :=
    g8ActualXiZetaThinBoundaryPointAddressMap_criticalImbalance addrMap

/-- Witness-carrier compatibility needed to feed strict point geometry. -/
structure G8ActualXiZetaThinBoundaryPointAddressWitnessAdapter
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source) where
  pointSpecificWitness :
    ∀ z : OrthodoxXiZeroCarrier,
      G8ActualXiZetaThinChartOffAxis source z →
        source.tauWitness
  witness_normalForm_eq_normalizedAddress :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      source.tauNormalForm (pointSpecificWitness z hOffAxis) =
        (addrMap.normalizedWitness z hOffAxis).nf

/-- A selected-NF-compatible point-address map with a compatible tau-witness
    carrier feeds the strict point-geometry target. -/
def
    G8ActualXiZetaThinBoundaryPointAddressMap.to_strictPointGeometry
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source)
    (hSelected :
      G8ActualXiZetaThinBoundaryPointAddressMapSelectedNFCompatible
        addrMap)
    (witness :
      G8ActualXiZetaThinBoundaryPointAddressWitnessAdapter addrMap) :
    G8ActualXiZetaThinStrictPointGeometryTarget source where
  pointSpecificWitness := witness.pointSpecificWitness
  canonicalBoundaryAddress := addrMap.normalizedWitness
  witness_normalForm_eq_address :=
    witness.witness_normalForm_eq_normalizedAddress
  address_selectedShadow := hSelected
  normalizedRelated := by
    intro z hOffAxis
    unfold G8ActualXiZetaThinNormalizedAxisRelated
    rw [witness.witness_normalForm_eq_normalizedAddress z hOffAxis]
    exact (addrMap.normalizedAxis_agrees z hOffAxis).symm
  criticalImbalance := by
    intro z hOffAxis
    rw [witness.witness_normalForm_eq_normalizedAddress z hOffAxis]
    exact
      g8ActualXiZetaThinBoundaryPointAddressMap_criticalImbalance
        addrMap z hOffAxis
  nonSampleGeometryDiscipline := True

-- ============================================================
-- SHADOW-INDUCED POINT-ADDRESS MAP
-- ============================================================

/-- The current shadow-induced point-address map for an actual thin source.

It uses the existing point-sensitive boundary-address selector at the
`CriticalAxisShadow` level.  This produces an address map immediately, but
point sensitivity over the actual `xi` carrier remains a separate obligation:
the carrier must supply two distinct actual off-axis shadows before that
stronger theorem can be asserted. -/
def g8ActualXiZetaThinShadowInducedBoundaryPointAddressMap
    (source : G8ActualXiZetaThinSourceContext) :
    G8ActualXiZetaThinBoundaryPointAddressMap source where
  addressOf :=
    fun z _hOffAxis =>
      g8PointSensitiveBoundaryAddressOf
        (g8ActualXiZetaThinCenteredShadow source z)
  normalizedAxis_agrees := by
    intro z _hOffAxis
    exact
      g8PointSensitiveBoundaryAddressOf_axisClass
        (g8ActualXiZetaThinCenteredShadow source z)
  finiteStageGuardrails := True
  finiteStageGuardrails_proof := by
    trivial
  noXiDivisorClaim := True
  noXiDivisorClaim_proof := by
    trivial
  noAnalyticCompletionClaim := True
  noAnalyticCompletionClaim_proof := by
    trivial

/-- The shadow-induced map discharges its finite-stage guardrail marker. -/
theorem
    g8ActualXiZetaThinShadowInducedBoundaryPointAddressMap_finiteStageGuardrails
    (source : G8ActualXiZetaThinSourceContext) :
    (g8ActualXiZetaThinShadowInducedBoundaryPointAddressMap
      source).finiteStageGuardrails := by
  trivial

/-- The shadow-induced map does not assert a receiving-side `xi` divisor
    claim. -/
theorem
    g8ActualXiZetaThinShadowInducedBoundaryPointAddressMap_noXiDivisorClaim
    (source : G8ActualXiZetaThinSourceContext) :
    (g8ActualXiZetaThinShadowInducedBoundaryPointAddressMap
      source).noXiDivisorClaim := by
  trivial

/-- The shadow-induced map does not assert analytic-completion uniqueness or
    existence. -/
theorem
    g8ActualXiZetaThinShadowInducedBoundaryPointAddressMap_noAnalyticCompletionClaim
    (source : G8ActualXiZetaThinSourceContext) :
    (g8ActualXiZetaThinShadowInducedBoundaryPointAddressMap
      source).noAnalyticCompletionClaim := by
  trivial

-- ============================================================
-- SAMPLE-CLASS AND POINT-SENSITIVITY DIAGNOSTICS
-- ============================================================

/-- An actual point-address map is sample-class when every actual off-axis
    shadow normalizes to the current off-axis sample boundary witness. -/
def G8ActualXiZetaThinBoundaryPointAddressMapSampleClass
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source) :
    Prop :=
  ∀ (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
    addrMap.normalizedWitness z hOffAxis =
      g8TauSampleOffAxisCanonicalBoundaryWitness

/-- An actual point-address map is point-sensitive when two actual off-axis
    shadows normalize to distinct canonical boundary witnesses. -/
def G8ActualXiZetaThinBoundaryPointAddressMapPointSensitive
    {source : G8ActualXiZetaThinSourceContext}
    (addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source) :
    Prop :=
  ∃ (z q : OrthodoxXiZeroCarrier)
    (hZ : G8ActualXiZetaThinChartOffAxis source z)
    (hQ : G8ActualXiZetaThinChartOffAxis source q),
    addrMap.normalizedWitness z hZ ≠
      addrMap.normalizedWitness q hQ

/-- A certified point-sensitive actual address map cannot be sample-class. -/
theorem
    g8ActualXiZetaThinBoundaryPointAddressMap_pointSensitive_not_sampleClass
    {source : G8ActualXiZetaThinSourceContext}
    {addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source}
    (hPoint :
      G8ActualXiZetaThinBoundaryPointAddressMapPointSensitive addrMap) :
    ¬ G8ActualXiZetaThinBoundaryPointAddressMapSampleClass addrMap := by
  intro hSample
  rcases hPoint with ⟨z, q, hZ, hQ, hNe⟩
  have hZsample := hSample z hZ
  have hQsample := hSample q hQ
  exact hNe (hZsample.trans hQsample.symm)

/-- Certified point-sensitive actual address map. -/
structure G8ActualXiZetaThinPointSensitiveBoundaryPointAddressMap
    (source : G8ActualXiZetaThinSourceContext) where
  addrMap : G8ActualXiZetaThinBoundaryPointAddressMap source
  pointSensitive :
    G8ActualXiZetaThinBoundaryPointAddressMapPointSensitive addrMap

/-- A certified point-sensitive actual address map refutes sample-class
    collapse. -/
theorem
    g8ActualXiZetaThinPointSensitiveBoundaryPointAddressMap_not_sampleClass
    {source : G8ActualXiZetaThinSourceContext}
    (cert :
      G8ActualXiZetaThinPointSensitiveBoundaryPointAddressMap source) :
    ¬ G8ActualXiZetaThinBoundaryPointAddressMapSampleClass cert.addrMap :=
  g8ActualXiZetaThinBoundaryPointAddressMap_pointSensitive_not_sampleClass
    cert.pointSensitive

end Tau.BookIII.Bridge
