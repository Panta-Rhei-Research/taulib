import TauLib.BookIII.Bridge.G8ActualXiZetaShadowAddressConstruction

/-!
# TauLib.BookIII.Bridge.G8ActualXiZetaShadowAddressCorrectness

Correctness interface for the actual-`xi` centered-shadow boundary address.

The preceding module constructed an explicit finite boundary address from the
actual centered `xi` carrier.  This module packages the next proof-facing
claim: an accepted actual-shadow address readout is correct when it agrees
with that explicit centered construction and therefore inherits the
localization-bearing axis law.

This is still a local G8f chart-theory object.  It does not prove O3,
analytic-completion uniqueness, full divisor transfer, tau purity, classical
RH, or any global zero-divisor theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- ADDRESS CORRECTNESS INTERFACE
-- ============================================================

/-- Correctness package for the actual centered `xi` shadow address.

The field `addressOf` is the accepted finite boundary-address readout for an
actual off-axis carrier.  Correctness means this accepted readout agrees
pointwise with the explicit centered construction from
`G8ActualXiZetaShadowAddressConstruction`. -/
structure G8ActualXiZetaShadowAddressCorrectness
    (source : G8ActualXiZetaThinSourceContext) where
  addressOf :
    ∀ (z : OrthodoxXiZeroCarrier),
      G8ActualXiZetaThinChartOffAxis source z →
        G8BoundaryPointAddress
  address_correct :
    ∀ (z : OrthodoxXiZeroCarrier)
      (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
      addressOf z hOffAxis =
        orthodoxXiCarrierCenteredBoundaryPointAddress z
  finiteStageGuardrails : Prop
  finiteStageGuardrails_proof : finiteStageGuardrails
  noXiDivisorClaim : Prop
  noXiDivisorClaim_proof : noXiDivisorClaim
  noAnalyticCompletionClaim : Prop
  noAnalyticCompletionClaim_proof : noAnalyticCompletionClaim

/-- The canonical correctness object for the explicit centered address. -/
def g8ActualXiZetaExplicitShadowAddressCorrectness
    (source : G8ActualXiZetaThinSourceContext) :
    G8ActualXiZetaShadowAddressCorrectness source where
  addressOf := fun z _hOffAxis =>
    orthodoxXiCarrierCenteredBoundaryPointAddress z
  address_correct := by
    intro _z _hOffAxis
    rfl
  finiteStageGuardrails := True
  finiteStageGuardrails_proof := by
    trivial
  noXiDivisorClaim := True
  noXiDivisorClaim_proof := by
    trivial
  noAnalyticCompletionClaim := True
  noAnalyticCompletionClaim_proof := by
    trivial

/-- A correct accepted address readout has the same normalized tau axis class
    as the centered actual `xi` shadow. -/
theorem G8ActualXiZetaShadowAddressCorrectness.axisClass
    {source : G8ActualXiZetaThinSourceContext}
    (correct : G8ActualXiZetaShadowAddressCorrectness source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    primePolarityAxisOffset
        ((correct.addressOf z hOffAxis).normalize.nf) =
      normalizedAxisOffset (g8ActualXiZetaThinCenteredShadow source z) := by
  rw [correct.address_correct z hOffAxis]
  exact orthodoxXiCarrierCenteredBoundaryPointAddress_axisClass z

/-- A correct accepted address readout sends off-axis actual shadows to unit
    tau axis class. -/
theorem G8ActualXiZetaShadowAddressCorrectness.unitAxis
    {source : G8ActualXiZetaThinSourceContext}
    (correct : G8ActualXiZetaShadowAddressCorrectness source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    primePolarityAxisOffset
        ((correct.addressOf z hOffAxis).normalize.nf) = 1 := by
  exact
    (correct.axisClass z hOffAxis).trans
      (normalizedAxisOffset_eq_one_of_offAxis hOffAxis)

/-- A correct accepted address readout sends off-axis actual shadows to a
    tau B/C-imbalanced normal form. -/
theorem G8ActualXiZetaShadowAddressCorrectness.bcImbalance
    {source : G8ActualXiZetaThinSourceContext}
    (correct : G8ActualXiZetaShadowAddressCorrectness source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    TauBCImbalance ((correct.addressOf z hOffAxis).normalize.nf) :=
  (primePolarityAxisOffset_eq_one_iff_bcImbalance
    ((correct.addressOf z hOffAxis).normalize.nf)).mp
    (correct.unitAxis z hOffAxis)

/-- A correct accepted address readout sends off-axis actual shadows to a
    tau critical-imbalance normal form. -/
theorem G8ActualXiZetaShadowAddressCorrectness.criticalImbalance
    {source : G8ActualXiZetaThinSourceContext}
    (correct : G8ActualXiZetaShadowAddressCorrectness source)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    TauCriticalImbalance ((correct.addressOf z hOffAxis).normalize.nf) :=
  (tauCriticalImbalance_iff_bcImbalance
    ((correct.addressOf z hOffAxis).normalize.nf)).mpr
    (correct.bcImbalance z hOffAxis)

/-- Correctness packages expose their finite-stage guardrail. -/
theorem G8ActualXiZetaShadowAddressCorrectness.finiteStageGuardrails_holds
    {source : G8ActualXiZetaThinSourceContext}
    (correct : G8ActualXiZetaShadowAddressCorrectness source) :
    correct.finiteStageGuardrails :=
  correct.finiteStageGuardrails_proof

/-- Correctness packages do not assert a receiving-side `xi` divisor claim. -/
theorem G8ActualXiZetaShadowAddressCorrectness.noXiDivisorClaim_holds
    {source : G8ActualXiZetaThinSourceContext}
    (correct : G8ActualXiZetaShadowAddressCorrectness source) :
    correct.noXiDivisorClaim :=
  correct.noXiDivisorClaim_proof

/-- Correctness packages do not assert analytic-completion uniqueness or
    existence. -/
theorem G8ActualXiZetaShadowAddressCorrectness.noAnalyticCompletionClaim_holds
    {source : G8ActualXiZetaThinSourceContext}
    (correct : G8ActualXiZetaShadowAddressCorrectness source) :
    correct.noAnalyticCompletionClaim :=
  correct.noAnalyticCompletionClaim_proof

-- ============================================================
-- ADAPTERS BACK INTO THE ADDRESS CORRIDOR
-- ============================================================

/-- A correct accepted address readout is an actual boundary point-address
    map. -/
def G8ActualXiZetaShadowAddressCorrectness.toAddressMap
    {source : G8ActualXiZetaThinSourceContext}
    (correct : G8ActualXiZetaShadowAddressCorrectness source) :
    G8ActualXiZetaThinBoundaryPointAddressMap source where
  addressOf := correct.addressOf
  normalizedAxis_agrees := by
    intro z hOffAxis
    exact correct.axisClass z hOffAxis
  finiteStageGuardrails := correct.finiteStageGuardrails
  finiteStageGuardrails_proof := correct.finiteStageGuardrails_proof
  noXiDivisorClaim := correct.noXiDivisorClaim
  noXiDivisorClaim_proof := correct.noXiDivisorClaim_proof
  noAnalyticCompletionClaim := correct.noAnalyticCompletionClaim
  noAnalyticCompletionClaim_proof :=
    correct.noAnalyticCompletionClaim_proof

/-- The explicit correctness object recovers the explicit address map. -/
theorem g8ActualXiZetaExplicitShadowAddressCorrectness_addressOf
    (source : G8ActualXiZetaThinSourceContext)
    (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z) :
    (g8ActualXiZetaExplicitShadowAddressCorrectness
      source).toAddressMap.addressOf z hOffAxis =
      (g8ActualXiZetaThinExplicitBoundaryPointAddressMap
        source).addressOf z hOffAxis :=
  rfl

/-- A correct accepted address readout plus a compatible witness adapter
    supplies pointwise tau imbalance preimages. -/
theorem G8ActualXiZetaShadowAddressCorrectness.to_pointwisePreimages
    {source : G8ActualXiZetaThinSourceContext}
    (correct : G8ActualXiZetaShadowAddressCorrectness source)
    (witness :
      G8ActualXiZetaThinBoundaryPointAddressWitnessAdapter
        correct.toAddressMap) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist source :=
  correct.toAddressMap.to_pointwisePreimages witness

/-- In the canonical boundary carrier, a correct accepted address readout is
    address-resolved by the identity carrier adapter. -/
def g8ActualXiZetaCanonicalBoundaryCorrectAddressResolvedSource
    {chart : ZetaAsCoordinateChartContext}
    {hG3 : chart.g3ZetaBridge}
    {hG4 : chart.g4AnalyticContinuation}
    (correct :
      G8ActualXiZetaShadowAddressCorrectness
        (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4)) :
    G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource
      (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4) :=
  g8ActualXiZetaCanonicalBoundaryAddressResolvedSource
    correct.toAddressMap

/-- In the canonical boundary carrier, a correct accepted address readout
    supplies pointwise tau imbalance preimages. -/
theorem g8ActualXiZetaCanonicalBoundaryCorrectAddress_pointwisePreimages
    {chart : ZetaAsCoordinateChartContext}
    {hG3 : chart.g3ZetaBridge}
    {hG4 : chart.g4AnalyticContinuation}
    (correct :
      G8ActualXiZetaShadowAddressCorrectness
        (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4)) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist
      (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4) :=
  (g8ActualXiZetaCanonicalBoundaryCorrectAddressResolvedSource
    correct).to_pointwisePreimages

/-- The canonical explicit address correctness supplies pointwise tau
    imbalance preimages. -/
theorem g8ActualXiZetaCanonicalBoundaryExplicitCorrectAddress_pointwisePreimages
    (chart : ZetaAsCoordinateChartContext)
    (hG3 : chart.g3ZetaBridge)
    (hG4 : chart.g4AnalyticContinuation) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist
      (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4) :=
  g8ActualXiZetaCanonicalBoundaryCorrectAddress_pointwisePreimages
    (g8ActualXiZetaExplicitShadowAddressCorrectness
      (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4))

-- ============================================================
-- MISMATCH AND SAMPLE-COLLAPSE FALSIFIERS
-- ============================================================

/-- A proposed accepted address that disagrees with the centered construction
    at one off-axis point. -/
structure G8ActualXiZetaShadowAddressMismatchWitness
    (source : G8ActualXiZetaThinSourceContext)
    (correct : G8ActualXiZetaShadowAddressCorrectness source) where
  z : OrthodoxXiZeroCarrier
  offAxis : G8ActualXiZetaThinChartOffAxis source z
  proposed : G8BoundaryPointAddress
  proposed_eq : correct.addressOf z offAxis = proposed
  mismatch :
    proposed ≠ orthodoxXiCarrierCenteredBoundaryPointAddress z

/-- A centered-address mismatch refutes address correctness. -/
theorem G8ActualXiZetaShadowAddressMismatchWitness.refutes
    {source : G8ActualXiZetaThinSourceContext}
    {correct : G8ActualXiZetaShadowAddressCorrectness source}
    (w : G8ActualXiZetaShadowAddressMismatchWitness source correct) :
    False :=
  w.mismatch ((w.proposed_eq).symm.trans
    (correct.address_correct w.z w.offAxis))

/-- A correct accepted address readout is sample-class when every actual
    off-axis point normalizes to the old off-axis sample witness. -/
def G8ActualXiZetaShadowAddressCorrectnessSampleClass
    {source : G8ActualXiZetaThinSourceContext}
    (correct : G8ActualXiZetaShadowAddressCorrectness source) : Prop :=
  ∀ (z : OrthodoxXiZeroCarrier)
    (hOffAxis : G8ActualXiZetaThinChartOffAxis source z),
    (correct.addressOf z hOffAxis).normalize =
      g8TauSampleOffAxisCanonicalBoundaryWitness

/-- A correct accepted address readout is point-sensitive when two actual
    off-axis points normalize to distinct canonical boundary witnesses. -/
def G8ActualXiZetaShadowAddressCorrectnessPointSensitive
    {source : G8ActualXiZetaThinSourceContext}
    (correct : G8ActualXiZetaShadowAddressCorrectness source) : Prop :=
  ∃ (z q : OrthodoxXiZeroCarrier)
    (hZ : G8ActualXiZetaThinChartOffAxis source z)
    (hQ : G8ActualXiZetaThinChartOffAxis source q),
    (correct.addressOf z hZ).normalize ≠
      (correct.addressOf q hQ).normalize

/-- Point-sensitive correct address readouts are not sample-class. -/
theorem G8ActualXiZetaShadowAddressCorrectness.pointSensitive_not_sampleClass
    {source : G8ActualXiZetaThinSourceContext}
    {correct : G8ActualXiZetaShadowAddressCorrectness source}
    (hPoint :
      G8ActualXiZetaShadowAddressCorrectnessPointSensitive correct) :
    ¬ G8ActualXiZetaShadowAddressCorrectnessSampleClass correct := by
  intro hSample
  rcases hPoint with ⟨z, q, hZ, hQ, hNe⟩
  exact hNe ((hSample z hZ).trans (hSample q hQ).symm)

/-- A centered-address separation certificate makes any correct accepted
    address readout point-sensitive. -/
theorem G8ActualXiZetaShadowAddressCorrectness.pointSensitive_of_separation
    {source : G8ActualXiZetaThinSourceContext}
    (correct : G8ActualXiZetaShadowAddressCorrectness source)
    (cert : G8ActualXiZetaCenteredAddressSeparation source) :
    G8ActualXiZetaShadowAddressCorrectnessPointSensitive correct := by
  refine
    ⟨cert.zA, cert.zB, cert.offAxisA, cert.offAxisB, ?_⟩
  intro hEq
  have hA :
      (correct.addressOf cert.zA cert.offAxisA).normalize =
        g8PointSensitiveOffAxisAddressA.normalize := by
    rw [correct.address_correct cert.zA cert.offAxisA]
    simp [
      orthodoxXiCarrierCenteredBoundaryPointAddress_offAxis_classZero
        cert.zA cert.offAxisA cert.classA_zero
    ]
  have hB :
      (correct.addressOf cert.zB cert.offAxisB).normalize =
        g8PointSensitiveOffAxisAddressB.normalize := by
    rw [correct.address_correct cert.zB cert.offAxisB]
    simp [
      orthodoxXiCarrierCenteredBoundaryPointAddress_offAxis_classNonzero
        cert.zB cert.offAxisB cert.classB_nonzero
    ]
  exact
    g8PointSensitiveOffAxisAddressA_ne_B
      (hA.symm.trans (hEq.trans hB))

/-- A centered-address separation certificate refutes sample-class collapse
    for any correct accepted address readout. -/
theorem G8ActualXiZetaShadowAddressCorrectness.not_sampleClass_of_separation
    {source : G8ActualXiZetaThinSourceContext}
    (correct : G8ActualXiZetaShadowAddressCorrectness source)
    (cert : G8ActualXiZetaCenteredAddressSeparation source) :
    ¬ G8ActualXiZetaShadowAddressCorrectnessSampleClass correct :=
  correct.pointSensitive_not_sampleClass
    (correct.pointSensitive_of_separation cert)

-- ============================================================
-- POINTWISE GHOST ALIGNMENT
-- ============================================================

/-- Thin pointwise ghost against a correct accepted address readout.

The fatal case is now point-specific: an actual off-axis shadow is readable,
but the correct address-normalized canonical witness is not accepted as a
related tau critical-imbalance preimage. -/
structure G8ActualXiZetaCorrectAddressGhostWitness
    (source : G8ActualXiZetaThinSourceContext)
    (correct : G8ActualXiZetaShadowAddressCorrectness source)
    (witness :
      G8ActualXiZetaThinBoundaryPointAddressWitnessAdapter
        correct.toAddressMap) where
  z : OrthodoxXiZeroCarrier
  offAxis : G8ActualXiZetaThinChartOffAxis source z
  noCorrectAddressPreimage :
    ¬ G8ActualXiZetaThinRelatedTauCriticalPreimage
        source z (witness.pointSpecificWitness z offAxis)

/-- Correctness plus the witness adapter refutes the pointwise correct-address
    ghost. -/
theorem G8ActualXiZetaCorrectAddressGhostWitness.refutes
    {source : G8ActualXiZetaThinSourceContext}
    {correct : G8ActualXiZetaShadowAddressCorrectness source}
    {witness :
      G8ActualXiZetaThinBoundaryPointAddressWitnessAdapter
        correct.toAddressMap}
    (ghost :
      G8ActualXiZetaCorrectAddressGhostWitness
        source correct witness) :
    False := by
  have hPre :
      G8ActualXiZetaThinRelatedTauCriticalPreimage
        source ghost.z
        (witness.pointSpecificWitness ghost.z ghost.offAxis) := by
    constructor
    · unfold G8ActualXiZetaThinNormalizedAxisRelated
      rw [
        witness.witness_normalForm_eq_normalizedAddress
          ghost.z ghost.offAxis
      ]
      exact
        (correct.toAddressMap.normalizedAxis_agrees
          ghost.z ghost.offAxis).symm
    · rw [
        witness.witness_normalForm_eq_normalizedAddress
          ghost.z ghost.offAxis
      ]
      exact
        g8ActualXiZetaThinBoundaryPointAddressMap_criticalImbalance
          correct.toAddressMap ghost.z ghost.offAxis
  exact ghost.noCorrectAddressPreimage hPre

/-- In the canonical boundary carrier, a correct accepted address readout
    refutes the pointwise correct-address ghost. -/
theorem g8ActualXiZetaCanonicalBoundaryCorrectAddress_refutesGhost
    {chart : ZetaAsCoordinateChartContext}
    {hG3 : chart.g3ZetaBridge}
    {hG4 : chart.g4AnalyticContinuation}
    {correct :
      G8ActualXiZetaShadowAddressCorrectness
        (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4)}
    (ghost :
      G8ActualXiZetaCorrectAddressGhostWitness
        (g8ActualXiZetaCanonicalBoundaryThinSource chart hG3 hG4)
        correct
        (g8ActualXiZetaCanonicalBoundaryWitnessAdapter
          correct.toAddressMap)) :
    False :=
  ghost.refutes

end Tau.BookIII.Bridge
