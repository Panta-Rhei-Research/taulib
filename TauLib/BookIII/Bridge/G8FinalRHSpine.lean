import TauLib.BookIII.Bridge.G8ActualXiZetaCoverage
import TauLib.BookIII.Bridge.G8ActualXiZetaShadowAddressCorrectness

/-!
# TauLib.BookIII.Bridge.G8FinalRHSpine

Final obligation spine for the one-sided G8f route to Mathlib's formal
`RiemannHypothesis` target.

This module does not discharge the remaining tau-side proof obligations.
Instead, it packages them as explicit fields and proves that, once supplied,
the existing actual-`xi` corridor yields Mathlib's exact `RiemannHypothesis`.

No O3 theorem, analytic-completion uniqueness theorem, full divisor-transfer
theorem, tau-purity theorem, or classical RH proof is hidden here.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- FINAL RH SPINE
-- ============================================================

/-- Final proof-spine obligation package for the actual `xi`/`zeta` G8f route.

The receiving-side zeta-to-`xi` coverage is theorem-backed in
`G8ActualXiZetaCoverage`.  The remaining fields are the current proof-program
obligations:

* a transfer/chart context;
* the G3 and G4 chart readouts from that context;
* correctness of the actual centered-shadow boundary address;
* tau-side purity for the resulting actual-source context.

This is the strict proof-checked handoff object: constructing a term of this
structure is exactly the remaining route to Mathlib's `RiemannHypothesis`
through the current corridor. -/
structure G8FinalRHSpine where
  transfer : G8dZeroDivisorTransferContext
  g3ZetaChartReadout :
    transfer.completion.chart.g3ZetaBridge
  g4CompletedXiReadout :
    transfer.completion.chart.g4AnalyticContinuation
  addressCorrect :
    G8ActualXiZetaShadowAddressCorrectness
      (g8ActualXiZetaCanonicalBoundaryThinSource
        transfer.completion.chart g3ZetaChartReadout
        g4CompletedXiReadout)
  tauPurity :
    G8eTauPurityExcludesOffCritical
      (g8ActualXiZeta_base
        (g8ActualXiZetaThin_to_fullSource
          (g8ActualXiZetaCanonicalBoundaryThinSource
            transfer.completion.chart g3ZetaChartReadout
            g4CompletedXiReadout)
          transfer rfl))

/-- The thin actual `xi` source selected by the final spine. -/
def G8FinalRHSpine.thinSource
    (spine : G8FinalRHSpine) :
    G8ActualXiZetaThinSourceContext :=
  g8ActualXiZetaCanonicalBoundaryThinSource
    spine.transfer.completion.chart
    spine.g3ZetaChartReadout
    spine.g4CompletedXiReadout

/-- The full actual `xi` source selected by the final spine. -/
def G8FinalRHSpine.source
    (spine : G8FinalRHSpine) :
    G8ActualXiZetaSourceContext :=
  g8ActualXiZetaThin_to_fullSource
    spine.thinSource spine.transfer rfl

/-- The address-resolved preimage source supplied by final-spine address
    correctness. -/
def G8FinalRHSpine.resolvedSource
    (spine : G8FinalRHSpine) :
    G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource
      spine.thinSource :=
  g8ActualXiZetaCanonicalBoundaryCorrectAddressResolvedSource
    spine.addressCorrect

-- ============================================================
-- SELECTORS
-- ============================================================

/-- The final spine exposes the G3 zeta-chart readout guard. -/
theorem G8FinalRHSpine.requires_g3ZetaBridge
    (spine : G8FinalRHSpine) :
    spine.transfer.completion.chart.g3ZetaBridge :=
  spine.g3ZetaChartReadout

/-- The final spine exposes the G4 completed-`xi` readout guard. -/
theorem G8FinalRHSpine.requires_g4AnalyticContinuation
    (spine : G8FinalRHSpine) :
    spine.transfer.completion.chart.g4AnalyticContinuation :=
  spine.g4CompletedXiReadout

/-- The final spine exposes the accepted-address correctness package. -/
def G8FinalRHSpine.address_correctness
    (spine : G8FinalRHSpine) :
    G8ActualXiZetaShadowAddressCorrectness spine.thinSource :=
  spine.addressCorrect

/-- The final spine exposes tau-side purity for the selected actual source. -/
theorem G8FinalRHSpine.tau_purity
    (spine : G8FinalRHSpine) :
    G8eTauPurityExcludesOffCritical
      (g8ActualXiZeta_base spine.source) :=
  spine.tauPurity

-- ============================================================
-- CORRIDOR ASSEMBLY
-- ============================================================

/-- The final spine supplies pointwise tau-imbalance preimages for actual
    off-axis `xi` shadows through the correct boundary-address map. -/
theorem G8FinalRHSpine.pointwisePreimages
    (spine : G8FinalRHSpine) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist
      spine.thinSource :=
  spine.addressCorrect.to_pointwisePreimages
    (g8ActualXiZetaCanonicalBoundaryWitnessAdapter
      spine.addressCorrect.toAddressMap)

/-- The final spine assembles the actual `xi`/`zeta` corridor. -/
def G8FinalRHSpine.corridor
    (spine : G8FinalRHSpine) :
    G8ActualXiZetaCorridor spine.source :=
  spine.resolvedSource.to_corridor spine.transfer rfl

/-- The final spine plus tau-side purity yields local exclusion of off-critical
    actual `xi` zeros. -/
theorem G8FinalRHSpine.noOffCriticalXiZeros
    (spine : G8FinalRHSpine) :
    G8eNoOrthodoxOffCriticalZeros
      (g8ActualXiZeta_base spine.source) :=
  spine.resolvedSource.noOffCriticalXiZeros
    spine.transfer rfl spine.tauPurity

-- ============================================================
-- MATHLIB RH HANDOFF
-- ============================================================

/-- A completed final spine yields Mathlib's formal `RiemannHypothesis`.

The proof body has no placeholders: all remaining mathematical work is isolated in
the explicit `G8FinalRHSpine` fields. -/
theorem G8FinalRHSpine.mathlibRiemannHypothesis
    (spine : G8FinalRHSpine) :
    RiemannHypothesis :=
  g8ActualXiZetaCorridor_to_mathlibRiemannHypothesis_fromCoverage
    spine.source spine.corridor spine.tauPurity

end Tau.BookIII.Bridge
