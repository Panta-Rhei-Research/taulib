import TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightSpectralCore
import TauLib.BookIII.Bridge.G8ActualXiSigmaFixedReduction

/-!
# TauLib.BookIII.Bridge.G8ActualXiSigmaFixedFromSpectralReality

Conditional spectral-reality lane for the final actual-sigma-fixed hinge.

First-edition Book III used the reusable forcing pattern:

```text
zero -> real spectral parameter -> central quadratic has zero imaginary part
     -> nonzero height forces Re(s) = 1/2
```

This module records that pattern as an explicit context.  It does not prove a
determinant representation, O3, full divisor transfer, accepted coverage, or
unconditional RH.  It only shows that, if each actual orthodox `xi` carrier has
the spectral-reality readout and nonzero height, then the current sigma-fixed
target follows through the reduction module.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- SPECTRAL-REALITY CONTEXT
-- ============================================================

/-- Conditional spectral-reality context for actual `xi` carriers.

The `centeredQuadratic_readout` field is kept explicit so this context can be
instantiated from whichever determinant/spectral parameter interface is later
chosen. -/
structure G8ActualXiSpectralRealityContext where
  spectralParameterReal :
    ∀ z : OrthodoxXiZeroCarrier,
      (orthodoxXiCarrierCenteredQuadratic z).im = 0
  nontrivialHeight :
    ∀ z : OrthodoxXiZeroCarrier,
      z.toZero.point.im ≠ 0
  centeredQuadratic_readout :
    ∀ z : OrthodoxXiZeroCarrier,
      (orthodoxXiCarrierCenteredQuadratic z).im =
        orthodoxXiCarrierCenteredQuadraticImagReadout z
  status : G8OffCriticalExclusionStatus := .openObligation

/-- The theorem-backed algebraic readout closes the bookkeeping field, leaving
    only the two genuine spectral inputs explicit. -/
def G8ActualXiSpectralRealityContext.ofInputs
    (inputs : G8ActualXiSpectralRealityInputs) :
    G8ActualXiSpectralRealityContext where
  spectralParameterReal := inputs.spectralParameterReal
  nontrivialHeight := inputs.nontrivialHeight
  centeredQuadratic_readout := orthodoxXiCarrierCenteredQuadratic_im

/-- The spectral-reality context forces each actual carrier onto the orthodox
    critical axis. -/
theorem G8ActualXiSpectralRealityContext.carrierRe_eq_half
    (ctx : G8ActualXiSpectralRealityContext)
    (z : OrthodoxXiZeroCarrier) :
    z.toZero.point.re = (1 / 2 : ℝ) := by
  apply
    g8CenteredQuadraticReality_forces_re_eq_half
      (sigma := z.toZero.point.re)
      (gamma := z.toZero.point.im)
  · change orthodoxXiCarrierCenteredQuadraticImagReadout z = 0
    rw [← ctx.centeredQuadratic_readout z]
    exact ctx.spectralParameterReal z
  · exact ctx.nontrivialHeight z

/-- The spectral-reality context excludes carrier-level off-criticality. -/
theorem G8ActualXiSpectralRealityContext.noCarrierOffCritical
    (ctx : G8ActualXiSpectralRealityContext)
    (z : OrthodoxXiZeroCarrier) :
    ¬ OrthodoxXiCarrierOffCritical z := by
  intro hOff
  exact hOff (ctx.carrierRe_eq_half z)

/-- The spectral-reality context supplies actual centered-address balance via
    the reduction theorem. -/
theorem G8ActualXiSpectralRealityContext.centeredAddressBalanced
    (ctx : G8ActualXiSpectralRealityContext) :
    G8ActualXiCenteredAddressBalanced :=
  g8ActualXiCenteredAddressBalanced_of_noCarrierOffCritical
    ctx.noCarrierOffCritical

/-- The spectral-reality context supplies the final actual sigma-fixed target. -/
theorem G8ActualXiSpectralRealityContext.actualSigmaFixed
    (ctx : G8ActualXiSpectralRealityContext) :
    G8ActualXiBoundaryCharacterSigmaFixed :=
  G8ActualXiBoundaryCharacterSigmaFixed.of_centeredAddressBalanced
    ctx.centeredAddressBalanced

/-- Spectral-reality falsifier: an off-critical carrier refutes the context. -/
theorem G8ActualXiOffCriticalCarrierFalsifier.refutesSpectralRealityContext
    (w : G8ActualXiOffCriticalCarrierFalsifier)
    (ctx : G8ActualXiSpectralRealityContext) :
    False :=
  ctx.noCarrierOffCritical w.z w.offCritical

end Tau.BookIII.Bridge
